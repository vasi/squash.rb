#!/usr/bin/ruby

require 'rubygems'
require 'bit-struct'
require 'zlib'
require 'time'
require 'pp'
require 'inline'

class SquashFS
	class LEBitStruct < BitStruct; default_options :endian => :little; end
	
	class Superblock < LEBitStruct
		Magic = 0x73717368
		
		unsigned	:magic,			32
		unsigned	:inodes,		32
		unsigned	:mkfs_time,		32
		unsigned	:block_size,	32
		unsigned	:fragments,		32
		unsigned	:compression,	16
		unsigned	:block_log,		16
		unsigned	:flags,			16
		unsigned	:no_ids,		16
		unsigned	:vers_maj,		16
		unsigned	:vers_min,		16
		signed	:root_inode,	64
		signed	:bytes_used,	64
		signed	:id_table_start,		64
		signed	:xattr_id_table_start,	64
		signed	:inode_table_start,		64
		signed	:directory_table_start,	64
		signed	:fragment_table_start,	64
		signed	:lookup_table_start,	64
	
		def compr_inode?; (flags & 1).zero?; end
		def compr_data?; (flags & 2).zero?; end
		def compr_frag?; (flags & 4).zero?; end
		def frag?; (flags & 8).zero?; end
		def always_frag?; (flags & 16) != 0; end
		def dups?; (flags & 32) != 0; end
		def export?; (flags & 64) != 0; end
		def comp_opt?; (flags & 1024) != 0; end
	end
	
	MetadataSize = 8192
	Types = [:dir, :reg, :sym, :blkd, :chrd, :fifo, :sock]
	
	attr_reader :sb
	
	def read(off, size)
		@io.seek(off)
		@io.read(size)
	end
	
	def self.divceil(dividend, divisor)
		q, r = dividend.divmod(divisor)
		q += 1 if r != 0
		return q
	end
	
	class Int64 < BitStruct::Vector
		unsigned :i, 64, :endian => :little
	end
	def self.unpack64(s)
		Int64.new(s).map { |x| x.i }
	end
	
	class MDPos
		attr_accessor :block, :offset, :length
		def initialize(b, o)
			@block, @offset, @length = b, o , 0
		end
		def self.inode(n, add = 0)
			new((n >> 16) + add, n & 0xffff)
		end
	end
	
	class IdxTable
		def initialize(fs, md_cache, start, count)
			@md_cache = md_cache
			nblocks = SquashFS.divceil(count * size, MetadataSize)
			@idxs = SquashFS.unpack64(fs.read(start, 8 * nblocks))
		end
		
		def get(i)
			bidx, off = (i * size).divmod(MetadataSize)
			@md_cache.get(@idxs[bidx])[off, size]
		end
	end
	
	class IdTable < IdxTable
		def initialize(fs, md_cache)
			super(fs, md_cache, fs.sb.id_table_start, fs.sb.no_ids)
		end
		def size; 4; end
		def get(i); super.unpack('V').first; end
	end
	
	class ExportTable < IdxTable
		def initialize(fs, md_cache)
			if (p = fs.sb.lookup_table_start) != Inode::InvalidBlk
				@present = true
				super(fs, md_cache, p, fs.sb.inodes)
			end
		end
		def size; 8; end
		def get(i); @present && SquashFS.unpack64(super).first; end
	end
	
	class XattrInfo < LEBitStruct
		unsigned :xattr, 64
		unsigned :count, 32
		unsigned :size, 32
	end
	class XattrTable < IdxTable
		class XattrTableInfo < LEBitStruct
			signed :start, 64
			unsigned :count, 32
			unsigned :pad, 32
		end
		def initialize(fs, md_cache)
			off = fs.sb.xattr_id_table_start
			if off == Inode::InvalidBlk
				@info = nil
				return
			end
			isize = XattrTableInfo.round_byte_length
			@info = XattrTableInfo.new(fs.read(off, isize))
			super(fs, md_cache, off + isize, @info.count)
		end
		def pos(x); MDPos.inode(x, @info.start); end
		def size; XattrInfo.round_byte_length; end
		def get(i); @info && XattrInfo.new(super); end
	end
	
	class FragEntry < LEBitStruct
		unsigned :start_block, 64
		unsigned :size, 32
		unsigned :pad, 32
	end
	class FragTable < IdxTable
		def initialize(fs, md_cache)
			super(fs, md_cache, fs.sb.fragment_table_start, fs.sb.fragments)
		end
		def size; FragEntry.round_byte_length; end
		def get(i); FragEntry.new(super); end
	end
		
	def self.size_parse(sz, meta = false)
		flag = 1 << (meta ? 15 : 24)
		compressed = (sz & flag).zero?
		size = (sz & ~flag)
		size = flag if meta && size.zero?
		return [compressed, size]
	end
	# Read block, returning also the size
	def read_block_size(off, len = nil)
		#STDERR.puts [off, len].inspect
		if len
			hsz = 0
			header = len
			@io.seek(off)
		else
			hsz = 2
			header = read(off, hsz).unpack('v').first
		end
		compressed, size = SquashFS.size_parse(header, !len)
		
		data = @io.read(size)
		if compressed
			outsize = len ? @sb.block_size : MetadataSize
			data = decompress(data, outsize) if compressed
		end
		return [hsz + size, data]
	end
	
	def read_metadata(pos, size, &per_md)
		#STDERR.puts [pos, size].inspect
		ret = ""
		while size > 0
			per_md[pos.block] if per_md
			bsz, data = @md_cache.get_size(pos.block)
			take = [data.size - pos.offset, size].min
			ret << data[pos.offset, take]
			
			size -= take
			pos.offset += take
			pos.length += take
			if pos.offset == data.size
				pos.block += bsz
				pos.offset = 0
			end
		end
		
		ret
	end
	def read_md_struct(pos, kl)
		kl.new(read_metadata(pos, kl.round_byte_length))
	end
	
	def id(i); @id_table.get(i); end
	def read_fragment(i)
		frag = @frag_table.get(i)
		@frag_cache.get(frag.start_block, frag.size)
	end
	def xattr_pos(p); @xattr_table.pos(p); end
	def xattr_info(i); @xattr_table.get(i); end
	
	class StructMaker
		def initialize(header)
			@lines = IO.readlines(header)
		end

		Field = Struct.new(:name, :endian, :size)
		Spec = Struct.new(:name, :fields)

		def parse
			ks = []
			k = nil
			@lines.each do |l|
				if k
					if l.match(/^\s*\}\s*;\s*$/)
						ks << k
						k = nil
					elsif md = l.match(/^\s*__(le|be)(\d+)\s+(\w+)\s*;\s*$/)
						k.fields << Field.new(md[3],
							md[1] == 'le' ? :little : :big, md[2].to_i)
					# ignore unknown fields	
					end
				elsif md = l.match(/^\s*struct\s+(\w+)\s*\{\s*$/)
					k = Spec.new(md[1], [])
				end
			end
			ks
		end

		def make(spec)
			Class.new(BitStruct) do
				spec.fields.each do |f|
					unsigned f.name, f.size, :endian => f.endian
				end
			end
		end

		def make_inodes
			ks = {}
			parse.each do |spec|
				md = spec.name.match(/^squashfs_(\w+)_inode$/) or next

				# Remove common fields
				snip = spec.fields.index { |f| f.name == 'inode_number' }
				spec.fields.slice!(0, snip + 1)

				ks[md[1]] = make(spec)
			end
			
			order = %w[dir reg symlink dev dev ipc ipc]
			ret = []
			['', 'l'].each do |pre|
				order.each { |n| ret << (ks[pre + n] || ks[n]) }
			end
			ret
		end
	end
	
	class Inode
		InvalidFragment = 0xffffffff
		InvalidXattr = 0xffffffff
		InvalidBlk = -1
		
		class Base < LEBitStruct
			unsigned	:type,		16
			unsigned	:mode,		16
			unsigned	:uid,		16
			unsigned	:gid,		16
			unsigned	:mtime,		32
			unsigned	:inode_number,	32
		end
		
		TypeClasses = StructMaker.new('squashfs_fs.h').make_inodes
		
		def type_idx; @base.type % Types.size - 1; end
		def type; Types[type_idx]; end
		def long?; @base.type > Types.size; end
		def time; Time.at(@base.mtime); end
		def uid; @fs.id(@base.uid); end
		def gid; @fs.id(@base.gid); end
		
		def modestr
			ret = "d-lbcps"[type_idx, 1]
			6.step(0, -3) do |sh|
				perm = (@base.mode >> sh) & 7
				"rwx".each_char do |c|
					ret << (perm & 4 > 0 ? c : '-')
					perm <<= 1
				end
				if @base.mode & (1 << 9 + sh/3) > 0
					c = sh > 0 ? 's' : 't'
					ret[-1,1] = ret[-1] == ?- ? c.upcase : c
				end
			end
			ret
		end
		
		def next_pos; @pos.dup; end
		
		attr_reader :xtra, :inode_id
		
		def initialize(fs, pos)
			@fs = fs
			pos = MDPos.inode(pos) unless pos.respond_to?(:offset)
			@inode_id = (pos.block << 16) + pos.offset
			pos.block += @fs.sb.inode_table_start
			@base = @fs.read_md_struct(pos, Base)
			
			klass = TypeClasses[@base.type - 1] or raise 'Unsupported type'
			@xtra = @fs.read_md_struct(pos, klass)
			@pos = pos
			
			# Special case: long symlinks
			@xattr = nil
			if type == :sym && long?
				p = next_pos
				readlink(p)
				@xattr = @fs.read_metadata(p, 4).unpack('V').first
			end
		end
		
		def directory
			Directory.new(@fs, self)
		end
		
		def respond_to?(meth)
			super || @xtra.respond_to?(meth) || @base.respond_to?(meth)
		end
		
		def method_missing(meth, *args)
			[@xtra, @base].each do |b|
				return b.send(meth, *args) if b.respond_to?(meth)
			end
			super
		end
		
		def dump
			puts "inode %d: type %s, mode %s, uid %d, gid %d, time %s" %
				[@base.inode_number, type, modestr, uid, gid, time.iso8601]
		end
		
		def fragment?; @xtra.fragment != InvalidFragment; end
		
		def read_fragment
			return nil unless fragment?
			data = @fs.read_fragment(@xtra.fragment)
			return data[@xtra.offset, @xtra.file_size % @fs.sb.block_size]
		end
		
		def block_count
			bs = @fs.sb.block_size
			sz = @xtra.file_size
			fragment? ? (sz / bs) : SquashFS.divceil(sz, bs)
		end
		
		def read_block_sizes(start, count, &per_md)
			@fs.read_metadata(start, count * 4, &per_md).unpack('V*')
		end
		
		def read_block(pos, hdr)
			if hdr == 0 # Hole
				dsz = [@xtra.file_size - block_count * @fs.sb.block_size,
					@fs.sb.block_size].min
				return "\0" * dsz
			else
				bsz, data = @fs.read_block_size(pos, hdr)
				return data
			end
		end
		
		def read_range(start, size, &block)
			raise 'Too far' if start > @xtra.file_size
			return '' if size <= 0
			
			# Block list info
			blidx, blpos, blsizes = @fs.blocklist(self, start, size)
			
			bnum, off = start.divmod(@fs.sb.block_size)
			ret = []
			
			while size > 0 && start < @xtra.file_size
				data = nil
				if bnum >= block_count # It's a fragment
					data = read_fragment
				else # Look at the block list
					hdr = blsizes.shift
					compressed, bsize = SquashFS.size_parse(hdr)
					if bnum == blidx # Reached a block we want to read
						data = read_block(blpos, hdr)
					end
					blidx += 1
					blpos += bsize
				end
				if data
					take = [data.size - off, size].min
					data = data[off, take] if off != 0 || take != data.size
					block ? block[data] : (ret << data)
					start += take
					size -= take
					bnum += 1
					off = 0
				end
			end
			return block ? nil : ret.join('')
		end
		
		def read_file(&block)
			read_range(0, @xtra.file_size, &block)
		end
		
		def readlink(pos = nil)
			@fs.read_metadata(pos || next_pos, @xtra.symlink_size)
		end
		
		class XattrEntry < LEBitStruct
			unsigned :type, 16
			unsigned :size, 16

			XattrPrefixes = %w[user trusted security]
			XattrOOL = 0x100
			def ool?; (type & XattrOOL) != 0; end
			def prefix; XattrPrefixes[type & ~XattrOOL] + '.'; end
		end
		
		def xattr_num
			x = @xattr || (@xtra.respond_to?(:xattr) && @xtra.xattr)
			return (x && x != InvalidXattr) ? x : nil
		end
		
		def xattr_each(default = nil, &block)
			n = xattr_num or return default
			info = @fs.xattr_info(n)
			pos = @fs.xattr_pos(info.xattr)
			
			info.count.times do
				entry = @fs.read_md_struct(pos, XattrEntry)
				name_end = @fs.read_metadata(pos, entry.size)
				name = entry.prefix + name_end
				sz = @fs.read_metadata(pos, 4).unpack('V').first
				block[pos, name, entry.ool?, sz]
				@fs.read_metadata(pos, sz)
			end
		end
		
		def xattr_list
			ret = []
			xattr_each([]) { |pos, name, ool, sz| ret << name }
			ret
		end
		
		def xattr_get(name)
			xattr_each(nil) do |pos, xname, ool, sz|
				next unless xname == name
				return @fs.read_metadata(pos, sz) unless ool
				# Indirect xattr
				x2 = SquashFS.unpack64(@fs.read_metadata(pos, 8)).first
				p2 = @fs.xattr_pos(x2)
				s2 = @fs.read_metadata(p2, 4).unpack('V').first
				return @fs.read_metadata(p2, s2)
			end
			nil
		end
		
		def xattr_dump
			xattr_list.inject({}) { |h,k| h[k] = xattr_get(k); h }
		end
		
		def parent
			@fs.lookup_inode_number(@xtra.parent_inode)
		end
		
		def pretty_print_instance_variables
			instance_variables.sort - ['@fs']
		end
	end
	
	class MetaIndex
		Slots = 16
		MinBlocks = 2048
		
		Entry = Struct.new(:inum, :positions)
		Position = Struct.new(:block_pos, :md_block)
		
		def initialize(fs, slots)
			@fs = fs
			@slots = Array.new(slots)
			@pos = 0
		end
		
		def entry(inode)
			@slots.find { |s| s && s.inum = inode.inode_number }
		end
		def want?(inode); inode.block_count >= MinBlocks; end
		
		# First block entry idx in a new metadata block
		def first(inode)
			SquashFS.divceil(MetadataSize - inode.next_pos.offset, 4)
		end
		def step; MetadataSize / 4; end
		
		def add_index(inode, md_bpos, sizes)
			positions = []
			md_bpos.shift # don't want the zero'th md-block
			first = first(inode)
		
			bpos = inode.start_block
			sizes.each_with_index do |hdr, i|
				if i == first
					positions << Position.new(bpos, md_bpos.shift)
					first += step
				end
				compressed, bsize = SquashFS.size_parse(hdr)
				bpos += bsize
			end
		
			@slots[@pos] = Entry.new(inode.inode_number, positions)
			@pos = (@pos + 1) % @slots.size
		end
		
		def read_index(inode, positions, start, size)
			bfirst, blast = [start, start + size - 1].map do |p|
				[SquashFS.divceil(p, @fs.sb.block_size),
					inode.block_count].min
			end
			i = (bfirst - first(inode)) / step
			if i < 0
				bnum, bpos, mdpos = 0, inode.start_block, inode.next_pos
			else
				p = positions[i]
				bnum = first(inode) + i * step
				bpos = p.block_pos
				mdpos = MDPos.new(p.md_block, inode.start_block % 4)
			end
			return bnum, bpos, inode.read_block_sizes(mdpos,
				blast - bnum + 1)
		end
		
		def blocklist(inode, start, size)
			if e = entry(inode)
				return read_index(inode, e.positions, start, size)
			else
				md_bpos = []
				per_md = want?(inode) ? proc { |pos| md_bpos << pos } : nil
				sizes = inode.read_block_sizes(inode.next_pos,
					inode.block_count, &per_md)
				
				add_index(inode, md_bpos, sizes) if want?(inode)
				return [0, inode.start_block, sizes]
			end
		end
	end
	def blocklist(inode, start, size)
		@meta_idx.blocklist(inode, start, size)
	end
	
	class Directory
		class Header < LEBitStruct
			unsigned	:count, 32
			unsigned	:start_block, 32
			unsigned	:inode_number, 32
		end
		class Entry < LEBitStruct
			unsigned	:offset, 16
			signed		:inode_number, 16
			unsigned	:type, 16
			unsigned	:size, 16
		end
		class IndexEntry < LEBitStruct
			unsigned	:dirpos, 32
			unsigned	:start_block, 32
			unsigned	:namelen, 32
		end
		
		class Child
			attr_reader :entry, :name
			def initialize(fs, dirh, pos)
				@fs, @dirh = fs, dirh
				@entry = @fs.read_md_struct(pos, Entry)
				@name = @fs.read_metadata(pos, @entry.size + 1)
			end
			def inode_number; @entry.inode_number + @dirh.inode_number; end
			def type; Types[@entry.type - 1]; end
			def pos; MDPos.new(@dirh.start_block, @entry.offset); end
			def inode; Inode.new(@fs, pos); end
		end
		
		def children(pos = nil, &block)
			pos ||= start_pos
			
			while pos.length + 3 < @inode.file_size do
				dirh = @fs.read_md_struct(pos, Header)
				(dirh.count + 1).times do
					block[Child.new(@fs, dirh, pos)]
				end
			end
		end
		def nchildren
			c = 0
			children { c += 1 }
			c
		end
		
		def start_pos
			MDPos.new(@inode.start_block + @fs.sb.directory_table_start,
				@inode.offset)
		end
		
		def find_pos(name)
			pos = start_pos
			return pos unless @inode.respond_to?(:i_count)
			
			ipos = @inode.next_pos
			@inode.i_count.times do
				idx = @fs.read_md_struct(ipos, IndexEntry)
				iname = @fs.read_metadata(ipos, idx.namelen + 1)
				p [(pos.offset + idx.dirpos) % MetadataSize, iname]
				break if name < iname
				
				pos.length = idx.dirpos
				pos.block = idx.start_block + @fs.sb.directory_table_start
			end
			pos.offset = (pos.offset + pos.length) % MetadataSize
			p [:index, pos]
			return pos
		end
		
		def lookup(name)
			pos = find_pos(name)
			children(pos) { |c| return c if c.name == name }
			return nil
		end
		
		def initialize(fs, inode)
			raise "Not a directory" unless inode.type == :dir
			@fs, @inode = fs, inode
		end
	end
	
	class BlockCache
		MetadataCacheSize = 8
		FragmentCacheSize = 3
		
		Entry = Struct.new(:off, :data, :bsize)
		
		def initialize(fs, size)
			@fs = fs
			@blocks = Array.new(size)
			@pos = 0 # next to eject
		end
		
		def get_size(off, len = nil)
			unless e = @blocks.find { |e| e && e.off == off }
				bsz, data = @fs.read_block_size(off, len)
				e = @blocks[@pos] = Entry.new(off, data, bsz)
				@pos = (@pos + 1) % @blocks.size # Round robin ejection
			end
			return e.bsize, e.data
		end
		
		def get(off, len = nil)
			bsz, d = get_size(off, len)
			return d
		end
	end
	
	def lookup(path)
		parts = path.split('/')
		inode = root
		while inode && !parts.empty?
			inode = inode.directory.lookup(parts.shift).inode
		end
		inode
	end
	
	def scan(inode = nil, &block)
		inode ||= root
		block[:dir, inode]
		inode.directory.children do |c|
			block[:child, c]
			scan(c.inode, &block) if c.type == :dir
		end
		block[:dirend, nil]
	end
	def scan_paths(inode = nil, &block)
		parts = []
		scan(inode) do |t, c|
			parts << c.name if t == :child
			block[t, parts.join('/'), c]
			parts.pop if t == :dirend || (t == :child && c.type != :dir)
		end 		
	end
	def scan_ipaths(inode = nil, &block)
		inode ||= root
		block[inode, '']
		scan_paths(inode) do |t, p, c|
			block[c.inode, p] if t == :child
		end
	end
	
	def lookup_inode_number(num)
		Inode.new(self, @export_table.get(num - 1))
	end
	
	def root; Inode.new(self, @sb.root_inode); end
	
	Decompressors = [ :zlib, :lzma, :lzo, :xz ]
	def decompress(data, osize); __send__(@decomp, data, osize); end
	def zlib(data, osize); Zlib::Inflate.inflate(data); end
	
	def self.fink_build(hdr, lib)
		bin = `which fink`
		md = bin.match(%r{^(.*)/bin/fink}) and prefix = md[1]
		inline do |builder|
			builder.add_compile_flags "-I#{prefix}/include -Wno-pointer-sign"
			builder.add_link_flags "-L#{prefix}/lib -l#{lib}"
			builder.include "<#{hdr}>"
			yield builder, prefix
		end
	end
	fink_build('lzo1x.h', 'lzo2') do |builder, prefix|
		builder.add_compile_flags "-I#{prefix}/include/lzo"
		builder.c <<LZO
			VALUE lzo(VALUE src, unsigned long osize) {
				VALUE dst = rb_str_new(NULL, osize);
				int res = lzo1x_decompress_safe(RSTRING(src)->ptr,
					RSTRING(src)->len, RSTRING(dst)->ptr, (lzo_uintp)&osize,
					NULL);
				if (res != LZO_E_OK)
					return Qnil;
				rb_str_set_len(dst, osize);
				return dst;
			}
LZO
	end
	fink_build('lzma.h', 'lzma') do |builder, prefix|
		builder.c <<XZ
			VALUE xz(VALUE src, unsigned long osize) {
				VALUE dst = rb_str_new(NULL, osize);
				uint64_t memlimit = UINT64_MAX;
				size_t ipos = 0, opos = 0;
				lzma_ret res = lzma_stream_buffer_decode(&memlimit, 0, NULL,
					RSTRING(src)->ptr, &ipos, RSTRING(src)->len,
					RSTRING(dst)->ptr, &opos, osize);
				if (res != LZMA_OK)
					return Qnil;
				rb_str_set_len(dst, opos);
				return dst;
			}
XZ
	end
	
	def initialize(path)
		@io = open(path)
		@sb = Superblock.new(@io)
		raise 'Not a squashfs filesystem' \
			unless @sb.magic == Superblock::Magic
		raise 'Unsupported version' \
			unless @sb.vers_maj == 4 && @sb.vers_min >= 0
		
		@decomp = Decompressors[@sb.compression - 1] or
			raise 'Unknown compression'
		
		@md_cache = BlockCache.new(self, BlockCache::MetadataCacheSize)
		@frag_cache = BlockCache.new(self, BlockCache::FragmentCacheSize)
		@id_table = IdTable.new(self, @md_cache)
		@frag_table = FragTable.new(self, @md_cache)
		@xattr_table = XattrTable.new(self, @md_cache)
		@export_table = ExportTable.new(self, @md_cache)
		@meta_idx = MetaIndex.new(self, MetaIndex::Slots)
	end
end

fs = SquashFS.new(ARGV.shift)

#fs.lookup('var/lib/dpkg/info').directory.children { |c| puts c.name }; exit 0
#fs.lookup('var/lib/dpkg/info/zip.list'); exit 0

fs.scan_ipaths do |i, p|
	puts "%3d - %s" % [i.inode_number, p]
end
