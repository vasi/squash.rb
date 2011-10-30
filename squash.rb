#!/usr/bin/ruby

require 'rubygems'
require 'bit-struct'
require 'zlib'
require 'time'
require 'pp'

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
		unsigned	:root_inode,	64
		unsigned	:bytes_used,	64
		unsigned	:id_table_start,		64
		unsigned	:xattr_id_table_start,	64
		unsigned	:inode_table_start,		64
		unsigned	:directory_table_start,	64
		unsigned	:fragment_table_start,	64
		unsigned	:lookup_table_start,	64
	
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
#		STDERR.puts [off, len].inspect
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
		data = Zlib::Inflate.inflate(data) if compressed
		return [hsz + size, data]
	end
	
	def read_metadata(pos, size)
#		STDERR.puts [pos, size].inspect
		ret = ""
		while size > 0
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
		
		attr_reader :xtra
		
		def initialize(fs, pos)
			@fs = fs
			pos = MDPos.inode(pos) unless pos.respond_to?(:offset)
			pos.block += @fs.sb.inode_table_start
			@base = @fs.read_md_struct(pos, Base)
			
			klass = TypeClasses[@base.type - 1] or raise 'Unsupported type'
			@xtra = @fs.read_md_struct(pos, klass)
			@pos = pos
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
		
		def read_block_sizes
			@fs.read_metadata(next_pos, block_count * 4).unpack('V*')
		end
		
		def read_block(n, bscache = nil)
			start = @xtra.start_block
			hdr = 0
			(bscache || read_block_sizes).each_with_index do |sz,i|
				hdr = sz
				break if i == n
				comp, bsz = SquashFS.size_parse(sz)
				start += bsz
			end
			
			if hdr == 0 # Hole
				dsz = [@xtra.file_size - n * @fs.sb.block_size,
					@fs.sb.block_size].min
				return "\0" * dsz
			else
				bsz, data = @fs.read_block_size(start, hdr)
				return data
			end
		end
		
		def read_range(start, size, &block)
			raise 'Too far' if start > @xtra.file_size
			bsc = nil
			ret = []
			while size > 0 && start < @xtra.file_size
				bnum, off = start.divmod(@fs.sb.block_size)
				data = if bnum >= block_count
					read_fragment
				else
					bsc ||= read_block_sizes
					read_block(bnum, bsc)
				end
				take = [data.size - off, size].min
				data = data[off, take] if off != 0 && take != data.size
				block ? block[data] : (ret << data)
				start += take
				size -= take
			end
			return block ? nil : ret.join('')
		end
		
		def read_file(&block)
			read_range(0, @xtra.file_size, &block)
		end
		
		def readlink
			@fs.read_metadata(next_pos, @xtra.symlink_size)
		end
		
		def pretty_print_instance_variables
			instance_variables.sort - ['@fs']
		end
	end
	
	class Directory
		class Header < LEBitStruct
			unsigned	:count, 32
			unsigned	:start_block, 32
			unsigned	:inode_number, 32
		end
		class Entry < LEBitStruct
			unsigned	:offset, 16
			unsigned	:inode_number, 16
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
				break if name < iname
				
				pos.length = idx.dirpos
				pos.block = idx.start_block + @fs.sb.directory_table_start
			end
			pos.offset = (pos.offset + pos.length) % MetadataSize
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
	
	def scan_files(inode = nil, &block)
		inode ||= root
		block[:inode, inode]
		return unless inode.type == :dir
		inode.directory.children do |c|
			block[:child, c]
			scan_files(c.inode, &block) if c.type == :dir
		end
		block[:closedir, nil]
	end
	
	def root; Inode.new(self, @sb.root_inode); end
	
	def initialize(path)
		@io = open(path)
		@sb = Superblock.new(@io)
		raise 'Not a squashfs filesystem' \
			unless @sb.magic == Superblock::Magic
		raise 'Unsupported version' \
			unless @sb.vers_maj == 4 && @sb.vers_min >= 0
		raise 'FIXME: Compression not zlib' unless @sb.compression == 1
		
		@md_cache = BlockCache.new(self, BlockCache::MetadataCacheSize)
		@frag_cache = BlockCache.new(self, BlockCache::FragmentCacheSize)
		@id_table = IdTable.new(self, @md_cache)
		@frag_table = FragTable.new(self, @md_cache)
	end
end

fs = SquashFS.new(ARGV.shift)
file = fs.lookup('vmlinuz')
puts file.readlink
exit

parts = []
fs.scan_files do |w, o|
	case w
	when :child
		parts << o.name
		puts parts.join('/')
		parts.pop unless o.type == :dir
	when :closedir
		parts.pop
	end
end

# TODO
# data block indices
# xattrs
# lookup/export?
# compression types
# parent links?
