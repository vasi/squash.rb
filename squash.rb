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
	
	def blocks_needed(size, block_size)
		q, r = size.divmod(block_size)
		q += 1 if r != 0
		return q
	end
	
	class Int64 < BitStruct::Vector
		unsigned :i, 64, :endian => :little
	end
	def unpack64(s)
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
	
	def read_id_idxs
		nblocks = blocks_needed(@sb.no_ids * 4, MetadataSize)
		@id_idxs = unpack64(read(@sb.id_table_start, 8 * nblocks))
	end
	def id(i)
		block = @id_idxs[i * 4 / MetadataSize]
		@md_cache.get(block)[(i * 4) % MetadataSize, 4].unpack('V').first
	end
	
	class FragEntry < LEBitStruct
		unsigned :start_block, 64
		unsigned :size, 32
		unsigned :pad, 32
	end
	FragEntSize = FragEntry.round_byte_length
	def read_frag_idxs
		nblocks = blocks_needed(@sb.fragments * FragEntSize, MetadataSize)
		@frag_idxs = unpack64(read(@sb.fragment_table_start, 8 * nblocks))
	end
	def frag_lookup(i)
		block = @frag_idxs[i * FragEntSize / MetadataSize]
		FragEntry.new(@md_cache.get(block)[(i * FragEntSize) % MetadataSize,
			FragEntSize])
	end
	
	def read_block_size(off, len = nil)
		if len
			hsz = 0
			header = len
			@io.seek(off)
		else
			hsz = 2
			header = read(off, hsz).unpack('v').first
		end
		size = header & ~(1 << 15)
		compressed = (header - size).zero?
		
		data = @io.read(size)
		data = Zlib::Inflate.inflate(data) if compressed
		return [hsz + size, data]
	end
	
	def read_metadata(pos, size)
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
	
	def read_fragment(i)
		frag = frag_lookup(i)
		@frag_cache.get(frag.start_block, frag.size)
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
		class Dir < LEBitStruct
			unsigned	:start_block,	32
			unsigned	:nlink,			32
			unsigned	:file_size,		16
			unsigned	:offset,		16
			unsigned	:parent_inode,	32
		end
		class Reg < LEBitStruct
			unsigned	:start_block,	32
			unsigned	:fragment,		32
			unsigned	:offset,		32
			unsigned	:file_size,		32
		end
		class LDir < LEBitStruct
			unsigned	:nlink,			32
			unsigned	:file_size,		32
			unsigned	:start_block,	32
			unsigned	:parent_inode,	32
			unsigned	:idx_count,		16
			unsigned	:offset,		16
			unsigned	:xattr,			32
		end
		TypeClasses = [Dir, Reg, nil, nil, nil, nil, nil,
			LDir]
		
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

		def read_fragment
			return nil if @xtra.fragment == InvalidFragment
			data = @fs.read_fragment(@xtra.fragment)
			return data[@xtra.offset, @xtra.file_size % @fs.sb.block_size]
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
			return pos unless @inode.respond_to?(:idx_count)
			
			ipos = @inode.next_pos
			@inode.idx_count.times do
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
		read_id_idxs
		read_frag_idxs
	end
end

fs = SquashFS.new(ARGV.shift)
file = fs.lookup('etc/shells')
puts file.read_fragment
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
# data blocks
# parent finding
# all file types
# xattrs
# lookup/export?
# compression types
# holes?
