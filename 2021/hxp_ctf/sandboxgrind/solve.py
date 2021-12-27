import pwn
import base64

io = pwn.remote("168.119.235.55", 9001)

with open("solve", "rb") as f:
    s = f.read()

s64 = base64.b64encode(s)
io.sendlineafter("end with EOF\n", s64)
io.sendline()
io.interactive()