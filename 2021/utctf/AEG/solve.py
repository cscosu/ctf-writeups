import pwn
import subprocess


def aeg(i: int):
    """
    Run aeg.py in virtualenv with angr installed, since pwntools and angr seem
    to have dependency conflicts >:(
    """
    filename = f"bins/{i}"
    cmd = f"./env/bin/python aeg.py {filename}"
    print(subprocess.check_output(cmd, shell=True))
    return open(f"bins/{i}.exp", "rb").read()


pwn.context.log_level = "debug"
io = pwn.remote("pwn.utctf.live", 9997)
io.sendlineafter("Press enter when you're ready for the first binary.", "")

for i in range(10):
    s = io.recvuntilS("You have 60 seconds to provide input:")
    s = "\n".join(s.split("\n")[:-1])  # Get rid of the last line
    s = s.strip()
    open(f"bins/{i}.hex", "w").write(s)
    # Parse hexdump into a binary file
    subprocess.check_output(f"xxd -r bins/{i}.hex > bins/{i}", shell=True)

    exp = aeg(i)
    io.sendline(exp)
    io.recvuntil("Process exited with return code")
    io.recvline()

io.interactive()
