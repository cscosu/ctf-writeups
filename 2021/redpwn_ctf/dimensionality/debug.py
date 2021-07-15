import qiling
import string
import time

# This script runs `chall` in qiling, which allows me to hook address and print
# out registers and stuff. Useful for debugging.


class StringBuffer:
    def __init__(self):
        self.buffer = b""

    def read(self, n):
        ret = self.buffer[:n]
        self.buffer = self.buffer[n:]
        return ret

    def readline(self, end=b"\n"):
        ret = b""
        while True:
            c = self.read(1)
            ret += c
            if c == end:
                break
        return ret

    def write(self, string):
        self.buffer += string
        return len(string)

    def lseek(self, offset, origin):
        pass


char_index = 0


def boundary_fail(ql):
    global char_index
    print(f"boundary_fail {char_index}")


def char_fail(ql):
    global char_index
    print(f"char_fail {char_index} {ql.reg.edx}")


def char_pass(ql):
    global char_index
    print(f"char_pass {char_index} {ql.reg.edx}")
    char_index += 1


def my_sandbox(path, inp):
    global char_index
    char_index = 0

    stdin = StringBuffer()
    stdout = StringBuffer()

    ql = qiling.Qiling(
        path, "/", stdin=stdin, stdout=stdout, verbose=qiling.const.QL_VERBOSE.OFF
    )

    stdin.write(f"{inp}\n".encode())

    ql.hook_address(boundary_fail, 0x555555555518)  # boundary check fail
    ql.hook_address(char_fail, 0x5555555554D3)  # char check fail
    ql.hook_address(char_pass, 0x5555555554C1)  # char success

    ql.run()

    msg = stdout.buffer.decode().strip()
    print(f"msg = {msg}")

    if ":)" in msg:
        print(f"password = {inp}")
        return True

    print(f"char_index = {char_index}")

    if char_index >= len(inp):
        # All characters passed (and maybe more?)!
        return True
    else:
        # Some characters didn't pass (probably last)
        return False


if __name__ == "__main__":
    inp = "frrffllffddllffrrffuubbrrfff"
    my_sandbox(["./chall"], inp)
