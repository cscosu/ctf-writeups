import pwn
import Crypto.Util.number as cun
import Crypto.Util.Padding as cup
import os
import base64

if pwn.args.DEBUG:
    pwn.context.log_level = "debug"


def connect():
    if pwn.args.REMOTE:
        return pwn.remote("chal.b01lers.com", 25003)
    else:
        return pwn.process("python3 server.py", shell=True)


def get_params(io):
    io.recvuntil("ticket:\n")
    ticket = io.recvlineS().strip()
    ticket = base64.b64decode(ticket)
    print(f"[+] Got ticket {base64.b64encode(ticket)}")

    io.recvuntil("winning numbers are:\n")
    winning_nums = eval(io.recvlineS().strip())
    print(f"[+] Got winning numbers {winning_nums}")

    return (ticket, winning_nums)


def send(ct):
    p = base64.b64encode(ct)
    io.sendlineafter("Redeem a ticket:\n", p)
    return io.recvlineS().strip()


def split_blocks(xs, n=16):
    """Yield successive n-sized blocks from xs"""
    return [xs[i : i + n] for i in range(0, len(xs), n)]


def find_imm_chr(pre: bytes, front_ct: bytes, imms: bytes) -> bytes:
    payloads = []
    desired = len(imms) + 1  # The desired padding char

    """
    Example:
        ??\x03\x03
        Then \x03\03 is the front_padding
    """
    front_padding = cun.long_to_bytes(desired) * len(imms)

    for i in range(256):
        b = cun.long_to_bytes(i)

        # imm ^ forged = desired
        # imm ^ desired = forged
        forged_tail = pwn.xor(imms, front_padding)
        tail = b + forged_tail
        ct = b"\x00" * (16 - len(tail)) + tail

        payload = pre + ct + front_ct
        payloads.append(base64.b64encode(payload).decode())

    payload = "\n".join(payloads)
    # io.sendlineafter("Redeem a ticket:\n", payload)
    io.clean()
    io.sendline(payload)

    win = False
    for i in range(256):
        res = io.recvline().strip()
        if res == b"sorry, that ticket did not win anything":
            print(f"[+] Got {i}")
            # i ^ imm = desired
            # i ^ desired = imm
            imms = cun.long_to_bytes(i ^ desired) + imms
            win = True
        io.recvline()

    if not win:
        raise ValueError("Failed to forge char, maybe padding was already there?")
    else:
        return imms


def find_imms_block(pre, front_ct):
    """
    Find block of the immediate state using the padding oracle.
    """
    imms = b""
    for rnd in range(16):
        imms = find_imm_chr(pre, front_ct, imms)

    return imms


def find_imms_blocks(pre, pt):
    pt = cup.pad(pt, 16)
    pt_blocks = split_blocks(pt)

    blocks = [os.urandom(16)]

    for pt_block in reversed(pt_blocks):
        front_ct = blocks[0]
        imms = find_imms_block(pre, front_ct)
        block = pwn.xor(imms, pt_block)
        blocks = [block] + blocks

    return blocks


"""
numbers:xxx,xxx,xxx ... # generally takes 2.5 blocks
"""

io = connect()
ticket, winning_nums = get_params(io)
challenge = "numbers:" + ",".join([str(x) for x in winning_nums])
challenge = challenge.encode()

iv = ticket[:16]
ct = ticket[16:]
ct = split_blocks(ct)

pre_blocks = [iv] + ct[:3]
pre = b"".join(pre_blocks)

blocks = find_imms_blocks(pre, challenge)
print(blocks)

iv = pre_blocks[-1]

payload = [iv] + blocks
payload = b"".join(payload)
payload = base64.b64encode(payload)
io.clean()
io.sendline(payload)
io.interactive()
