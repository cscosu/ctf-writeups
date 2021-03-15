import pwn
from Crypto.Cipher import AES
import Crypto.Util.number as cun
import Crypto.Util.Padding as cup
from pprint import pprint
import os

if pwn.args.DEBUG:
    pwn.context.log_level = "debug"

if pwn.args.LOCAL:
    io = pwn.process("python3 aes.py", shell=True)
else:
    io = pwn.remote("crypto.utctf.live", 4356)

# AES-256-CBC, PKCS#7

io.recvuntil("Challenge: ")
challenge = bytes.fromhex(io.recvlineS().strip())
print(f"[+] Got challenge {challenge.hex()}")


def find_imm_chr(iv: bytes, front_ct: bytes, imms: bytes, rnd: int):
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

        payload = iv + ct + front_ct
        payloads.append(payload.hex())

    payload = "\n".join(payloads)
    io.sendlineafter("Please submit authorization token.", payload)

    win = False
    for i in range(256):
        if pwn.args.LOCAL:
            io.recvline()  # Discard "Please submit authorization token"
            res = io.recvline().strip()
            if res == b"Invalid challenge provided.":
                print(f"[+] Got {i} for round {rnd}")
                # i ^ imm = desired
                # i ^ desired = imm
                imms = cun.long_to_bytes(i ^ desired) + imms
                win = True
        else:
            io.recvline()
            res = io.recvline().strip()
            if res == b"Invalid challenge provided.":
                print(f"[+] Got {i} for round {rnd}")
                # i ^ imm = desired
                # i ^ desired = imm
                imms = cun.long_to_bytes(i ^ desired) + imms
                win = True
            io.recvline()
            io.recvline()

    if not win:
        raise ValueError("Failed to forge char, maybe padding was already there?")
    else:
        return imms


def find_imms_block(front_ct):
    """
    Find block of the immediate state using the padding oracle.
    """
    iv = b"\x00" * 16
    imms = b""
    for rnd in range(16):
        imms = find_imm_chr(iv, front_ct, imms, rnd)

    return imms


iv = b"\x00" * 16
blocks = [os.urandom(16)]

# Forge the 3rd padding block
front_ct = blocks[0]
imms = find_imms_block(front_ct)
block = pwn.xor(imms, b"\x10" * 16)
blocks = [block] + blocks
print(blocks)

# Forge the 2nd block (upper 16 bytes of challenge)
front_ct = blocks[0]
imms = find_imms_block(front_ct)
block = pwn.xor(imms, challenge[16:])
blocks = [block] + blocks
print(blocks)

# Forge the 1st block (lower 16 bytes of challenge)
front_ct = blocks[0]
imms = find_imms_block(front_ct)
block = pwn.xor(imms, challenge[:16])
blocks = [block] + blocks
print(blocks)

ans = "".join(block.hex() for block in blocks)
print(ans)
io.sendlineafter("Please submit authorization token.", ans)
io.interactive()
