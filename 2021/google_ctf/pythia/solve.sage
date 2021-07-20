from base64 import b64encode, b64decode
import string
import itertools
from tqdm import tqdm
import time
from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes
from cryptography.hazmat.backends import default_backend
from cryptography.hazmat.primitives.ciphers.aead import AESGCM
from cryptography.hazmat.primitives.kdf.scrypt import Scrypt
from cryptography.exceptions import InvalidTag
from Crypto.Cipher import AES
from Crypto.Random import get_random_bytes
from Crypto.Util.number import long_to_bytes, bytes_to_long
from bitstring import BitArray, Bits
import binascii

from cts import ct_chunks

import os

os.environ["PWNLIB_NOTERM"] = "true"
import pwn


def pick_option(op: int):
    io.sendlineafter(">>> ", str(op))


def send_ct(ct):
    pick_option(3)
    s = "{},{}".format(b64encode(nonce).decode(), b64encode(ct).decode())
    io.sendlineafter(">>> ", s)
    io.recvline()
    msg = io.recvlineS()
    if "ERROR" in msg:
        return False
    elif "successful" in msg:
        return True
    else:
        print(msg)
        raise ValueError("wat")


def set_key(i: int):
    pick_option(1)
    io.sendlineafter(">>> ", str(i))


ALL_ZEROS = b"\x00" * 16
GCM_BITS_PER_BLOCK = 128


def check_correctness(keyset, nonce, ct):
    flag = True

    for i, key in enumerate(keyset):
        aesgcm = AESGCM(key)
        try:
            aesgcm.decrypt(nonce, ct, None)
        except InvalidTag:
            print("key %s failed" % i)
            flag = False

    if flag:
        print("All %s keys decrypted the ciphertext" % len(keyset))


def pad(a):
    if len(a) < GCM_BITS_PER_BLOCK:
        diff = GCM_BITS_PER_BLOCK - len(a)
        zeros = ["0"] * diff
        a = a + zeros
    return a


def bytes_to_element(val, field, a):
    bits = BitArray(val)
    result = field.fetch_int(0)
    for i in range(len(bits)):
        if bits[i]:
            result += a ^ i
    return result


def multi_collide_gcm(keyset, nonce, tag, first_block=None, use_magma=False):
    # initialize matrix and vector spaces
    P.<x> = PolynomialRing(GF(2))
    p = x ^ 128 + x ^ 7 + x ^ 2 + x + 1
    GFghash.<a> = GF(2^128,'x',modulus=p)
    if use_magma:
        t = "p:=IrreducibleLowTermGF2Polynomial(128); GFghash<a> := ext<GF(2) | p>;"
        magma.eval(t)
    else:
        R = PolynomialRing(GFghash, "x")

    # encode length as lens
    if first_block is not None:
        ctbitlen = (len(keyset) + 1) * GCM_BITS_PER_BLOCK
    else:
        ctbitlen = len(keyset) * GCM_BITS_PER_BLOCK
    adbitlen = 0
    lens = (adbitlen << 64) | ctbitlen
    lens_byte = int(lens).to_bytes(16, byteorder="big")
    lens_bf = bytes_to_element(lens_byte, GFghash, a)

    # increment nonce
    nonce_plus = int((int.from_bytes(nonce, "big") << 32) | 1).to_bytes(16, "big")

    # encode fixed ciphertext block and tag
    if first_block is not None:
        block_bf = bytes_to_element(first_block, GFghash, a)
    tag_bf = bytes_to_element(tag, GFghash, a)
    keyset_len = len(keyset)

    if use_magma:
        I = []
        V = []
    else:
        pairs = []

    for k in keyset:
        # compute H
        aes = AES.new(k, AES.MODE_ECB)
        H = aes.encrypt(ALL_ZEROS)
        h_bf = bytes_to_element(H, GFghash, a)

        # compute P
        P = aes.encrypt(nonce_plus)
        p_bf = bytes_to_element(P, GFghash, a)

        if first_block is not None:
            # assign (lens * H) + P + T + (C1 * H^{k+2}) to b
            b = (lens_bf * h_bf) + p_bf + tag_bf + (block_bf * h_bf ^ (keyset_len + 2))
        else:
            # assign (lens * H) + P + T to b
            b = (lens_bf * h_bf) + p_bf + tag_bf

        # get pair (H, b*(H^-2))
        y = b * h_bf ^ -2
        if use_magma:
            I.append(h_bf)
            V.append(y)
        else:
            pairs.append((h_bf, y))

    # compute Lagrange interpolation
    if use_magma:
        f = magma("Interpolation(%s,%s)" % (I, V)).sage()
    else:
        f = R.lagrange_polynomial(pairs)
    coeffs = f.list()
    coeffs.reverse()

    # get ciphertext
    if first_block is not None:
        ct = list(map(str, block_bf.polynomial().list()))
        ct_pad = pad(ct)
        ct = Bits(bin="".join(ct_pad))
    else:
        ct = ""

    for i in range(len(coeffs)):
        ct_i = list(map(str, coeffs[i].polynomial().list()))
        ct_pad = pad(ct_i)
        ct_i = Bits(bin="".join(ct_pad))
        ct += ct_i
    ct = ct.bytes

    return ct + tag


def generate_cts():
    cts = []
    ns = [1024, 512, 256]

    for n in ns:
        chunks = [keys[x : x + n] for x in range(0, len(keys), n)]
        chunk_cts = []

        for i, chunk in enumerate(chunks):
            first_block = b"\x01"
            nonce = b"\x00" * 12
            tag = b"\x01" * 16
            keyset = chunk
            ct = multi_collide_gcm(keyset, nonce, tag, first_block=first_block)
            print(f"Got ciphertext for {n} {i}")
            check_correctness(keyset, nonce, ct)

            chunk_cts.append(ct)

        cts.append(chunk_cts)

    open("cts.py", "w").write(str(cts))


def make_collisions(keyset: list):
    print(f"Making collisions for {len(keyset)} keys ...")
    ct = multi_collide_gcm(keyset, nonce, tag, first_block=first_block)
    print("Done")
    check_correctness(keyset, nonce, ct)
    return ct


if False:
    # Run this to generate `cts.py`, which contains multi-collision ciphertexts.
    # Takes around 20 min to run :(
    generate_cts()


if pwn.args.REMOTE:
    io = pwn.remote("pythia.2021.ctfcompetition.com", 1337)
else:
    io = pwn.process("python3 server.py", shell=True)

first_block = b"\x01"
nonce = b"\x00" * 12
tag = b"\x01" * 16
ns = [1024, 512, 256]

passwords = [
    "".join(p).encode() for p in itertools.product(string.ascii_lowercase, repeat=3)
]
keys = [b"?"] * len(passwords)

for i, p in tqdm(enumerate(passwords)):
    kdf = Scrypt(salt=b"", length=16, n=2 ** 4, r=8, p=1, backend=default_backend())
    key = kdf.derive(p)
    keys[i] = key


final_passwords = []

for password_i in range(3):
    prev_chunk_i = None
    n = None

    for ct_chunks_i, ct_chunk in enumerate(ct_chunks):
        n = ns[ct_chunks_i]
        if prev_chunk_i is None:
            for ct_chunk_i, ct in enumerate(ct_chunk):
                if send_ct(ct):
                    print(f"[+] Decryption successful {n} {ct_chunk_i}")
                    prev_chunk_i = ct_chunk_i
                    break
        else:
            ct_chunk_i = 2 * prev_chunk_i
            if send_ct(ct_chunk[ct_chunk_i]):
                prev_chunk_i = ct_chunk_i
            else:
                # assert send_ct(ct_chunk[ct_chunk_i] + 1)
                prev_chunk_i = ct_chunk_i + 1

    assert prev_chunk_i != None
    assert n != None

    final_chunk_i = None

    while n > 1:
        assert n % 2 == 0

        start = prev_chunk_i * n
        end = start + n
        mid = (start + end) // 2
        chunk_left = keys[start:mid]
        chunk_right = keys[mid:end]

        ct_chunk_left = make_collisions(chunk_left)
        ct_chunk_right = make_collisions(chunk_left)

        n = n // 2

        if send_ct(ct_chunk_left):
            prev_chunk_i = 2 * prev_chunk_i
        else:
            # assert send_ct(ct_chunk_right)
            prev_chunk_i = 2 * prev_chunk_i + 1

        if n == 1:
            final_chunk_i = prev_chunk_i

    assert final_chunk_i != None
    key = keys[final_chunk_i]
    password = passwords[final_chunk_i]
    final_passwords.append(password)
    print(f"[+] Found password = {password}")

    if password_i < 2:
        set_key(password_i + 1)


print(f"[+] passwords = {final_passwords}")

pick_option(2)
io.sendlineafter(">>> ", b"".join(final_passwords))

io.interactive()
