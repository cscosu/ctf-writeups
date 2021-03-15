# Delphi

**Category**: Crypto \
**Points**: 998 (18 solves) \
**Author**: Sohmaster

## Challenge

Help me forge a token quickly.

`nc crypto.utctf.live 4356`

**Hint**: The server is not lagging.

## Overview

No source code provided, so let's just try connecting:
```
$ nc crypto.utctf.live 4356
Welcome to the secure flag vault.
Only authorized users can retrieve the flag.
Just encrypt the following challenge in bytes with the secret key.
Use AES-256-CBC with PKCS7 padding. The first 16 bytes should be the IV.
Submit it in hex encoded form.
For security reasons, only 12289 tries are permitted.
Challenge: 80cb208eb56643d4c41c995fb011766dab696872715c1ef75aa42ca09364cc69

Uh-oh. Someone is trying to shut down the system.
The connection will close in 29 seconds.

29 seconds remain. 12289 tries left.
Please submit authorization token.
00
Decryption failed.
```

## Solution

This is a padding oracle attack on AES-CBC.
The challenge we have to encrypt is 32 bytes, so we have to forge 3 blocks.

I don't really feel like doing a detailed write-up since there are already many
[resources](https://robertheaton.com/2013/07/29/padding-oracle-attack/) on
padding oracle attacks.

As always, this image is helpful in understanding what's going on:
![cbc](https://upload.wikimedia.org/wikipedia/commons/thumb/2/2a/CBC_decryption.svg/1200px-CBC_decryption.svg.png)

We use the padding oracle to determine the immediate states where the
ciphertext is XOR'd with the plaintext, and use that to control the decryption.
Since we also control the IV, we have full control over all blocks.

The only real twist to this challenge was the time limit. Sending requests
one-by-one would take too long, so a trick I learned was to just send 256
messages at once and parse the output in bulk.

Most of the work was done in this function I wrote:
```python
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
```

To solve for multiple blocks, I did:
```python
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
```

Full script is in `solve.py`. I also wrote a local server in `aes.py` for
testing.

Output:
```
$ python3 solve.py
[+] Opening connection to crypto.utctf.live on port 4356: Done
[+] Got challenge 6ba2cc1f88a3ebc42f0aec850ab4583f86c5e05679e36854bedca1d97ecc4177
[+] Got 136 for round 0
[+] Got 48 for round 1
[+] Got 52 for round 2
[+] Got 104 for round 3
[+] Got 12 for round 4
[+] Got 129 for round 5
[+] Got 82 for round 6
[+] Got 123 for round 7
[+] Got 198 for round 8
[+] Got 202 for round 9
[+] Got 153 for round 10
[+] Got 192 for round 11
[+] Got 173 for round 12
[+] Got 232 for round 13
[+] Got 231 for round 14
[+] Got 188 for round 15
[b'\xbc\xf8\xf6\xb0\xdc\x82\xd0\xdfcE\x97\x19|\'"\x99', b'@\x1d1\x02\xf5\xebB\xce\xd8\xc7\xb7\xd4\xf0\xfd\xb2G']
[+] Got 186 for round 0
[+] Got 5 for round 1
[+] Got 41 for round 2
[+] Got 30 for round 3
[+] Got 29 for round 4
[+] Got 205 for round 5
[+] Got 161 for round 6
[+] Got 195 for round 7
[+] Got 246 for round 8
[+] Got 37 for round 9
[+] Got 120 for round 10
[+] Got 136 for round 11
[+] Got 146 for round 12
[+] Got 247 for round 13
[+] Got 68 for round 14
[+] Got 119 for round 15
[b'\xe1\x8e\x19\xc9\xfd\x90G\xabuzj\xc1d\xe6F\xcc', b'\xbc\xf8\xf6\xb0\xdc\x82\xd0\xdfcE\x97\x19|\'"\x99', b'@\x1d1\x02\xf5\xebB\xce\xd8\xc7\xb7\xd4\xf0\xfd\xb2G']
[+] Got 235 for round 0
[+] Got 164 for round 1
[+] Got 221 for round 2
[+] Got 232 for round 3
[+] Got 64 for round 4
[+] Got 245 for round 5
[+] Got 213 for round 6
[+] Got 248 for round 7
[+] Got 70 for round 8
[+] Got 218 for round 9
[+] Got 241 for round 10
[+] Got 73 for round 11
[+] Got 119 for round 12
[+] Got 105 for round 13
[+] Got 63 for round 14
[+] Got 219 for round 15
[b'\xa0\x92\xabe\xcdY;\x8b\xdf\xd8\x1f\xc0\xe6j\xfe\xd5', b'\xe1\x8e\x19\xc9\xfd\x90G\xabuzj\xc1d\xe6F\xcc', b'\xbc\xf8\xf6\xb0\xdc\x82\xd0\xdfcE\x97\x19|\'"\x99', b'@\x1d1\x02\xf5\xebB\xce\xd8\xc7\xb7\xd4\xf0\xfd\xb2G']
a092ab65cd593b8bdfd81fc0e66afed5e18e19c9fd9047ab757a6ac164e646ccbcf8f6b0dc82d0df634597197c272299401d3102f5eb42ced8c7b7d4f0fdb247
[*] Switching to interactive mode

The flag is utflag{oracle_padded_oops}
[*] Got EOF while reading in interactive
$
```
