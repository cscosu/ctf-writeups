# pythia

**Category**: crypto \
**Points**: 173 (65 solves)

Yet another oracle, but the queries are costly and limited so be frugal with
them.

```
nc pythia.2021.ctfcompetition.com 1337
```

Attachments: `server.py`

## Overview

The premise is pretty simple:

- The server picks 3 random passwords, but they are only 3 characters each
  (which normally can be brute-forced).

- We can submit ciphertexts for the server to decrypt with AES GCM mode. We
  also get to choose the nonce, and we pick which of the 3 passwords to use.

- If we find all 3 passwords, then the server sends us the flag.

- However, each decryption takes 10 seconds, and we are only allowed to use it
  150 times.

## Solution

A naive bruteforce requires around `26^3 / 2` attempts per character, which
exceeds the limit. But if we can send specially crafted ciphertexts so that
decryption is only successful for half the known keys, then we can use this as
an oracle to binary search for the key.

Luckliy [this paper](https://eprint.iacr.org/2020/1491.pdf) has us covered, and
even provides a SageMath
[implementation](https://github.com/julialen/key_multicollision)!

I just copied it and wrote a pwntools wrapper to solve this challenge (script
in `solve.sage`). One issue is that generating a ciphertext to collide `26^3 /
2` keys took way too long on my machine. Instead the largest partition size I
chose was 1024 keys, which worked well enough.

```
$ sage solve.sage REMOTE
[x] Opening connection to pythia.2021.ctfcompetition.com on port 1337
[x] Opening connection to pythia.2021.ctfcompetition.com on port 1337: Trying 34.77.25.116
[+] Opening connection to pythia.2021.ctfcompetition.com on port 1337: Done
17576it [00:01, 13695.86it/s]
[+] Decryption successful 1024 7
Making collisions for 128 keys ...
Done
All 128 keys decrypted the ciphertext
Making collisions for 128 keys ...
Done
All 128 keys decrypted the ciphertext
Making collisions for 64 keys ...
Done
All 64 keys decrypted the ciphertext
Making collisions for 64 keys ...
Done
...
All 1 keys decrypted the ciphertext
[+] Found password = b'kta'
...
All 1 keys decrypted the ciphertext
[+] Found password = b'zod'
All 1 keys decrypted the ciphertext
[+] Found password = b'rqk'
[+] passwords = [b'kta', b'zod', b'rqk']
[*] Switching to interactive mode
Checking...
ACCESS GRANTED: CTF{gCm_1s_n0t_v3ry_r0bust_4nd_1_sh0uld_us3_s0m3th1ng_els3_h3r3}
```
