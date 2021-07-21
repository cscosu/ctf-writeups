# Filestore

**Category**: misc \
**Points**: 50 (321 solves)

We stored our flag on this platform, but forgot to save the id. Can you help us
restore it?

```
nc filestore.2021.ctfcompetition.com 1337
```

Attachments: `filestore.py`

## Solution

The server lets you save text in a 64 KB `bytearray`. The flag is stored at the
beginning of the array, but we aren't able to fetch it. Instead, we can store
our own text. The server also implements
[deduplication](https://en.wikipedia.org/wiki/Data_deduplication) which is a
method to save storage space by re-using existing data that matches new data.
The server also lets us query the amount of storage space used, so we can use
this as compression oracle to brute-force characters one-by-one.

Basically we send `CTF{a`, `CTF{b`, `CTF{c`, etc., and the one that uses the
least space must be correct. I sped this up by using 32 simultaneous
connections.

> Another way I sped this up to was to first send single characters like `a`,
> `b`, `c`, etc., and found that these characters had the lowest sizes:
> `cdfinptuCFMRT0134_{}`. Those are the characters contained in the flag, so we
> can limit ourselves to this character set.

I was able to recover `CTF{CR1M3_0f_d3d`, but then ran into issues where many
characters had the smallest size. This was because my string was 16 characters,
and the block size was also 16 bytes, so the server would match the next
character wherever it wanted.

```
           0123456789012345
           ----------------
1st block: CTF{CR1M3_0f_d3d
2nd block: X (where X denotes the unknown character)
```

For example if guess the character `1` for `X`, it could also match the `CR1ME`
instead of `d3d1`. The problem with this is every character contained in the
flag will now result in the same size.

A simple workaround was to start from the end and
send `a}`, `b}`, `c}`, etc., and work backwards.

Solve script in `solve.py`:

```
$ python3 solve.py
[+] Opening connection to filestore.2021.ctfcompetition.com on port 1337: Done
/home/plushie/Programs/archive/pwntools/pwnlib/tubes/tube.py:822: BytesWarning: Text is not bytes; assuming ASCII, no guarantees. See https://docs.pwntools.com/#bytes
  res = self.recvuntil(delim, timeout=timeout)
solve.py:15: BytesWarning: Text is not bytes; assuming ASCII, no guarantees. See https://docs.pwntools.com/#bytes
...

[*] Closed connection to filestore.2021.ctfcompetition.com port 1337
[*] Closed connection to filestore.2021.ctfcompetition.com port 1337
_ => 0.037
n => 0.037
} => 0.037
[*] Closed connection to filestore.2021.ctfcompetition.com port 1337
[*] Closed connection to filestore.2021.ctfcompetition.com port 1337
f => 0.037R => 0.037

[+] known = up1ic4ti0n}
[*] Best guess: CTF{CR1M3_0f_d3dup1ic4ti0n}
```

> Note: The flag references the [CRIME](https://en.wikipedia.org/wiki/CRIME)
> attack, which was a compression oracle vunlerability in TLS
