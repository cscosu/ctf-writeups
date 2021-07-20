import pwn
import z3


solver = z3.Solver()

inp = z3.BitVecs(" ".join([f"inp_{i}" for i in range(8)]), 8)
for c in inp:
    solver.add(c >= ord(" "))
    solver.add(c <= ord("~"))

assert len(inp) == 8
R2 = z3.Concat(*inp[0:4][::-1])
R3 = z3.Concat(*inp[4:8][::-1])

R0 = z3.BitVecVal(0x6F67202A, 32)  # " *go"
R0, R2 = R2, R0
R1 = z3.BitVecVal(1, 32)

# hex1()
# Since R1 is constant, `tstbit(R1, 0x6) is always false, so we only need to
# focus on one branch.
R5 = z3.BitVecVal(0x0A5D2F34, 32)
R0 += R5
R0 = -1 - R0

R2 ^= R0
R0 = z3.BitVecVal(0x656C676F, 32)  # "ogle"
R0, R3 = R3, R0
R1 = z3.BitVecVal(6, 32)

# hex2()
R0 = -1 - R0
R5 = z3.BitVecVal(0x48268673, 32)
R0 ^= R5

R3 ^= R0
R0 = z3.BitVecVal(0x6E696220, 32)  # " bin"
R1 = z3.BitVecVal(15, 32)

# hex3()
R5 = z3.BitVecVal(0x5A921187, 32)
R0 ^= R5
R5 = z3.BitVecVal(0xE9BB17BC, 32)
R0 += R5

R0 ^= R3
R2, R3 = R3, R2 ^ R0
R0 = z3.BitVecVal(0x682D616A, 32)  # "ja-h"
R1 = z3.BitVecVal(28, 32)

# hex4()
R0 = -1 - R0
R5 = z3.BitVecVal(0xD71037D1, 32)
R0 ^= R5

R0 ^= R3
R2, R3 = R3, R2 ^ R0
R0 = z3.BitVecVal(0x67617865, 32)  # "exag"
R1 = z3.BitVecVal(45, 32)

# hex5()
P0 = z3.BitVecVal(0xFF, 32)
R0 = -1 - R0
R5 = z3.BitVecVal(0x101FBCCC, 32)
R0 += R5

R0 ^= R3
R2, R3 = R3, R2 ^ R0
R0 = z3.BitVecVal(0x2A206E6F, 32)  # "on *"
R1 = z3.BitVecVal(66, 32)

# hex6()
P0 = z3.BitVecVal(0, 32)
R5 = z3.BitVecVal(0x8B0163C1, 32)
R0 ^= R5
R5 = z3.BitVecVal(0xEECE328B, 32)
R0 ^= R5

R0 ^= R3
R2, R3 = R3, R2 ^ R0

R4 = z3.BitVecVal(0x6D80BF97, 32)
R5 = z3.BitVecVal(0x9D450E3D, 32)

solver.add(R5 == R3)
solver.add(R4 == R2)

print(solver.check())
model = solver.model()

inpc = [model.evaluate(c) for c in inp]
inpc = [c.as_long() for c in inpc]

inpc = bytes(inpc).decode()
print(inpc)
