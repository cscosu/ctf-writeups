import z3
from pprint import pprint
import string

solver = z3.Solver()

FLAG = z3.BitVecs(" ".join([f"FLAG_{i}" for i in range(27)]), 8)

solver.add(FLAG[0] == ord("C"))
solver.add(FLAG[1] == ord("T"))
solver.add(FLAG[2] == ord("F"))
solver.add(FLAG[3] == ord("{"))
solver.add(FLAG[-1] == ord("}"))

for b in FLAG[4:-1]:
    solver.add(b >= ord(" "))
    solver.add(b <= ord("~"))

ROM = [z3.BitVecVal(0, 8)] * 256

# fmt: off
tmp = [187, 85, 171, 197, 185, 157, 201, 105, 187, 55, 217, 205, 33, 179, 207, 207, 159, 9, 181, 61, 235, 127, 87, 161, 235, 135, 103, 35, 23, 37, 209, 27, 8, 100, 100, 53, 145, 100, 231, 160, 6, 170, 221, 117, 23, 157, 109, 92, 94, 25, 253, 233, 12, 249, 180, 131, 134, 34, 66, 30, 87, 161, 40, 98, 250, 123, 27, 186, 30, 180, 179, 88, 198, 243, 140, 144, 59, 186, 25, 110, 206, 223, 241, 37, 141, 64, 128, 112, 224, 77, 28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
# fmt: on

tmp = [z3.BitVecVal(x, 8) for x in tmp]
ROM[:128] = tmp

start = 0b10000000
ROM[start : start + len(FLAG)] = FLAG

A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W, X, Y, Z = [0] * 26
S = 0


def go(include_level=0):
    global A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W, X, Y, Z

    if include_level > 12:
        if S == 0:
            S = 24

        if S == 1:
            S = 2
            R ^= 0b11111111

        if S == 2:
            S = 3
            Z = 0b00000001

        if S == 3:
            S = 4
            R += Z
            R &= 0xFF

        if S == 4:
            S = 5
            R += Z
            R &= 0xFF

        if S == 5:
            S = 6
            # Comparing a Z3 BitVec to an int will always be false, so add
            # asserts just in case.
            assert type(R) is int
            if R == 0b00000000:
                S = 38

        if S == 6:
            S = 7
            R += Z
            R &= 0xFF

        if S == 7:
            S = 8
            assert type(R) is int
            if R == 0b00000000:
                S = 59

        if S == 8:
            S = 9
            R += Z
            R &= 0xFF

        if S == 9:
            S = 10
            assert type(R) is int
            if R == 0b00000000:
                S = 59

        if S == 10:
            S = 11
            raise ValueError("BUG")

        if S == 11:
            S = -1

        if S == 12:
            S = 13
            X = 0b00000001

        if S == 13:
            S = 14
            Y = 0b00000000

        if S == 14:
            S = 15
            assert type(X) is int
            if X == 0b00000000:
                S = 22

        if S == 15:
            S = 16
            Z = X

        if S == 16:
            S = 17
            Z &= B

        if S == 17:
            S = 18
            # Very shit hack to fix type issues
            tmp = int(repr(z3.simplify(Z)))
            if tmp == 0b00000000:
                S = 19

        if S == 18:
            S = 19
            Y += A
            Y &= 0xFF

        if S == 19:
            S = 20
            X += X
            X &= 0xFF

        if S == 20:
            S = 21
            A += A
            A &= 0xFF

        if S == 21:
            S = 14

        if S == 22:
            S = 23
            A = Y

        if S == 23:
            S = 1

        if S == 24:
            S = 25
            I = 0b00000000

        if S == 25:
            S = 26
            M = 0b00000000

        if S == 26:
            S = 27
            N = 0b00000001

        if S == 27:
            S = 28
            P = 0b00000000

        if S == 28:
            S = 29
            Q = 0b00000000

        if S == 29:
            S = 30
            B = 0b11100101

        if S == 30:
            S = 31
            B += I
            B &= 0xFF

        if S == 31:
            S = 32
            assert type(B) is int
            if B == 0b00000000:
                S = 56

        if S == 32:
            S = 33
            B = 0b10000000

        if S == 33:
            S = 34
            B += I
            B &= 0xFF

        if S == 34:
            S = 35
            A = ROM[B]

        if S == 35:
            S = 36
            B = ROM[I]

        if S == 36:
            S = 37
            R = 0b00000001

        if S == 37:
            S = 12

        if S == 38:
            S = 39
            O = M

        if S == 39:
            S = 40
            O += N
            O &= 0xFF

        if S == 40:
            S = 41
            M = N

        if S == 41:
            S = 42
            N = O

        if S == 42:
            S = 43
            A += M
            A &= 0xFF

        if S == 43:
            S = 44
            B = 0b00100000

        if S == 44:
            S = 45
            B += I
            B &= 0xFF

        if S == 45:
            S = 46
            C = ROM[B]

        if S == 46:
            S = 47
            A ^= C

        if S == 47:
            S = 48
            P += A
            P &= 0xFF

        if S == 48:
            S = 49
            B = 0b01000000

        if S == 49:
            S = 50
            B += I
            B &= 0xFF

        if S == 50:
            S = 51
            A = ROM[B]

        if S == 51:
            S = 52
            A ^= P

        if S == 52:
            S = 53
            Q |= A

        if S == 53:
            S = 54
            A = 0b00000001

        if S == 54:
            S = 55
            I += A
            I &= 0xFF

        if S == 55:
            S = 29

        if S == 56:
            solver.add(Q == 0b00000000)
            S = 58

        if S == 57:
            S = 58
            raise ValueError("INVALID_FLAG")

        if S == 58:
            S = -1
    else:
        if S != -1:
            go(include_level + 1)
        if S != -1:
            go(include_level + 1)

    print(".", end="", flush=True)

    if include_level == 0:
        print()
        if S != -1:
            raise ValueError("Failed to execute program")
        print("Win")


go()

print(solver.check())
model = solver.model()

flag = bytes(model.evaluate(c).as_long() for c in FLAG).decode()
print(flag)
