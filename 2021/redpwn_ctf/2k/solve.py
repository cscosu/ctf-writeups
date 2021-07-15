import string
import sys
from pprint import pprint
import z3
import time

prog = list(open("prog.bin", "rb").read())

i = 0
tape = [z3.BitVecVal(0, 16)] * 0x800
tape_index = 0
stack = []
mask = 0xFFFF


inp = z3.BitVecs(" ".join([f"inp_{i}" for i in range(64)]), 16)
inp_index = 0

solver = z3.Solver()

for c in inp:
    solver.add(c >= ord(" "))
    solver.add(c <= ord("~"))

i = 0


def check_jmp(addr, res):
    if addr == 4:
        # addr 4 is exit with failure
        solver.add(z3.Not(res))


def do_jmp(res):
    # The only `jmp` calls in this program are conditional jumps to address 4,
    # we'll just pretend that we don't fail and continue
    assert addr == 4


while i < len(prog):
    # if i == 0x212:
    # if i == 0x2A3B:
    # if i == 0x216:
    # if i == 0x2a5a:
    # break

    msg = ""

    l = hex(i) + ": "
    if prog[i] == 0x1:
        val = stack.pop()
        stack.append(val)
        stack.append(val)
        msg = l + "dup\t\t\t\t\t({})".format(str(val))

    elif prog[i] == 0x3:
        a = stack.pop()
        msg = l + "exit {}".format(a)
        print(msg)
        break

    elif prog[i] == 0x10:
        b = stack.pop()
        a = stack.pop()
        res = a + b
        stack.append(b + a)
        msg = l + "add \t\t\t\t{} + {} = {}".format(b, a, res)

    elif prog[i] == 0x11:
        b = stack.pop()
        a = stack.pop()
        res = b - a
        stack.append(b - a)
        msg = l + "sub \t\t\t\t{} - {} = {}".format(b, a, res)

    elif prog[i] == 0x12:
        b = stack.pop()
        a = stack.pop()
        res = b * a
        stack.append(res)
        msg = l + "mul \t\t\t\t{} * {} = {}".format(b, a, res)

    elif prog[i] == 0x13:
        a = stack.pop()
        b = stack.pop()

        if isinstance(a, int):
            a = z3.BitVecVal(a, 16)
        if isinstance(b, int):
            b = z3.BitVecVal(b, 16)

        a32 = z3.SignExt(16, a)
        b32 = z3.SignExt(16, b)
        # res32 = a32.SRem(b32)
        res32 = a32 / b32
        res = z3.Extract(15, 0, res32)

        stack.append(res)
        msg = l + "div \t\t\t\t{} // {} = {}".format(a, b, res)
        pass

    elif prog[i] == 0x14:
        a = stack.pop()
        b = stack.pop()

        if isinstance(a, int):
            a = z3.BitVecVal(a, 16)
        if isinstance(b, int):
            b = z3.BitVecVal(b, 16)

        a32 = z3.SignExt(16, a)
        b32 = z3.SignExt(16, b)
        res32 = z3.SRem(a32, b32)
        res = z3.Extract(15, 0, res32)

        stack.append(res)
        msg = l + "mod \t\t\t\t{} % {} = {}".format(a, b, res)

    elif prog[i] == 0x15:
        a = stack.pop()
        b = stack.pop()
        c = stack.pop()

        if isinstance(a, int):
            a = z3.BitVecVal(a, 16)
        if isinstance(b, int):
            b = z3.BitVecVal(b, 16)
        if isinstance(c, int):
            c = z3.BitVecVal(c, 16)

        a32 = z3.ZeroExt(16, a)
        b32 = z3.ZeroExt(16, b)
        c32 = z3.ZeroExt(16, c)

        m32 = c32 * b32
        res32 = z3.SRem(m32, a32)
        res = z3.Extract(15, 0, res32)
        stack.append(res)
        msg = l + "modmul \t\t\t\t({} * {}) % {} = {}".format(b, c, a, res)

    elif prog[i] == 0x16:
        a = stack.pop()
        b = stack.pop()

        res = z3.If(a == b, z3.BitVecVal(1, 16), z3.BitVecVal(0, 16))

        stack.append(res)

        msg = l + "push({} == {})\t\t->{}".format(a, b, res)

    elif prog[i] == 0x17:
        before = stack[-1]

        stack[-1] = z3.If(
            stack[-1] == 0,
            0,
            z3.If(stack[-1] < 0, z3.BitVecVal(-1, 16), z3.BitVecVal(1, 16)),
        )

        msg = l + "sign {} -> {}".format(before, stack[-1])

    elif prog[i] == 0x20:
        msg = l + "push getc() -> {}".format(inp[inp_index])
        stack.append(inp[inp_index])
        inp_index += 1

    elif prog[i] == 0x21:
        msg = l + "print '{}'".format(chr(stack.pop()))

    elif prog[i] == 0x22:
        val = hex(prog[i + 2])[2:] + hex(prog[i + 1])[2:]
        val = int(val, 16)
        msg = l + "push {}".format(val)

        stack.append(val)
        i += 2  # plus 2 not 3 because we always add 1 :)

    elif prog[i] == 0x30:
        addr = stack.pop()
        msg = l + f"goto {addr}"
        i = addr - 1

    elif prog[i] == 0x31:
        addr = stack.pop()
        cond = stack.pop()
        res = cond == 0
        check_jmp(addr, res)
        msg = l + "jmp {} if {} == 0 -> {}".format(addr, cond, res)
        # if fail or success two items are always popped.
        do_jmp(res)

    elif prog[i] == 0x32:
        addr = stack.pop()
        cond = stack.pop()
        res = cond != 0
        check_jmp(addr, res)
        msg = l + "jmp {} if {} != 0".format(addr, cond, res)
        do_jmp(res)

    elif prog[i] == 0x33:
        addr = stack.pop()
        cond = stack.pop()
        res = cond < 0
        check_jmp(addr, res)
        msg = l + "jmp {} if {} < 0".format(addr, cond, res)
        do_jmp(res)

    elif prog[i] == 0x34:
        addr = stack.pop()
        cond = stack.pop()
        res = cond > 0
        check_jmp(addr, res)
        msg = l + "jmp {} if {} > 0".format(addr, cond, res)
        do_jmp(res)

    elif prog[i] == 0x35:
        addr = stack.pop()
        cond = stack.pop()
        res = cond <= 0
        check_jmp(addr, res)
        msg = l + "jmp {} if {} <= 0".format(addr, cond, res)
        do_jmp(res)

    elif prog[i] == 0x36:
        addr = stack.pop()
        cond = stack.pop()
        res = cond >= 0
        check_jmp(addr, res)
        msg = l + "jmp {} if {} >= 0".format(addr, cond, res)
        do_jmp(res)

    elif prog[i] == 0x40:
        a = stack.pop()
        tape[tape_index] = a
        msg = l + "tape[{}] = pop = {}".format(tape_index, a)

    elif prog[i] == 0x41:
        a = tape[tape_index]
        stack.append(a)
        msg = l + "push = tape[{}] = {}".format(tape_index, a)

    elif prog[i] == 0x50:
        tape_index = (tape_index + 1) & mask
        msg = l + "tape_index += 1\t\t -> {}".format(tape_index)

    elif prog[i] == 0x51:
        tape_index = (tape_index - 1) & mask
        msg = l + "tape_index -= 1\t\t -> {}".format(tape_index)

    elif prog[i] == 0x52:
        a = stack.pop()
        b = tape_index + a
        tape_index = b

    elif prog[i] == 0x53:
        a = stack.pop()
        b = tape_index - a
        msg = l + "tape_index -= pop\t\t{} -> {}".format(tape_index, b)
        tape_index = b

    else:
        msg = l + "unknown opcode " + hex(prog[i])
        raise ValueError(msg)

    i += 1
    print(msg)


print(solver.check())
model = solver.model()

inpc = [model.evaluate(c) for c in inp]
inpc = [c.as_long() for c in inpc]

inpc = bytes(inpc).decode()
print(inpc)
