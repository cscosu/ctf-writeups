import claripy
import binaryninja
from binaryninja.highlevelil import HighLevelILOperation
from binaryninja.mediumlevelil import SSAVariable
from base64 import b64encode

from pwn import *
context.log_level = 'debug'

TICKET = ""

p = remote("blazin_etudes.satellitesabove.me", 5300)
p.recvuntil("Ticket please:\n")
p.sendline(TICKET)
p.recvline()
p.recvline()


class Walker:
    def __init__(self, bv):
        self.bv = bv
        self.x = claripy.BVS('x', 32)
    def _handle(self, x):
        if x.operation == HighLevelILOperation.HLIL_ADD:
            return self._handle(x.left) + self._handle(x.right)
        elif x.operation == HighLevelILOperation.HLIL_LSR:
            return claripy.LShR(self._handle(x.left), self._handle(x.right))
        elif x.operation == HighLevelILOperation.HLIL_SUB:
            return self._handle(x.left) - self._handle(x.right)
        elif x.operation == HighLevelILOperation.HLIL_CONST:
            return claripy.BVV(x.constant, 32)
        elif x.operation == HighLevelILOperation.HLIL_VAR:
            # Fold variable definitions (took this code from another project i was working on)
            # Alternatively, we could have added variables to Z3 and let it handle things... but I
            # since it seems we can write a single expressions for these challenges, that's what I did.
            ssa_variable = x.ssa_form.var
            assert isinstance(ssa_variable, SSAVariable)
            var_def_inst = x.function.ssa_form.get_ssa_var_definition(ssa_variable)
            if var_def_inst is None and 'arg' in x.var.name:
                return self.x
            assert var_def_inst.operation == HighLevelILOperation.HLIL_VAR_INIT_SSA, f"{x} {var_def_inst}"
            to_fold = var_def_inst.src.non_ssa_form
            #print(f"traceback: {var_def_inst} {to_fold}")
            return self._handle(to_fold)
        elif x.operation == HighLevelILOperation.HLIL_XOR:
            # Every problem uses XOR to check that the result of the computation is correct
            assert x.right.operation == HighLevelILOperation.HLIL_CONST
            
            # HACK: The immediate handling is wrong in the microblaze plugin
            const_pt1 = x.right.constant
            inst_bytes_addr = x.address
            b = self.bv.read(inst_bytes_addr, 4)
            assert b[0] == 0xb0
            const_pt2 = u16(b[2:], endian='big')
            const_all = (const_pt1 & 0xffff) | (const_pt2 << 16)
            print(f"const_all: {hex(const_all)}")

            return self._handle(x.left) ^ claripy.BVV(const_all, 32)
        elif x.operation == HighLevelILOperation.HLIL_CALL:
            assert x.dest.operation == HighLevelILOperation.HLIL_CONST_PTR
            f = self.bv.get_function_at(x.dest.constant)
            if f.name == '__udivsi3':
                left, right = tuple(x.params)
                return self._handle(left) / self._handle(right)
            else:
                raise RuntimeError(f"Unimplemented {f.name}")
        else:
            raise RuntimeError(f"Unimplemented {str(x.operation)}")

BASE_FOLDER = "<base folder containing all the binaries>"
while True:
    chall, c_hash = p.recvline().decode().split("\t")
    print(chall)

    with binaryninja.open_view(BASE_FOLDER+chall) as bv:
        f = bv.get_functions_by_name("quick_maths")[0]
        hlil = f.hlil
        body = hlil.root.body

        last_stmt = body[-4]
        assert last_stmt.src.operation == HighLevelILOperation.HLIL_XOR

        # last_stmt.src must be 0
        w = Walker(bv)
        expr = w._handle(last_stmt.src)
        print(expr)
        solver = claripy.Solver()
        solver.add(expr == 0)

        try:
            ans = solver.eval(w.x, 1)
            print(f"{ans}")
            p.sendline(b64encode((str(ans[0]) + "\n").encode('utf-8')))
        except claripy.errors.UnsatError:
            print('unsat')
            print(f"{solver.unsat_core()}")