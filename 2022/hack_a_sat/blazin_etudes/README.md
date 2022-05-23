Blazin' Etudes
====

Summary
----

This challenge is basicially a bunch of Microblaze binaries like the Ominous Etude challenge, but the math in each is a bit different to check the input. The server will prompt you for solutions to a few of the binaries at random.

As with Ominous Etude, my approach was to use Binary Ninja and a SMT solver. I wrote a script that converts Binary Ninja HLIL (High-level intermediate language, basically the decompiler output as an AST) into a [claripy](https://github.com/angr/claripy) expression, and then invokes the solver.

Details
----

The [Microblaze binary ninja plugin](https://github.com/amtal/microblaze) had a few bugs:
- 32-bit immediates were not handled correctly. This caused bad call targets for the previous 'Ominous Etude' challenge, and also caused bad constants to show for the XOR. I fixed this with a hack in solve.py to pull the immediate out of the instructions manually.
- SRL was lifted as a left-shift. It is really a right-shift. Patch in `microblaze.patch`