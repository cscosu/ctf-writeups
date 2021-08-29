hwdbg
====

Writeup by Andrew Haberlandt (ath0)

Solved with @qxxxb

I don't know much about linux kernel pwn. But I'm familiar with userspace. `hwdbg` is a setuid program so if we pwn it, we can read the flag and win. They give us direct access to physical memory, so this should be easy. There should be some (writable) pages in physical memory somewhere for the hwdbg program. My initial thought is that we ought to be able to find something to overwrite (malloc_hook, or something you otherwise might use for exploitation in userspace). But how to know what physical page our program is in?

qxxxb had heard of a cool tool to show page tables in GDB when attached to QEMU. https://github.com/martinradev/gdb-pt-dump/

I modified this tool slightly to output the physical addresses when using the `pt -sb` command to search. (see gdb-pt-dump.patch)

Searching for some unique sequence of instructions in `hwdbg`, we get an interesting result:

```
pt -sb ba19000000be01000000488d3d4e3d0000e8a2050000
Found at 0xffff9e4a038e5316 in   0xffff9e4a035e0000 : 0xa00000 | W:1 X:0 S:1 UC:0 WB:1
Found at 0xffffffffa94e5316 in   0xffffffffa91e0000 : 0x420000 | W:1 X:0 S:1 UC:0 WB:1
```

This is before even running `hwdbg` even once. There is a *writable* page in physical memory containing the executable. We didn't bother to check, but the entire filesystem is probably be sitting in physical memory. And better yet, it's at a constant address.

If you run `hwdbg` once (and let it hang running) we get a better picture of what is going on:

```
gef➤  pt -sb ba19000000be01000000488d3d4e3d0000e8a2050000
Found at 0x401316 in             0x401000 :   0x4000 | W:0 X:1 S:0 UC:0 WB:1 (phys 0x38e5000)
Found at 0xffff9e4a038e5316 in   0xffff9e4a035e0000 : 0xa00000 | W:1 X:0 S:1 UC:0 WB:1
Found at 0xffffffffa94e5316 in   0xffffffffa91e0000 : 0x420000 | W:1 X:0 S:1 UC:0 WB:1
```

Our executable page is mapped at 0x401000 in `hwdbg`'s virtual address space, and that maps to physical address 0x38e5000. The other match `0xffff9e4a038e5316` is just the mapping of this page in the kernel's virtual address space -- note after slide `0xffff9e4a0` everything is the same.

So when our executable is launched, it literally just adds a single page table entry to map our page from the filesystem into the process (as executable), but we can still write to this from /dev/mem.

The sequence of instructions I was searching for was not entirely randomly chosen... this is a decent spot to patch in the `io_read` function of this program -- this functionality is not needed.

![screenshot1](screenshot1.png)


So we just patch this out with code that does a open+read+write, then we run any valid 'ior' command:
```
/bin/hwdbg ior 1 0
```
and we win. See solve.py.
