# Mooosl

**Category**: Pwn

**Points**: 177 (18 solves)

**Author**: ?

## Challenge

**Description**: check my new baby toy! (Ubuntu 21.04: apt install musl)

**Attachments**: libc.so, mooosl

**I did not solve this challenge during the competition. After reading about some techniques others applied (mentioned below) I finished my solution two days later.**

I am going to try to go through this challenge with as much detail as possible. Perhaps a painful amount of deetail. If you just want to see the exploitation technique, you probably want to scroll down to Part 4.


## Part 1. Obtain and Run the Challenge

They told us to `apt install musl`, so we can google "apt musl" to find out this is installing the "musl" libc implementation. This also explains the challenge name.

Okay, so they gave us two files:
- libc.so (presumably, this is the same libc that you get by doing `apt install musl`)
- moosl
```
$ file mooosl
mooosl: ELF 64-bit LSB shared object, x86-64, version 1 (SYSV), dynamically linked, interpreter /lib/ld-musl-x86_64.so.1, stripped
```

Ok, so it's a 64-bit x86 executable, it's dynamically linked, and will use /lib/ld-musl-x86_64.so.1 as the linker. (Luckily, `apt install musl` also installed the linker in that exact location.)

I'm also going to run checksec to see if it was compiled with all the security mitigations or not.
```
$ checksec mooosl
[*] '/home/andrew/moosl/mooosl'
    Arch:     amd64-64-little
    RELRO:    Full RELRO
    Stack:    Canary found
    NX:       NX enabled
    PIE:      PIE enabled
```

OK - so all protections enabled. This is DEFCON Quals, after all.

To check my sanity, I want to make sure the libc that is getting loaded when the process runs is the same as the libc that they gave us.

So I ran `gdb ./mooosl` and then typed `run` and then pressed CTRL-C to interrupt the program, and then `info proc mappings` to get a list of memory mappings:

```
gef> info proc mappings
process 7409
Mapped address spaces:

          Start Addr           End Addr       Size     Offset objfile
      0x555555554000     0x555555555000     0x1000        0x0 /home/andrew/moosl/mooosl
      0x555555555000     0x555555556000     0x1000     0x1000 /home/andrew/moosl/mooosl
      0x555555556000     0x555555557000     0x1000     0x2000 /home/andrew/moosl/mooosl
      0x555555557000     0x555555558000     0x1000     0x2000 /home/andrew/moosl/mooosl
      0x555555558000     0x555555559000     0x1000     0x3000 /home/andrew/moosl/mooosl
      0x555555559000     0x555555561000     0x8000        0x0 [heap]
      0x555555561000     0x555555562000     0x1000        0x0 [heap]
      0x555555562000     0x555555563000     0x1000        0x0 [heap]
      0x7ffff7f41000     0x7ffff7f45000     0x4000        0x0 [vvar]
      0x7ffff7f45000     0x7ffff7f47000     0x2000        0x0 [vdso]
      0x7ffff7f47000     0x7ffff7f5c000    0x15000        0x0 /usr/lib/x86_64-linux-musl/libc.so
      0x7ffff7f5c000     0x7ffff7fc3000    0x67000    0x15000 /usr/lib/x86_64-linux-musl/libc.so
      0x7ffff7fc3000     0x7ffff7ffa000    0x37000    0x7c000 /usr/lib/x86_64-linux-musl/libc.so
      0x7ffff7ffa000     0x7ffff7ffb000     0x1000    0xb2000 /usr/lib/x86_64-linux-musl/libc.so
      0x7ffff7ffb000     0x7ffff7ffc000     0x1000    0xb3000 /usr/lib/x86_64-linux-musl/libc.so
```

Okay, so it's getting libc from `/usr/lib/x86_64-linux-musl/libc.so`. 

```
$ md5sum libc.so
0cb0503eb60496782d21cf9b26d61c01  libc.so

$ md5sum /lib/x86_64-linux-musl/libc.so
40dcd7cec2b87e3f65a6b96ec6d383d3  /lib/x86_64-linux-musl/libc.so
```

Uh oh, the libc I got with `apt install musl` is not the same as the libc they gave us. This is probably because I'm on Ubuntu 20.10 and not Ubuntu 21.04. We want to have the *exact same environment* as the remote server, otherwise our exploit may work locally but not remotely. I tried a couple of tricks (LD_PRELOAD, LD_LIBRARY_PATH) to get it to load the libc out of the current directory instead, but I was unsuccessful. Since this is the only thing using musl libc on this system and I'm lazy, I just copied the libc they gave us over the one from apt:

```
cp libc.so /usr/lib/x86_64-linux-musl/libc.so
```

OK great, we can now run the program and are confident we have the correct libc version.

## Part 2. Understand the Challenge

We are greeted with a prompt which gives us a number of options.

```
$ ./mooosl 
1: store
2: query
3: delete
4: exit
option: 
```

Those of us who are not strangers to pwn know this *wreaks* of a heap challenge. (Why? 'store' => `malloc`, 'delete' => `free`, 'query' => print out the contents of an allocation).

I tried a few inputs, and made some observations:

```
$ ./mooosl 
1: store
2: query
3: delete
4: exit
option: 1
key size: 10
key content: ffffff
value size: 60
value content: FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
ok
1: store
2: query
3: delete
4: exit
option: invalid
$ FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF: command not found
```

- It seems to be some kind of key-value store. A hash table? what happens on collisions??
- It asks for size of the key and value, and if you input fewer bytes, it stops on newline
- If you input too may bytes it doesn't read them in (it tried to read my Fs as the next "option:" input instead)

```
$ ./mooosl 
1: store
2: query
3: delete
4: exit
option: 1
key size: 2
key content: f
value size: 10
value content: lololol
ok
1: store
2: query
3: delete
4: exit
option: 2
key size: 2
key content: f
0x7:6c6f6c6f6c6f6c
ok
1: store
2: query
3: delete
4: exit
option: 1
key size: 2
key content: f
value size: 10
value content: yyyyyyy
ok
1: store
2: query
3: delete
4: exit
option: 2
key size: 2
key content: f
0x7:79797979797979
ok
1: store
2: query
3: delete
4: exit
option: 4
bye
```

- It prints my input in hex (0x<SIZE>:<SIZE hex bytes>), size was the # of bytes actually read, not the number I entered
- I stored two things for the same key. When I did query, I got the _second_ one I stored.


That's about all I cared to explore dynamically for the moment -- lets pop it into Ghidra.

## Part 3. Find the bug

Find main. It looks like this:

![main, before labelling](screenshots/s1.png)

The first call prints the menu. The second call (FUN_0010128f) calls some function and then does `atoi` on it (atoi reads a string and returns the decimal integer that was in it), so it's probably reading the option selected by the user.

Ghidra has the wrong function signature for FUN_0010128f; we notice this because the return value of atoi is unused and when main calls this function it uses its return value. Edit the function signature to correct the return type, for more accurate decompilation.

![edit function signature](screenshots/s2.png)

With this knowledge, we know that iVar1 containst the option entered by the user. So we can label the diffrent branches accordingly.

![labelled main](screenshots/s3.png)

Lets dive into `do_store`.

![do_store](screenshots/s4.png)

The first thing store does is calloc 0x30 bytes (calloc is just malloc, but it zeroes the region before you get it) - the pointer goes in `puVar2`. Then, we see three function calls and a bunch of operations relative to puVar2. Whenever we see a bunch of specific array subscripts on a pointer, we can suspect that this is actually a pointer to a structure, not an array of 8-byte values.

We know the structure is 0x30 bytes, and every member to be 8 bytes (there is no wacky math on puVar2, and it's never cast to any other type). For now, we don't know the names of the members. There's a cool Ghidra feature that will auto-generate this structure for you (normally, i've just done it in the 'Data Type Manager' window).

![do_store](screenshots/s5.png)
![do_store](screenshots/s6.png)

Cool, lets try to figure out what each function does now. The first function, once you fix the argument type, looks like this:

![do_store](screenshots/s7.png)

We see that it prompts for a key size, we calloc that size, then we set the value at p2buf to the new chunk we just allocated. Next, this function calls FUN_001011e9. I am omitting this for brevity, but it just `read`s one character at a time from the user into arg1, until either \n is reached or we've written `len` (arg2) characters. It returns the number of chars read. (Note, it does not null-terminate the string, but it won't matter because this value isn't treated anywhere as a string). I'm naming this function `read_until_newline`.

Going back out to `do_store`, we can label that first call as a call to `get_key_from_user`. 

Notice that the argument is just puVar2 -- this is a pointer to the structure, which is also a pointer to the *first member of the structure*, `field_0x0`. So we know that get_key_from_user is going to set `field_0x0` to the pointer it gets from its calloc call... that was where the key was stored! So we can rename `field_0x0` to `key_buf`. 

The return value of `get_key_from_user` is the return value of `read_until_newline` (the number of characters read). So `field_0x10` is the `key_len`.

![do_store](screenshots/s8.png)


The next function that is called is FUN_00101364. We'll notice a very similar pattern here, except we are reading in the value instead of the key. So `field_0x8` is the `value_buf`. And `field_0x18` is the `value_len`. We've filled in over half the struct!

So far, we haven't seen much interesting. Just labelling struct members. That's about to change with `FUNC_001013db`. Here's how it gets called in do_store:

![do_store](screenshots/s9.png)

We need a important observation about how the return value of the mysterious `FUNC_001013db` gets used: It gets stored in field_0x20 and then they mask it with `0xfff`, and use it as an index into a global `DAT_00104040` (an array of pointers!). They pull the old pointer from `&DAT_00104040 + uVar1 * 8`. Then they store the new pointer in that same spot, and set field_0x28 to the old pointer. **This is insertion into the beginning of a singly-linked list**. FUNC_001013db is the *hash function*, whose lower 12 bits are used as an index to select which "bucket" the new node should be added to. Nodes are always inserted at the beginning of the list.

Here's the hash function:

![do_store](screenshots/s10.png)

Those are some cool constants: 2021 and 0x13377331. So we know the first param is the key buffer and the second param is the key length. It iterates over every character in param_1 by incrementing local_14 as an index. For every character it computes:
```
val = (ulong)current_character + val * 0x13377331
```
with val = 0x7e5 (2021) as the starting condition, and it returns val. I played around with this equation a bit, it turns out its a linear diophantine equation and I tried to get SymPy to solve it but I wasn't thrilled with those results.

Luckily, a brute force search over the space of all two-byte keys is very effective at finding collisions (keys whose hash value & 0xfff yields the same thing)

```python
START = 0x7e5
def brute_force_collision(desired_bucket):
    options = []
    for x in range(256):
        for y in range(256):
            cur_num = START
            cur_num = ((x + cur_num * 0x13377331))
            cur_num = ((y + cur_num * 0x13377331))
            if (cur_num & 0xfff) == desired_bucket:
                options.append((x, y))
    return options
```

This will return a 2-tuple for every 2-byte key that hashes to the same hash table bucket.

So far, there's nothing wrong with the fact we might have a hash collision. Some keys will hash to the same thing & 0xfff so those nodes will be inserted into the same bucket. If we check the do_query function, we'll see it actually does a memcmp (in the function at 0x1014fb) on the two keys to make sure it's found the right node before printing it. There's nothing wrong with this aspect of the implementation of chained hashing.

## The bug

Let's take a look at `do_delete`. Remember that `do_store` effectively did a linked list insert at the beginning of the list, so we expect `do_delete` to handle removing from a linked list.

![do_delete](screenshots/s11.png)

I've already labelled one key function without telling you: `get_node_by_key` at 0x1014fb. This function (actually only takes two parameters) does a linked list traversal until it finds the node matching a particular key, and returns a pointer to the node if it finds it. I'll leave that one for you to look at on your own. No issue there.

Let's try to label a variable or two:
- local_18, returned by get_node_by_key... from REing get_node_by_key we know it returns a pointer to a node in the list, depending on the key the user typed. Going to name `node_to_delete`.

![do_delete](screenshots/s12.png)


Let's look closely at what happens when `get_node_by_key` returns non-null (aka it found the node to delete).


It gets a pointer to the list head from the global (line 20), then it checks:
- If the node we are trying to delete is the list head
- OR the node we are trying to delete is NOT the list tail (->next is not null)

If either of these conditions is satisifed, it actually unlinks correctly: The loop finds the pointer to change (the previous node's next pointer, or the pointer to the head of the list) and then changes it to new next node.

But what happens when neither of these conditions are satisfied? That is, the node we are deleting is not the first node, but *is* the last node. We skip the unlinking entirely, but still free the key buffer, value buffer, and the node itself.

This means that if we 'delete' the last node in a list of at least two elements, the previous node *still references the node we just free'd*.

This one bug leads to essentially two vulnerabilities:
- Use-after-free: The node is still in the linked list. We can still use the 'query' function to print out its value.
- Double free: We can still use the 'delete' function to free the same node (and it's key and value buffers) again, since the node is still in the linked list.

## Part 4: Exploiting the UAF / double free (aka how does the musl libc heap work)

TODO
