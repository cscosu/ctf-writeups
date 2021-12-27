.intel_syntax noprefix
.global _start
.type _start, @function
_start:

cool:
movq rsi, 0xfaceb00b
jmp start2

start2:

# big-ass loop so we can attach gdb 
mov rdi, 1000
loop:
decq rdi
jne loop

movabs r12, 0x0000001002d9d2f0
mov byte ptr [r12+0], 0x48
mov byte ptr [r12+1], 0xbf
mov byte ptr [r12+2], 0x2f
mov byte ptr [r12+3], 0x62
mov byte ptr [r12+4], 0x69
mov byte ptr [r12+5], 0x6e
mov byte ptr [r12+6], 0x2f
mov byte ptr [r12+7], 0x73
mov byte ptr [r12+8], 0x68
mov byte ptr [r12+9], 0x0
mov byte ptr [r12+10], 0x57
mov byte ptr [r12+11], 0x48
mov byte ptr [r12+12], 0x89
mov byte ptr [r12+13], 0xe7
mov byte ptr [r12+14], 0x48
mov byte ptr [r12+15], 0xc7
mov byte ptr [r12+16], 0xc6
mov byte ptr [r12+17], 0x0
mov byte ptr [r12+18], 0x0
mov byte ptr [r12+19], 0x0
mov byte ptr [r12+20], 0x0
mov byte ptr [r12+21], 0x48
mov byte ptr [r12+22], 0xc7
mov byte ptr [r12+23], 0xc2
mov byte ptr [r12+24], 0x0
mov byte ptr [r12+25], 0x0
mov byte ptr [r12+26], 0x0
mov byte ptr [r12+27], 0x0
mov byte ptr [r12+28], 0xb8
mov byte ptr [r12+29], 0x3b
mov byte ptr [r12+30], 0x0
mov byte ptr [r12+31], 0x0
mov byte ptr [r12+32], 0x0
mov byte ptr [r12+33], 0xf
mov byte ptr [r12+34], 0x5

jmp cool

ret

str:
.string "Hello world!\n"
