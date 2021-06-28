# This patches vmips to print register state at a static address
from ELFPatch import *

f = ELFPatch("./vmips")

new_patch = f.new_patch(virtual_address=0x40f2c0, size=0x200, append_original_instructions=True, append_jump_back=True)

new_patch.update_patch(f.assembler.assemble("""
start:
nop
push rdi
push rcx
push rsi
push rax

mov rdi, QWORD PTR [rbx+0x10]
mov rcx, rdi
mov ecx, DWORD PTR [rcx+0x158]
cmp ecx, 0xa00fefe0
jne end

mov rsi, 0x545cc8
mov rsi, QWORD PTR [rsi]
call 0x0404600 
end:

pop rax
pop rsi
pop rcx
pop rdi
nop
""", offset=new_patch.chunk.virtual_address))
print("New patch at %s" % (hex(new_patch.chunk.virtual_address)))
f.write_file("./vmips_patched")
