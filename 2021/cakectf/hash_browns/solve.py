import qiling
import hashlib

base = 0x555555554000
i = 0
flag = list(
    b"CakeCTF{?????????????????????????????????????????????????????????????????}"
)

md5s = {hashlib.md5(bytes([i])).digest()[:5].hex(): i for i in range(255)}
sha256s = {hashlib.sha256(bytes([i])).digest()[:5].hex(): i for i in range(255)}


def f(ql):
    global i
    i = ql.reg.rdi


def md5_strcmp(ql):
    global flag
    s1 = ql.mem.string(ql.reg.rdi)
    flag[i * 2] = md5s[s1]


def sha256_strcmp(ql):
    global flag
    s1 = ql.mem.string(ql.reg.rdi)
    flag[i * 2 + 1] = sha256s[s1]


def post_strcmp(ql):
    ql.reg.eax = 0


inp = "CakeCTF{aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa}"
ql = qiling.Qiling(
    [
        "./hash_browns",
        inp,
    ],
    "/",
    verbose=qiling.const.QL_VERBOSE.OFF,
)

ql.hook_address(f, base + 0x1586)

ql.hook_address(md5_strcmp, base + 0x16D8)
ql.hook_address(post_strcmp, base + 0x16DD)

ql.hook_address(sha256_strcmp, base + 0x1722)
ql.hook_address(post_strcmp, base + 0x1727)

ql.run()
print(bytes(flag))
