# Hash browns

**Category**: misc \
**Points**: 149 points (40 solves) \
**Author**: yoshiking

Would you mind making the finest hash browns, chef?

Attachments: `hash_browns.tar.gz`

## Overview

We're given a single binary:
```
$ ./hash_browns
Usage: ./hash_browns <flag>

$ ./hash_browns CakeCTF{help}
Too sweet :(
```

Opening it up in Ghidra, we get something like this:

```c
len = strlen(argv[1]);
half_len = (int)(len >> 1);

if (half_len == 0x25) {
  i = 0;
  while (i < half_len) {
    f(i, half_len, &output, useless);
    if (output < 0) {
      output = half_len + output;
    }

    md5(&argv[1][i * 2], md5_hash, md5_hash);
    sha256(&argv[1][i * 2 + 1], sha256_hash, sha256_hash);

    // To hex string
    for (int j = 0; j < 5; j++)
      sprintf(md5_str + j * 2, "%02x", md5_hash[j]);
      sprintf(sha256_str + j * 2, "%02x", sha256_hash[j]);
      j = j + 1;
    }

    if (strcmp(expected_md5s + i * 0xb, md5_str) != 0) {
      puts("Too spicy :(");
      return 0;
    }

    if (strcmp(expected_sha256s + output * 0xb, sha256_str) != 0) {
      puts("Too spicy :(");
      return 0;
    }

    i = i + 1;
  }
  puts("Yum! Yum! Yummy!!!! :)\nThe flag is one of the best ingredients.");
}
else {
  puts("Too sweet :(");
}
```

Basically what it does is:
- Compute the `MD5` and `SHA256` of characters one-by-one.
- Compare them with hardcoded strings (the index of these hardcoded strings is
  scrambled by the `f()` function)

## Solution

Since it hashes the characters one by one, they can be bruteforced. To solve
the challenge, I used [Qiling](https://github.com/qilingframework/qiling) to
emulate the binary and hook addresses to grab the hashes.

Then I looked-up which character contained that hash and overwrote the
`strcmp()` result to 0 so that the program would continue.

Solution:
```python
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
ql = qiling.Qiling(["./hash_browns", inp], "/", verbose=qiling.const.QL_VERBOSE.OFF)

ql.hook_address(f, base + 0x1586)

ql.hook_address(md5_strcmp, base + 0x16D8)
ql.hook_address(post_strcmp, base + 0x16DD)

ql.hook_address(sha256_strcmp, base + 0x1722)
ql.hook_address(post_strcmp, base + 0x1727)

ql.run()
print(bytes(flag))
```

Output:
```
$ python3 solve.py
Yum! Yum! Yummy!!!! :)
The flag is one of the best ingredients.
b'CakeCTF{(^o^)==(-p-)~~(=_=)~~~POTATOOOO~~~(^@^)++(-_-)**(^o-)_486512778b4}'
```
