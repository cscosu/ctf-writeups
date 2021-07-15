# Crypto

I enjoyed the crypto challenges in this CTF—here are write-ups for most of the
challenges.

## baby

**Points**: 102 (827 solves) \
**Author**: EvilMuffinHa

I want to do an RSA!

```
n = 228430203128652625114739053365339856393
e = 65537
c = 126721104148692049427127809839057445790
```

### Solution

We can see that `n` is small so it can easily be factored. We can use
SageMath's `euler_phi` function which will do that for us and compute the
totient.

```python
from Crypto.Util.number import long_to_bytes

n = 228430203128652625114739053365339856393
e = 65537
c = 126721104148692049427127809839057445790

d = inverse_mod(e, euler_phi(n))
print(long_to_bytes(pow(c, d, n)))
```

Flag: `flag{68ab82df34}`

## blecc

**Points**: 119 (146 solves) \
**Author**: AdnanSlef

Blecc! What are all these numbers? This doesn't look like RSA...

```
p = 17459102747413984477
a = 2
b = 3
G = (15579091807671783999, 4313814846862507155)
Q = (8859996588597792495, 2628834476186361781)
```

### Solution

This problem defines the elliptic curve
```
y^2 = x^3 + 2*x + 3  (mod p)
```

We're given two points `G` and `Q` that lie on the curve, and the goal is to find `d` where
```
d * G == Q
```

This can be done like so:

```python
from Crypto.Util.number import long_to_bytes

p = 17459102747413984477
a = 2
b = 3
G = (15579091807671783999, 4313814846862507155)
Q = (8859996588597792495, 2628834476186361781)

E = EllipticCurve(GF(p), [a, b])
G = E(G)
Q = E(Q)
d = G.discrete_log(Q)
print(long_to_bytes(d))
```

Flag: `flag{m1n1_3cc}`

## yahtzee

**Points**: 128 (103 solves) \
**Author**: AdnanSlef

Pseudo-random number generators are weak! I use only true RNGs, like rolling a
set of dice!

```
nc mc.ax 31076
```

Attachments: `yahtzee.py`

### Overview

All we can do is request ciphertexts:
```
============================================================================
=            Welcome to the yahtzee message encryption service.            =
=  We use top-of-the-line TRUE random number generators... dice in a cup!  =
============================================================================
Would you like some samples?

Ciphertext: 1df40e469d07fdfe426677eb46a2acb72bd3ad25b6626546123b019b9c9ee593f01fdc7b7f1fae7456bd06c4ab85984a35c9668c4e6116a731a70ada48fdd86c4035646946aba4a410129f8eb5fc4b18e899b5e09c7f367ce28512f1007c736dffddf92a4ab4ac4c161752ee53
Would you like some more samples, or are you ready to 'quit'?

Ciphertext: 2a133a7e50c7bdfc383a3fc025f2c8ad549255f24d3e9780346d57c62b0124b69a4add8d066dbfc384b78d2e9636f0bca4de0ed0aeaee714aa69622d8b2e805623ed4096695f63be1c0569a52b85bd9eca084612b23f08eba11abcc03ca1bc4d9ccfcd940d30c26d7d964aec9456181d
Would you like some more samples, or are you ready to 'quit'?

Ciphertext: 2a133a7e50c7bdfc383a3fc025f2c8ad549254fb582d85de3b12779a7b015bbb9d5a8fc9145ca5acb2f7c3298b6be5b1b0930cc6fabbae0da2277120983cd5436ceb1493675a72be1a1069ba318bb3c483034f00f52518f49123ec943a98bd49d9ce8a953d35e812219e1ef2d1450a4e
Would you like some more samples, or are you ready to 'quit'?

...
```

Each ciphertext is a randomly chosen famous quote (there are 25 total)
encrypted with AES CTR mode. However, the nonce is chosen as the sum of two
die, so its values are between 2 and 12. The flag is embedded in a random
position in each quote.

### Solution

I started by collecting a bunch of ciphertexts, and I ended up with 4037 unique
ciphertexts out of about 16384 total.

```python
>>> len(cts_set)
4037
```

Next I checked how many different lengths of ciphertexts I had:
```python
>>> lens = set(len(ct) for ct in cts_set)
>>> lens
{89, 90, 91, 92, 93, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 108, 109, 112, 113, 114, 115, 116, 118}

>>> len(lens)
25
```

The ciphertexts had 25 different lengths, meaning every quote had a different
length. Next I focused on only ciphertexts with length `118` (chosen
arbitrarily).

```python
>>> cts = [ct for ct in cts_set if len(ct) == 118]
>>> len(cts)
198
```

We have 198 ciphertexts with length 188. Next I picked the first ciphertext and
XOR'd all other ciphertexts with it.

```python
>>> a = cts[0]
>>> for b in enumerate(cts):
...     print(pwn.xor(a, b))
```

```python
...
b'\xf90\x8e\x8cbQ6\x91\x99NU\xd5\xc2\xfb\xf5\xb6\x05\x90:\xf3\x19\xf0}v\xa6\x8b\x82\xc2\x9fV\xaa\xf4\x14\xf3\xd6\x1a\xc2\xfa\x8c\x81\xca6F\x86\xd9*\xb7P\xbe\x8b\xda6I\x06<\xaf\x98S\xf8\r\x86\t\xcf\xd0%x\xe5\xd3\rNg\xfc\xb7m\x0f\xf6oT\x07\x00\x8dH\x82(r1\xc4\n\x0c\x82N/\x843|\x10\x19\xc0\xe6\xccl\xd9]\xe6/DX\xb0\xa8\xfb\x926\x1a\x8a#\xd0\xc5\x97'
b'vB\x13\xe6f\xdc\xe0\xf8/\x14\xc0\xfe\xae\xaf\xbb\xf7\xe38\xe2\xdf\xba.\xb8\xe5\x8a\x890\x9a\x88nQ\xaf\xb4\xb0|3\x86\x98\x1b\xbf\x021[\xa7\x9e\x102\xe93\xca\xb8\xf2?\x12UQ\xf9!\x1f\xf9\xb6\xcdU9\n"{\xf9\xca\xd3~\xe1\xd9\xfe\xec\xe9\xd0\xb4\x7f_\xab(\xc2\xd2G:9\xbby\xda,\xdf\xde\x16?\xd3++ \xcb\x96\xf3d\xe8\x87\xdbI\xa590\xb4x|\xdbRL\xab\xbb'
b'\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x12\x04\x04G\x0bU\x1a,8Z\x11\x037\x1bH\x0c\x01\x13\x153\x0f($\x03\x06+%\x04A\r"T\x1c\r\x17\x13\x03:\x1c<0]N\x03\x1a_P\x10\x0e\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00'
b'\x8e\xead\xbd\x00\x18o\xca\x0f\x8b\xc3\xce\xfe\xed\xee\xee\x83\xb1\xb4\x03\x06\xe4\xbd.Q4\xc73V\xa1\xc1\rp3<\xb1y\xd3\xe3:\x91=\xe6XU3\xb4g\xf6\xe2\xd0\xbf\x07\x16\x94Y\x06V%*e\x9d\x82\x9b\xf0\xeaQj6j\x84A\xeb\xbe\xb7\xfa\x9d\x8f\x16MI\xd5Cw\x83\nXC\x1by\x9f\n\x05Y)\xb2\xa1\xa3\x9f@q\x13\xd9#,T\xeam\x7f\xe5\x85\xe2\xafH3K\xd1\x06'
b"\xe5r\xe8\xd7i\xb9^MIkY.\xb0#y\xeeD\xd5L\x04]\xe55\t=\xd1\xf81\xd2\xbe\xbaq\x01\xc9\x96>\x95\xad\xa6k\xf7\x06\xacr\x92=\x9dh\xb0v\x0c\x88\xb1*\xeb{'\xf9\x04h\x8cH`|J'\x1a\xea\x84\xc2tQ\xf3\xc5\xdcP\x959\x15\xf1\xe6\xfd\xa2\x85\xe1q\xcd\xa9\xdb\xcc\xcb\x19\rTo\x12R\x93;\t\x9f`\xfd~\xe8!)\xec\xe8urkB}\xea\x06\xa5\xf5"
...
```

You might notice that one of the lines above as a lot of `\x00` bytes, which is
because they were encrypted with the same nonce.

The junk in the middle of the string is due to the flag being in different positions:

```
0000000000000xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx000000000000000000000000000000
It is better flag{this_is_a_fake_flag}to be feared than loved, if you cannot be both.
It is better to be feared thanflag{this_is_a_fake_flag} loved, if you cannot be both.
```

We know `flag{` is at the start of the junk, so let's trying XOR'ing it:

```python
>>> def first_nonzero_byte(c):
...     i = 0
...     while i < len(c):
...         if c[i] != 0:
...             return i
...         i += 1
...     else:
...         return -1
>>> s = b'\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x0
... 0\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x12\x04\x04G\x0bU\x1a,8Z\x11\x037\x1bH\x0c\x01\x13\x153\x0f($\x03\x06+%\x04A\r"T\x1c\r\x17\x13\x03:\x1c<0]N\x03\x1a_P\x10\x0e\x
... 00\x00\x00\x00\x00\x00\x00\x00\x00\x00'
>>> i = first_nonzero_byte(s)
>>> pwn.xor(s[i:], b"flag{")
b'the p3vM_!woV|3jmrrHiDEd}MIe&vD8}jluo[{GV1/da9<qi{flag{flag'
```

We managed to get a little bit of readable text: `the p`. To recover more parts of the quote, we can do this a few more times:

``` python
>>> def is_same_nonce(a, b):
...     x = pwn.xor(a, b)
...     r = x.count(b"\x00") / len(x)
...     return r > 0.25
...
>>> def crib_xor(c):
...     i = first_nonzero_byte(c)
...     return pwn.xor(c[i:], b"flag{"), i
...
>>> for b in cts:
...     if is_same_nonce(a, b):
...         c = pwn.xor(a, b)
...         x, i = crib_xor(c)
...         s = b"?" * i + x
...         print(s)
```

We get something like this:

```
b"?????????????????????????????????????????????????inter$qNDo#p[3cfl!{J(TV;5{mqqnz+s9g\\I'#\x7fM8}jluo[{GV1/da9<qi{flag{flag"
b'??????????????????????????????be do8a\x1eC\'8mRw3mq&4MfW[&ggn%7vs)#r>pp`l{bla2~qlidn!~?{AC*%cP2plpheV}[K;"b}$6|og{flag{fla'
b'???????????????????????????????????????????????????????????????perso8$IX wqM3uo\x7f5o\x14`|i`$fA%\x7fgi\x7fb]gZ\\<)x|31wuflag{flag{'
b'???????????????says ?p\x1eS.9vQg3a{rpKfF\x1e\'}}k=s"u#f&k{8ma)p}{)`z)#r>pp`l{bla2~qlidn!~?{AC*%cP2plpheV}[K;"b}$6|og{flag{fla'
b'????????????????????it ca8jQDo5}\x1ew|m{rgLgVR05|q%7ku8ma)p}{)`z)#r>pp`l{bla2~qlidn!~?{AC*%cP2plpheV}[K;"b}$6|og{flag{fla'
b'?????????????????????????????????????????????????????????????????????????????doingvbRQ(,(VLD7/&KP`FLgfMp\x1eH1u8w8bqvag{f'
b'??????????????????????????????????????????????????????????????????????who i%$X\\.0c\x0e{LT*c`{|K[&&aA?X]("b}$6|og{flag{fla'
b'???????????????????????canno"$\\Uo3wPv3pv=aHl\x03P;a2w?cgi>wva(w}"9s)w{zmleg{3ivgsey&u%zVD!?bG5{vq\x7fb]gZ\\<)x|31wuflag{flag{'
b"??????????????????????????????????????shoul2$P_;wqPgvql'dP(WV15b{#dmuleg{3ivgsey&u%zVD!?bG5{vq\x7fb]gZ\\<)x|31wuflag{flag{"
b'?????????????????????????????????????????????????????????????????????????????doingvmJ\x1eo1t_th3v\rC\x109Wa }wlbd]u\x03Z;||yq~v5'
b'?????????????????????????????????done %lQE#38P|g#w<`AzQK$a2j9r"k)w{zmleg{3ivgsey&u%zVD!?bG5{vq\x7fb]gZ\\<)x|31wuflag{flag{'
b'???????????????????????????????????????????????????????????the p3vM_!woV|3jmrrHiDEd}MIe&vD8}jluo[{GV1/da9<qi{flag{flag'
b'?????????????????????????????????????????????not i8p[B="hJ3gk{rdAzPQ:5ev>7khlidn!~?{AC*%cP2plpheV}[K;"b}$6|og{flag{fla'
b'??????????????????????????????????????????????????????????????????????????is fl7cE\x00\'\x08O\n"g\\j:qV;Pa:ZM-?cp+<qi{flag{flag'
```

Using just these characters and a little bit of Goolging we can see that the
quote is `The person who says it cannot be done should not interrupt the person doing it`.

Now we can recover the flag:

```python
>>> A = b"The person who says it cannot be done should not interrupt the person doing it"
>>> for b in cts:
...     if is_same_nonce(a, b):
...         c = pwn.xor(a, b)
...         print(pwn.xor(c, A))
b'The person who says it cannot be done should not interrupt the person doing itThe person who says it cannot be done sh'
b'The person who says it cannot be done should not flag{0h_W41t_ther3s_n\\X5 z!ybAt"2.yHV)*$\\<s-drzI<UD}-bt1?d.be done sh'
b'The person who says it cannot flag{0h_W41t_ther3s_nO_3ntr0py} be done `oi;b7i|W}"2.yHV)*$\\<s-drzI<UD}-bt1?d.be done sh'
b'The person who says it cannot be done should not interrupt the flag{0hLP2\x7fz\x0c=z]{1(\x1fcb{h1 Z,w<|rzI<UD}-bt1?d.be done sh'
b'The person who flag{0h_W41t_ther3s_nO_3ntr0py} says it cannot be done `oi;b7i|W}"2.yHV)*$\\<s-drzI<UD}-bt1?d.be done sh'
b'The person who says flag{0h_W41t_ther3s_nO_3ntr0py} it cannot be done `oi;b7i|W}"2.yHV)*$\\<s-drzI<UD}-bt1?d.be done sh'
b'The person who says it cannot be done should not interrupt the person doing ivW`l<`kAE<$d@CPq0&UX&CY ~Jr\x11@>36s\x7f}xte sh'
b"The person who says it cannot be done should not interrupt the person ukg)uc!Mo=3/\x1fyEA)l'wrH\x1a2<~^~VRn-bt1?d.be done sh"
b'The person who says it flag{0h_W41t_ther3s_nO_3ntr0py} cannot be done `oi;b7i|W}"2.yHV)*$\\<s-drzI<UD}-bt1?d.be done sh'
b'The person who says it cannot be done flag{0h_W41t_ther3s_nO_3ntr0py} `oi;b7i|W}"2.yHV)*$\\<s-drzI<UD}-bt1?d.be done sh'
b'The person who says it cannot be done should not interrupt the person doing ivW`l<`dY\n{98I{|ui\r]\x18\x7fRtgepnmlR3\r^|cu{u9~;'
b'The person who says it cannot be flag{0h_W41t_ther3s_nO_3ntr0py} done `oi;b7i|W}"2.yHV)*$\\<s-drzI<UD}-bt1?d.be done sh'
b'The person who says it cannot be done should not interrupt flag{0h_W41gXr&k!zaggM\x04scYVk/-U<s-drzI<UD}-bt1?d.be done sh'
b'The person who says it cannot be done should flag{0h_W41t_ther3s_nO_3ngu6>w.i|W}"2.yHV)*$\\<s-drzI<UD}-bt1?d.be done sh'
b'The person who says it cannot be done should not interrupt the person doinh?(uC9j\x04\x179\x1cP\x04+<Mn46^<Es}H_a=ee#?d.be done sh'
```

Flag: `flag{0h_W41t_ther3s_nO_3ntr0py}`

## scrambled-elgs

**Points**: 143 (70 solves) \
**Author**: AdnanSlef

My elgs have been scrambled! I hope that makes them more secure...

```python
#!/usr/bin/env sage
import secrets
import json
from Crypto.Util.number import bytes_to_long, long_to_bytes
from sage.combinat import permutation

n = 25_000
Sn = SymmetricGroup(n)


def pad(M):
    padding = long_to_bytes(secrets.randbelow(factorial(n)))
    padded = padding[: -len(M)] + M
    return bytes_to_long(padded)


# Prepare the flag

with open("flag.txt", "r") as flag:
    M = flag.read().strip().encode()

m = Sn(permutation.from_rank(n, pad(M)))

# Scramble the elgs
g = Sn.random_element()
a = secrets.randbelow(int(g.order()))
h = g ^ a
pub = (g, h)

# Encrypt using scrambled elgs
g, h = pub
k = secrets.randbelow(n)
t1 = g ^ k
t2 = m * h ^ k
ct = (t1, t2)

# Provide public key and ciphertext
with open("output.json", "w") as f:
    json.dump({"g": str(g), "h": str(h), "t1": str(t1), "t2": str(t2)}, f)
```

Attachments: `output.json`

### Overview

This is El Gamal encryption using the
[Symmetric Group](https://en.wikipedia.org/wiki/Symmetric_group).

In short, each element of a symmetric group encodes a permutation of the
numbers from `1` to `n`. You can use function composition of two permutations
to obtain another permutation - this is defined as multiplication.

### Solution

The value `k` is between 1 and 25000, which can be bruteforced.

```sage
#!/usr/bin/env sage
import json
from Crypto.Util.number import long_to_bytes
from sage.combinat import permutation

n = int(25000)
Sn = SymmetricGroup(n)

with open("orig.json") as f:
    output = json.load(f)

g = Sn(output["g"])
h = Sn(output["h"])
t1 = Sn(output["t1"])
t2 = Sn(output["t2"])

for k in range(n):
    if t1 == g ^ k:
        s = h ^ k
        m = t2 * s.inverse()
        pt = long_to_bytes(Permutation(m).rank())
        print(pt)
        break
    print(".", end="", flush=True)
print()
```

Flag: `flag{1_w1ll_n0t_34t_th3m_s4m_1_4m}`

## Keeper of the Flag

**Points**: 174 (42 solves) \
**Author**: tpa

can you convince keeper of the flag to give you flag?

```
nc mc.ax 31538
```

Attachments: `kotf.py`

### Overview

Running the program we get this:

```
p = 119381252141434529399113269618537518206454494819367461369242599973041597387921220969483252653247976730028350723793549625130273183509150811188027451637912792875231236602996729080009715138520773905543562114005627515043275171799523906695722815352981457447421784094426169686948213794384647316587526093691513841281
q = 1369745245683727534448543568971509700336395050779
g = 107452118431160869736993018061835061177694411626265745275477766233663800557369551421010380933116321020405546287383245773546454851974473573782444080574242106454721595646546494381359224716083274717708795877121255971672594808032074422931216643349307590961174454811365589735346255219590445366163979560443070247793
y = 108318518778890062621615420589241357367369077471794479344099251965830976224101469526450107758235935258076296906653871079733036601800234349903087376356200235322096082240423666504818486360170757432965268627613240976875735388340925867550136431581364578819426384718381966235330128051070605647029960093681055278742
what would you like me to sign? in hex, please
00
H(m) = 461765542000148736210520199810417503543616410629
r = 884121412451688684697635258836038910326399229058
s = 905081460104866723889166621875171396507092089945
what would you like me to sign? in hex, please
01
H(m) = 354857952909939164482365250177189196318647056686
r = 563096559376404136663283452203432007640041964755
s = 356916840119534169973895737632184418942272972648
ok im done for now
you visit the flag keeper...
for flag, you must bring me signed message:
'give flag':122233989766006461487114950198068517224823012488
00
00
sorry
```

Basically we can get DSA signatures of any two messages. The goal is forge a
signature of `give flag`.

### Solution

> Note: I used
> [this write-up](http://blog.redrocket.club/2018/03/26/VolgaCTF-Nonsense/),
> which referenced a similar challenge.

We have 3 equations and 3 unknowns (`k1`, `k2`, `x`)

```
(s1 * k1) - (r1 * x) === H(m1)  (mod q)
(s2 * k2) - (r2 * x) === H(m2)  (mod q)
k1 - k2 === H(m1) - H(m2) - 1   (mod q)
```

The third equation was derived from:

```
k1 === H(m1) + pad  (mod q)
k2 === H(m2) + pad + 1  (mod q)
k1 - k2 === H(m1) - H(m2) - 1   (mod q)
```

We can solve this linear system of equations with SageMath to obtain `k1`,
`k2`, and `x`. Then we use `x` to forge a signature of `give flag`.

Final script:

```python
import Crypto.Util.number as cun
import subprocess
import os

os.environ["PWNLIB_NOTERM"] = "true"
import pwn

if pwn.args.REMOTE:
    io = pwn.remote("mc.ax", 31538)
    cmd = io.recvlineS().strip().lstrip("proof of work: ")
    out = subprocess.check_output(cmd, shell=True).strip()
    io.sendlineafter("solution: ", out)
else:
    io = pwn.process("python3 kotf.py", shell=True)

p = int(io.recvlineS().strip())
q = int(io.recvlineS().strip())
g = int(io.recvlineS().strip())

y = int(io.recvlineS().strip())


def get_signature(msg: bytes):
    io.sendlineafter("what would you like me to sign? in hex, please\n", msg.hex())
    Hm = int(io.recvlineS().strip())
    r = int(io.recvlineS().strip())
    s = int(io.recvlineS().strip())
    return Hm, r, s


Hm1, r1, s1 = get_signature(b"\x00")
Hm2, r2, s2 = get_signature(b"\x01")

M = MatrixSpace(GF(q), 3, 3)
V = VectorSpace(GF(q), 3)

A = M([s1, 0, -r1, 0, s2, -r2, 1, -1, 0])
Y = V([Hm1, Hm2, Hm1 - Hm2 - 1])
X = A \ Y

k1, k2, x = X


def sign(msg: bytes):
    m = cun.bytes_to_long(msg)
    k = randint(1, q)
    r = pow(g, k, p) % q
    s = (pow(k, -1, q) * (H_give_flag + x * r)) % q
    return (r, s)


io.recvuntil("'give flag':")
H_give_flag = int(io.recvlineS().strip())

r, s = sign(b"give flag")
io.sendline(str(r))
io.sendline(str(s))
io.interactive()
```

## quaternion-revenge

**Points**: 205 (29 solves) \
**Author**: AdnanSlef

Those sure are some quirky quaternions. See if you can identify some surprising
behavior. Note - Please test your solution locally and don't DoS the box
:lemon:

```
nc mc.ax 31868
```

Attachments: `quaternion_revenge.sage`

### Overview

```python
p = getPrime(512)
q = getPrime(512)
n = p * q
e = 65537
Q.<i,j,k> = QuaternionAlgebra(-p, -q)

...

print("Calculate the left quaternion isomorphism of m:")
inp = input(">>> ").strip()
assert all([x in "1234567890 ijk*+" for x in inp])
if eval(inp) == m:
    print("win")
    print(flag)
else:
    print("Wrong!")
```

### Solution

There's a bug in SageMath with `QuaternionAlgebra` so that
```python
>>> eval("i") == m
True
```

Flag: `flag{00p5_1_l13d_r0fl}`

## retrosign

Wait, I'm not sure that's what signature-based intrusion detection means...

```
nc mc.ax 31079
```

Attachments: `retrosign.py`

### Overview

```python
p = getPrime(512)
q = getPrime(512)
n = p * q
k = randbelow(n)

...

def execute(cmd):
    if cmd == "sice_deets":
        print(flag)
    elif cmd == "bad_signature":
        print("INTRUSION DETECTED!")
    else:
        print("Command unknown.")


def authorize_command(cmd, sig):
    assert len(sig) == 128 * 2
    a = bytes_to_long(sig[:128])
    b = bytes_to_long(sig[128:])
    if (a ** 2 + k * b ** 2) % n == bytes_to_long(sha256(cmd)):
        execute(cmd.decode())
    else:
        execute("bad_signature")
```

The goal is to find `a` and `b` so that
```
(a ** 2) + k * (b ** 2) === 57017600678424052973112218428169268962602893691613160657481137428089607732073  (mod n)
```

### Solution

Some Googling finds this
[paper](https://www.researchgate.net/publication/262234058_An_efficient_solution_of_the_congruence)
from 1985. From there I learned that this is called the Ong-Schnorr-Shamir
signature scheme. Some more Googling takes me to a similar challenge, which conveniently has many publicly available
[write-ups](https://github.com/perfectblue/ctf-writeups/tree/master/2020/twctf-2020/circular).

I just copied their script and to get the flag:
`flag{w0w_th4t_s1gn4tur3_w4s_pr3tty_r3tr0}`
