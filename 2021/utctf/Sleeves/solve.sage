from Crypto.Cipher import AES
from Crypto.Hash import SHA256

p = 115792089210356248762697446949407573530086143415290314195533631308867097853951
b = 0x5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B

E = EllipticCurve(GF(p), [-3, b])
P = E.lift_x(
    110498562485703529190272711232043142138878635567672718436939544261168672750412
)
Q = E.lift_x(
    67399507399944999831532913043433949950487143475898523797536613673733894036166
)

d = Q.discrete_log(P)


def do_next(s):
    # Given state `s`, return pseudorandom value `r` and the new state `s_new`
    sP = s * P
    r = Integer(sP[0])
    s_new = Integer((r * P)[0])

    rQ = r * Q
    return Integer(rQ[0]), s_new


def do_guess(r1):
    # Check if `r1` is a valid x coordinate on the curve
    try:
        rQ1 = E.lift_x(r1)
    except ValueError:
        return None

    sP2 = d * rQ1
    s2 = Integer(sP2[0])
    r2, s3 = do_next(s2)
    return r2, s3


def decrypt(r):
    ct = bytes.fromhex(
        "c2c59febe8339aa2eee1c6eddb73ba0824bfe16d410ba6a2428f2f6a38123701"
    )
    aes_key = SHA256.new(str(r).encode("ascii")).digest()
    cipher = AES.new(aes_key, AES.MODE_ECB)
    pt = cipher.decrypt(ct)
    print(pt)


r1 = 135654478787724889653092564298229854384328195777613605080225945400441433200
r2 = 16908147529568697799168358355733986815530684189117573092268395732595358248

for i in range(2 ** 8):
    r1_guess = (r1 << 8) + i
    guess = do_guess(r1_guess)

    if guess:
        r2_guess, s3 = guess
        if r2_guess >> 8 == r2:
            r3, s4 = do_next(s3)
            decrypt(r3 >> 8)
            break
