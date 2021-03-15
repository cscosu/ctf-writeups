from Crypto.Cipher import AES
from Crypto.Hash import SHA256

"""
This is a Dual_EC_DRBG backdoor solver.
https://en.wikipedia.org/wiki/Dual_EC_DRBG
"""

# This elliptical curve is NIST P-256
p = 115792089210356248762697446949407573530086143415290314195533631308867097853951
b = 0x5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B
E = EllipticCurve(GF(p), [-3, b])

# These are the generator points for the PRNG.
P = E.lift_x(
    110498562485703529190272711232043142138878635567672718436939544261168672750412
)
Q = E.lift_x(
    67399507399944999831532913043433949950487143475898523797536613673733894036166
)

# Surprisingly this works and returns 173. I guess the backdoor is pretty weak.
# This value allows us to completely break the PRNG (i.e. we can accurately
# predict returned values and states).
d = Q.discrete_log(P)


def do_next(s):
    """
    This is essentially the RNG.next() function.
    Given state `s`, return pseudorandom value `r` and the new state `s_new`.
    """
    sP = s * P
    r = Integer(sP[0])
    s_new = Integer((r * P)[0])
    rQ = r * Q
    return Integer(rQ[0]), s_new


def do_guess(r1):
    """
    Given a guess for a value `r1` return from the PRNG, determine the next
    random value as well as the state after that.
    """

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
    """
    Decrypt the ciphertext from the challenge.
    """
    ct = bytes.fromhex(
        "c2c59febe8339aa2eee1c6eddb73ba0824bfe16d410ba6a2428f2f6a38123701"
    )
    aes_key = SHA256.new(str(r).encode("ascii")).digest()
    cipher = AES.new(aes_key, AES.MODE_ECB)
    pt = cipher.decrypt(ct)
    print(pt)


# These are the random values returned from the PRNG.
r1 = 135654478787724889653092564298229854384328195777613605080225945400441433200
r2 = 16908147529568697799168358355733986815530684189117573092268395732595358248

# Bruteforce the lower 8 bits until we guess the full value of `r1`. If our
# guess is correct, the predicted value will match r2.
for i in range(2 ** 8):
    r1_guess = (r1 << 8) + i
    guess = do_guess(r1_guess)

    if guess:
        r2_guess, s3 = guess
        if r2_guess >> 8 == r2:
            r3, s4 = do_next(s3)
            decrypt(r3 >> 8)
            break
