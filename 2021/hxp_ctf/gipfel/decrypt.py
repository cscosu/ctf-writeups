from Crypto.Hash import SHA256
from Crypto.Cipher import AES
from tqdm import tqdm


def enc(a):
    # If you give this something that isn't a str or int, it returns the same
    # thing back
    f = {str: str.encode, int: int.__str__}.get(type(a))
    return enc(f(a)) if f else a


def H(*args):
    data = b"\0".join(map(enc, args))
    return SHA256.new(data).digest()


flag = bytes.fromhex(
    "8cc14560e62654903a42eb6b9d95d24ea7bb2a63a394cabfedbd61e2450b9555164fcf30c1f0f8ba"
)

for password in tqdm(range(10 ** 6)):
    g = int(H(password).hex(), 16)

    key = H(password, 1)
    aes = AES.new(key, AES.MODE_CTR, nonce=b"")
    pt = aes.decrypt(flag)
    if pt.startswith(b"hxp{"):
        tqdm.write(pt.decode())
        break
