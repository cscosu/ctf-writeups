import pwn

pwn.context.log_level = "debug"

TICKET = b"ticket{charlie751363sierra3:GN3V4dzRfb4yZtGnJREYUff56lp_3EokEIsP4cgdFVI0pM-9DObLzmVURI9exskplg}"


def send(msg: bytes) -> bytes:
    io.sendlineafter("Msg: ", msg.hex())
    m = io.recvlineS().strip()
    try:
        return bytes.fromhex(m)
    except ValueError:
        raise ValueError(m)


def indices(needles: bytes, haystack: bytes):
    return [haystack.find(needle) for needle in needles]


def decrypt(s: bytes, length: int):
    # str_a: known plaintext
    # str_a_c: known ciphertext
    # inds: indices to XOR in ciphertext
    inds, str_a, str_a_c = store[length]
    ans = bytearray()
    for j, ind in enumerate(inds):
        p = s[ind] ^ str_a_c[ind] ^ str_a[j]
        ans.append(p)
    return ans


def check_partial_encrypt(pt: bytes):
    # Check that it encrypts correctly on the specific indices
    pt_c = send(pt)
    inds, _, _ = store[len(pt)]
    return all(pt_c[ind] == ct[ind] for ind in inds)


io = pwn.remote("black_hole.satellitesabove.me", 5300)
io.sendlineafter(b"Ticket please:\n", TICKET)

io.recvuntil(b"Encoded msg is: ")
ct = bytes.fromhex(io.recvlineS().strip())

"""
Basically the approach is:
- Send two plaintexts
- Notice that the XOR'd ciphertexts are similar to the XOR'd plaintexts, but it's shuffled
- The indices of the shuffle are only dependent on the length of the plaintext

- To decrypt a message of a given length, we need:
    - A plaintext of the same length with a known ciphertext
    - The indices of the shuffle for that length

- We don't know how long the desired plaintext is, so we just keep sending
  longer and longer plaintexts until we get the flag
"""

# Contains data to decrypt plaintext of some given length
store = {}

# The string we get once the two plaintexts are XOR'd. We need this string to
# not contain duplicates so we can figure out the indices of the shuffle.
xor_string = list(range(1, 256))

# One of the plaintext strings. Doing it this way ensures we don't send any
# null bytes
pool = bytes((x + 1) % 256 for x in xor_string)

str_a = bytearray()  # The 1st plaintext string
str_b = bytearray()  # The 2nd plaintext string

# We can only send 255 bytes max
i = 0
while i < 255:
    a = pool[i]
    b = xor_string[i] ^ a

    str_a.append(a)
    str_b.append(b)

    print(f"i = {i}")

    if i < 120:
        # After running for a few iterations, we can be reasonably confident
        # that the desired message is longer than 120 bytes.
        i += 1
        continue

    try:
        str_a_c = send(str_a)
        str_b_c = send(str_b)

        str_ab = pwn.xor(str_a, str_b)
        str_ab_c = pwn.xor(str_a_c, str_b_c)

        inds = indices(str_ab, str_ab_c)

        store[len(str_a)] = (inds, str_a, str_a_c)

        assert decrypt(str_a_c, len(str_a)) == str_a
        assert decrypt(str_b_c, len(str_b)) == str_b

        pt = decrypt(ct, len(str_a))
        assert check_partial_encrypt(pt)
        print(f"i = {i} OK!")

    except ValueError as e:
        if "NULL" in str(e):
            print("NULL byte!")

        elif "too large" in str(e):
            print("Out of bytes, try running script again?")
            break

        else:
            raise e

    i += 1
