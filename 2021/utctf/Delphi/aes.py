import os
from Crypto.Cipher import AES
import Crypto.Util.Padding as cup

key = b"a" * 32
challenge = b"1234567887654321" * 2

print("Challenge:", challenge.hex())


def encrypt(pt):
    iv = os.urandom(16)
    cipher = AES.new(key, AES.MODE_CBC, iv)
    pt = cup.pad(pt, 16)
    return cipher.encrypt(pt)


def decrypt(ct):
    iv = ct[:16]
    ct = ct[16:]
    cipher = AES.new(key, AES.MODE_CBC, iv)
    pt = cipher.decrypt(ct)
    return cup.unpad(pt, 16)


def go():
    ct = input("Please submit authorization token.\n")
    try:
        ct = bytes.fromhex(ct)
        pt = decrypt(ct)
        if pt == challenge:
            print("You win")
        else:
            print("Invalid challenge provided.")
    except ValueError as e:
        print("Decryption failed.")


for i in range(12230 + 64):
    go()
