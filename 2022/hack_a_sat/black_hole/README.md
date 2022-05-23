# Black Hole

**Category**: Crypto \
**Points**: 111

We found a satellite but we can't speak its language. It changes its encryption
encoding every time we open a connection...

We've got an open connection to the satellite.

It sent us this encoded message. Decode it and send it back to get the flag.

## Overview

Connecting to the server we see:

```
$ nc black_hole.satellitesabove.me 5300
Ticket please:
ticket{charlie751363sierra3:GN3V4dzRfb4yZtGnJREYUff56lp_3EokEIsP4cgdFVI0pM-9DObLzmVURI9exskplg}
Generating black hole...

Encoded msg is: d7cd51f7864a2014bc8b34022012a5970cde9593b18f6be0ce4dd25c03e583c3a9c59f6d3f57d0c234778a8afb01afde8abdb7ff4d63e0bb5944714209bcab4949c48838ee385ce7f7193ef09e36696b214725487625dca6f9a44b4f183b6f750c23a22a8338338540345f616cc00fcb5e71b9918efce2aadf3fb6dd99745f5697045c95d198df55a1b8e3520e907631453b0f58062d093a8665e471ce584abc7d7990f0b034c111cc38c17617d6a3ad32abbda3a214c0199a289769f4051268df7e81d8e1277d1f92919954c3b1dd3038b7b5d224a8822b4373401856260bb763e62d5ef5e6871720037fd3ffd7083db528a62fda4f364b679797ba54ffb5c7
We can stream 18909 bytes of data before the sat kills the connection. Please help. (Send your message in hex.)
(18909) Msg: aa
bb0e89d16e2fc7da100946fd15448e977a3221ba630a3d5caf2876f2bc5c8a576da4ea86407f2fdc9623b93be13da0b1f7f18964cea2a3566f443badde4f87749174185804952eeaf3facdeb4c91bd34f4bd0995a20e9e08327e0f63f3814b2db1abb474187ef73f769c4505a0779ba69bcc642256da9bfa962ee10288cb6743d3186d450a7a876345ca82c31a5933ef154c17afe8db85fc6d2a3dab501ba09bc375409196badd42e75357d4f24fcec5b24ef6812462a98d09629a619a496cce2c8fb4a1d7484f38a9cd0e8b4162e2c10afb75587267811aea6ce239c68ab778aaff8b2eb02a3a7d565530d13e716156ef904353948b15e936324aed7fbec01d
(18908) Msg: ab
bb0e89d16e2fc7da100946fd15448e977a3221ba630a3d5caf2876f2bc5c8a576da4ea86407f2fdc9623b93be13da0b1f7f18964cea2a3566f443badde4f87749174185804952eeaf3facdeb4c91bd34f4bd0995a20e9e08327e0f63f3814b2db1abb474187ef73f769c4505a0779ba69bcc642256da9bfa962ee10288cb6743d3186d450a7a876345ca82c31a5933ef154d17afe8db85fc6d2a3dab501ba09bc375409196badd42e75357d4f24fcec5b24ef6812462a98d09629a619a496cce2c8fb4a1d7484f38a9cd0e8b4162e2c10afb75587267811aea6ce239c68ab778aaff8b2eb02a3a7d565530d13e716156ef904353948b15e936324aed7fbec01d
(18907) Msg:
```

Basically we can send 18909 bytes of plaintext that the server encrypts for us.
The goal is to decrypt the encoded message.

It turns out plaintexts with similar lengths have similar ciphertexts. The
XOR'd ciphertexts the same as the XOR'd plaintexts, but the bytes are shuffled.

Also the indices of the shuffle only depend on the length of the plaintext, so
we can decrypt a message a given length with just the following things:
1. A plaintext of the same length with a known ciphertext
2. The indices of the shuffle for that length

Also, since we don't know how long the desired plaintext is, we just keep
sending longer and longer plaintexts until we get the flag. One hiccup is that
we can't send null bytes for some reason, but that's not too difficult to work
around. Solve script in [solve.py](solve.py).

> Note: The script sometimes fails to get the flag for some reason, idk why
