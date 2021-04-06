# scrapyard_scramble

**Category**: Rev \
**Points**: 497 (7 solves) \
**Author**: jrmo14

## Challenge

Here's 200 bucks, go get some stuff from the scrap yard. And try not to get
tetanus, yeah?

Attachments: `scrapyard_scramble`

## Overview

It's a Rust binary. Let's try running it:
```
$ ./scrapyard_scramble
Welcome to the scrapyard, choose whatever catches your eye

Would you like to:
[0] Search for an item
[1] Check your cart
[2] Checkout
[3] Remove an item from your cart
[4] Check wallet
[5] Leave

What do you wanna do? 0
You found a Engine block for $100, ya want it?
[0] No
[1] Yes
What do you wanna do? 1

Would you like to:
[0] Search for an item
[1] Check your cart
[2] Checkout
[3] Remove an item from your cart
[4] Check wallet
[5] Leave

What do you wanna do? 2
Thank you for shopping
```

## Solution

Open it in Ghidra and find a hidden option:
```
$ ./scrapyard_scramble
Welcome to the scrapyard, choose whatever catches your eye

Would you like to:
[0] Search for an item
[1] Check your cart
[2] Checkout
[3] Remove an item from your cart
[4] Check wallet
[5] Leave

What do you wanna do? 1337
What's the discount code: idk
You think you're slick huh?
```

To find the discount code, just try super hard to parse through the disassembly
because Rust reversing is painful as fuck (I ended up using GDB to figure out
what was in the registers). Basically it calls `try_fold` with your input and
some constant byte string, goal is to make it return 0.

Solution
```python
enc = bytes.fromhex("6262706f6b597b5d7330170dcfdc9b8569452a5ecfded7651f05c1ad2427f1f47d")
decrypt = lambda i, b: ((i * i) & 0xff) ^ b
print(bytes([decrypt(i, b) for i, b in enumerate(enc)]))
```
