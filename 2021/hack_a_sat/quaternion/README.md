# Quaternion

**Category**: Physics \
**Points**: 49

```
nc grave-error.satellitesabove.me 5020
```

## Overview

Connecting to the server we see:

```
[+] Opening connection to grave-error.satellitesabove.me on port 5020: Done
[*] Switching to interactive mode
            QUATERNION
            CHALLANGE

               z
               |
             __|____
            /  |   /|
  ______   /______/ |    ______
 |      |==|      | ====|      |---y
 |______|  |  /   | /   |______|
           |_/____|/
            /
           /                    /x
          x               z_ _ /
        Satellite              \
          Body                  \y
         Frame             J2000

A spacecraft is considered "pointing" in the direction of its z-axis or [0,0,1] vector in the "satellite body frame."
In the J2000 frame, the same spacecraft is pointing at [ 0.14129425 -0.98905974  0.04238827].
Determine the spacecraft attitude quaternion.
```

## Solution

We have get the sattelite's quaternion in the J2000 frame.
To calculate it, we just need the quaternion that rotates: \
`[0, 0, 1]` (the forward direction in the sattelite's body frame) to \
`[0.14129425, -0.98905974, 0.04238827]` (the forward direction in the J2000 frame).

I used this as reference: https://answers.unity.com/questions/1668856/whats-the-source-code-of-quaternionfromtorotation.html

```python
import pwn
import numpy as np
from pyquaternion import Quaternion

v_from = np.array([0, 0, 1])
v_to = np.array([0.14129425, -0.98905974, 0.04238827])

axis = np.cross(v_from, v_to)
angle = np.arccos(np.clip(np.dot(v_from, v_to), -1.0, 1.0))

q = Quaternion(axis=axis, angle=angle)
assert np.allclose(q.rotate(v_from), v_to)
print(q)

if pwn.args.REMOTE:
    io = pwn.remote("grave-error.satellitesabove.me", 5020)
    ticket = "ticket{bravo494806sierra2:GAtCHZzGFiRKyL5rxXEtFnoIRMN3TqnuUgXSu-np2BUwKi26O0Hd0L0Nw8kYWRcCOQ}"

    io.sendlineafter("Ticket please:\n", ticket)

    io.sendlineafter("Qx = ", str(q.x))
    io.sendlineafter("Qy = ", str(q.y))
    io.sendlineafter("Qz = ", str(q.z))
    io.sendlineafter("Qw = ", str(q.w))

    io.interactive()
```
