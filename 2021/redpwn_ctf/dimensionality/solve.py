import pwn


pwn.context.binary = elf = pwn.ELF("./chall")
elf.address = 0x555555554000

bytes_thing = elf.read(0x55555555607F, 0x533)

start = bytes_thing.find(b"\x02")
end = bytes_thing.find(b"\x03")

thing = bytes_thing[start : end + 1]


def succ(path):
    """
    Possible successor paths from `path`.
    """

    pos = path[-1]
    visited = set(path)
    choices = [1, 11, 121, -1, -11, -121]
    ans = []

    new_poss = [pos + c for c in choices]
    for new_pos in new_poss:
        if new_pos < 0 or new_pos >= len(thing):
            continue

        if thing[new_pos] != 0 and new_pos not in visited:
            ans.append(path + [new_pos])

    return ans


def bfs():
    q = succ([0])
    winners = []
    while q:
        path = q.pop()
        if len(path) >= 29:
            continue

        succs = succ(path)
        real_succs = []

        for path in succs:
            pos = path[-1]

            if thing[pos] == 3:
                winners.append(path)
            else:
                real_succs.append(path)

        q += real_succs

    return winners


def path_diffs(path):
    return [path[i + 1] - path[i] for i in range(len(path) - 1)]


def to_char(x):
    if x == -121:
        ans = 0
    elif x == 11:
        ans = 2
    elif x == 121:
        ans = 4
    elif x == -1:
        ans = 10
    elif x == 1:
        ans = 0x10
    elif x == -11:
        ans = 0x13
    else:
        raise ValueError("Unknown diff")
    return chr(0x62 + ans)


paths = bfs()

for path in paths:
    diffs = path_diffs(path)
    chars = "".join(to_char(x) for x in diffs)
    print(chars)
