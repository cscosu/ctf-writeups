import sys
from enum import Enum, auto


class NodeKind(Enum):
    Block = auto()
    Def = auto()
    UnDef = auto()
    Include = auto()
    Warning = auto()
    Error = auto()
    If = auto()
    IfDef = auto()
    IfNDef = auto()
    Raw = auto()


NK = NodeKind


class Node:
    def __init__(self, kind):
        self.kind = kind
        self.children = []

    attrs = ["kind", "children"]

    def __eq__(self, other):
        if not isinstance(other, Node):
            return NotImplemented
        else:
            return all(
                hasattr(self, a) == hasattr(other, a)
                and getattr(self, a, None) == getattr(other, a, None)
                for a in Node.attrs
            )

    def __repr__(self):
        ans = {}
        for a in Node.attrs:
            if hasattr(self, a):
                if a == "children" and self.children == []:
                    pass  # Too many `children: []` is ugly
                elif a == "kind":
                    ans[a] = self.kind.name  # More concise
                else:
                    ans[a] = getattr(self, a)

        return repr(ans)

    def __str__(self):
        join_children = lambda prefix: " ".join(
            [prefix] + [str(c) for c in self.children]
        )
        join_children_newline = lambda: "\n".join(str(c) for c in self.children)

        def indent(s):
            return "\n".join(f"    {line}" for line in s.split("\n"))

        def str_if(prefix: str):
            cond = self.children[0]
            blocks = [indent(str(c)) for c in self.children[1:]]

            if len(self.children) == 2:
                return "#{} {}\n{}\n#endif".format(prefix, cond, blocks[0])
            elif len(self.children) == 3:
                return "#{} {}\n{}\n#else\n{}\n#endif".format(
                    prefix, cond, blocks[0], blocks[1]
                )
            else:
                raise ValueError(f"Too many children")

        return {
            NK.Block: join_children_newline,
            NK.Def: lambda: join_children("#define"),
            NK.UnDef: lambda: join_children("#undef"),
            NK.Include: lambda: join_children("#include"),
            NK.Warning: lambda: join_children("#warning"),
            NK.Error: lambda: join_children("#error"),
            NK.If: lambda: str_if("if"),
            NK.IfDef: lambda: str_if("ifdef"),
            NK.IfNDef: lambda: str_if("ifndef"),
            NK.Raw: lambda: self.children[0],
        }[self.kind]()

    def with_children(self, *children):
        self.children += children
        return self


class Parser:
    def __init__(self, prog: str):
        self.prog = prog.split("\n")
        self.i = 0

    def peek(self):
        if self.i < len(self.prog):
            words = self.prog[self.i].split()
            if len(words) > 0:
                return words[0]
            else:
                return ""
        else:
            return None

    def next(self):
        ans = self.prog[self.i]
        self.i += 1
        return ans

    def get_def(self):
        s = self.next().split()
        assert s[0] == "#define"
        return Node(NK.Def).with_children(*s[1:])

    def get_undef(self):
        s = self.next().split()
        assert s[0] == "#undef"
        assert len(s) == 2
        return Node(NK.UnDef).with_children(s[1])

    def get_include(self):
        s = self.next().split()
        assert s[0] == "#include"
        assert len(s) == 2
        return Node(NK.Include).with_children(s[1])

    def get_warning(self):
        s = self.next().split(" ", 1)
        assert s[0] == "#warning"
        assert len(s) == 2
        return Node(NK.Warning).with_children(s[1])

    def get_error(self):
        s = self.next().split(" ", 1)
        assert s[0] == "#error"
        assert len(s) == 2
        return Node(NK.Error).with_children(s[1])

    def get_if(self, kind):
        prefix = {
            NK.If: "#if",
            NK.IfDef: "#ifdef",
            NK.IfNDef: "#ifndef",
        }[kind]

        s = self.next().split(" ", 1)
        assert s[0] == prefix
        assert len(s) == 2

        if_block = self.get_block()
        ans = Node(kind).with_children(s[1], if_block)

        t = self.peek()
        if t == "#else":
            assert self.next() == "#else"
            else_block = self.get_block()
            ans.with_children(else_block)

        assert self.next() == "#endif"
        return ans

    def get_raw(self):
        s = self.next()
        return Node(NK.Raw).with_children(s)

    def get_block(self):
        ans = Node(NK.Block)

        while True:
            t = self.peek()
            terminals = {"#endif", "#else"}
            if t is None or t in terminals:
                break

            switch = {
                "#define": lambda: self.get_def(),
                "#undef": lambda: self.get_undef(),
                "#include": lambda: self.get_include(),
                "#warning": lambda: self.get_warning(),
                "#error": lambda: self.get_error(),
                "#if": lambda: self.get_if(NK.If),
                "#ifdef": lambda: self.get_if(NK.IfDef),
                "#ifndef": lambda: self.get_if(NK.IfNDef),
            }

            n = switch.get(t, self.get_raw)()
            ans.with_children(n)

        return ans


if __name__ == "__main__":
    f = "cpp.c"
    s = open(f).read().strip()
    n = Parser(s).get_block()
    print(n)
