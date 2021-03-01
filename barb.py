#!/usr/bin/env python
import atexit
import os
import re
import readline
import sys


class ParseError(Exception): pass
class RunError(Exception): pass


class Env:
    def __init__(self, parent=None, globalize=True):
        self.bindings = {}
        self.parent = parent

        if not parent and globalize:
            self.globalize()

    def globalize(self):
        self.bindings = {
            "decl": Primitive(decl, 1),
            "def": Primitive(def_, 2),
            "fn": Primitive(fn, 2),
            "list": Primitive(list_),
            "quote": Primitive(quote, 1),
            "meta": Primitive(meta, 2),
            "meta-set!": Primitive(meta_set, 3),
            "do": Primitive(do),
            "eval": Primitive(eval_, 1),
            "cons": Primitive(cons, 2),
        }
        [self.evaluate(e) for e in PRELUDE]

    def lookup(self, k):
        if k in self.bindings:
            return self.bindings[k]
        if self.parent:
            return self.parent.lookup(k)
        raise RunError(f"unknown variable: {k}")

    def bind(self, k, v):
        self.bindings[k] = v

    def evaluate(self, expr):
        return expr.evaluate(self)


empty_env = Env(globalize=False)


class Expr:
    def __init__(self):
        self.meta = {}

    def expand(self, env):
        return self

    def evaluate(self, env):
        return self

    def get_meta(self, k):
        return self.meta.get(k.value, List([]))

    def set_meta(self, k, v):
        self.meta[k.value] = v
        return self


class Value(Expr):
    def __init__(self, value):
        self.value = value
        super().__init__()

    def __repr__(self):
        return str(self.value)


class Number(Value): pass
class String(Value): pass


class Boolean(Value):
    def __bool__(self):
        return bool(self.value)


class Symbol(Value):
    def evaluate(self, env):
        return env.lookup(self.value)


class Call(Expr):
    def __init__(self, args, body):
        self.args = args
        self.body = body
        super().__init__()

    def __repr__(self):
        return f"(fn [{' '.join(str(a) for a in self.args)}] {self.body})"


class Fn(Call):
    def evaluate(self, env):
        return Closure(self, env)

    def apply(self, args, env):
        return Closure(self, env).apply(args, env)


class Closure(Expr):
    def __init__(self, fn, env):
        self.fn = fn
        self.env = env
        super().__init__()

    def apply(self, args, env):
        is_macro = self.fn.meta.get("macro", False)
        if is_macro:
            e = env
        else:
            e = Env(parent=self.env)

        if len(args) != len(self.fn.args):
            raise RunError(
                f"function called with {len(args)} arguments, but expected {len(self.fn.args)}."
            )

        for k, v in zip(self.fn.args, args):
            e.bind(k.value, v if is_macro else env.evaluate(v))
        return e.evaluate(self.fn.body)


class CollectionIt:
    def __init__(self, c):
        self.c = c
        self.idx = 0

    def __next__(self):
        if self.idx >= len(self.c):
            raise StopIteration
        self.idx += 1
        return self.c.values[self.idx-1]


class Collection(Expr):
    def __init__(self, values):
        self.values = values
        super().__init__()

    def __repr__(self):
        return " ".join(str(v) for v in self.values)

    def __len__(self):
        return len(self.values)

    def __iter__(self):
        return CollectionIt(self)


class Array(Collection):
    def __repr__(self):
        return f"[{super().__repr__()}]"


class List(Collection):
    def __repr__(self):
        return f"({super().__repr__()})"

    def evaluate(self, env):
        if not self.values:
            raise RunError("Calling empty list!")
        return env.evaluate(self.values[0]).apply(self.values[1:], env)


class Primitive(Expr):
    def __init__(self, f, arity=None):
        self.f = f
        self.arity = arity
        super().__init__()

    def apply(self, args, env):
        if self.arity:
            if len(args) != self.arity:
                raise RunError(
                    f"primitive called with {len(args)} arguments, but expected {self.arity}."
                )
            return self.f(env, *args)

        return self.f(env, args)

    def __repr__(self):
        return "<primitive>"


def def_(env, s, v):
    v = env.evaluate(v)
    env.bind(s.value, v)
    return v


def fn(env, args, body):
    return Fn(args, body)


def list_(env, args):
    return List([env.evaluate(a) for a in args])


def quote(env, arg):
    return arg


def decl(env, s):
    env.bind(s.value, s)

    return s


def meta(env, s, k):
    e = env.lookup(s.value)

    return e.get_meta(k)


def meta_set(env, s, k, v):
    e = env.lookup(s.value)
    e.set_meta(k, env.evaluate(v))

    env.bind(s.value, e)

    return e


def do(env, args):
    return [env.evaluate(a) for a in args][-1]


def eval_(env, expr):
    return env.evaluate(env.evaluate(expr))


def cons(env, e, l):
    e = env.evaluate(e)
    l = env.evaluate(l)
    n = l.values.copy()
    n.insert(0, e)
    return l.__class__(n)


def tokenize(s):
    s = s.replace(",", " ").replace(":", " ")
    special = "(){}[]\""

    for c in special:
        s = s.replace(c, f" {c} ")

    return s.split()


def make_pairs(l):
    if len(l) % 2 != 0:
        raise ParseError("Map length not even.")
    for i in range(0, len(l), 2):
        yield l[i:i+2]


def read_string(tokens):
    s = []
    while tokens:
        t = tokens.pop(0)
        if t == '"':
            return " ".join(s)
        if t.endswith('\\'):
            s.append(t[:-2])
            t = tokens.pop(0)
        s.append(t)


def read_tokens(tokens, parent=None):
    pairs = {
        "(": ")",
        "[": "]",
        "{": "}",
    }
    builders = {
        "(": List,
        "[": Array,
        "{": lambda l: cons(empty_env, Symbol("Map", "from-array"), List(make_pairs(l))),
    }
    if not tokens:
        raise ParseError("Unclosed expression: {parent}")

    token = tokens.pop(0)

    if token in pairs:
        l = []
        closer = pairs[token]
        build = builders[token]
        while tokens[0] != closer:
            l.append(read_tokens(tokens, parent=token))
        tokens.pop(0)
        return build(l)
    elif token in "}])":
        raise ParseError(f"Unexpected expression close: {token}")
    elif token.isdigit():
        return Number(int(token))
    elif token == '"':
        return String(read_string(tokens))
    elif token == 'true':
        return Boolean(True)
    elif token == 'false':
        return Boolean(False)
    else:
        return Symbol(token)


def strip_comments(s):
    return re.sub(";.*", "", s)


def parse(s):
    s = strip_comments(s)
    tokens = tokenize(s)

    res = []
    while tokens:
        res.append(read_tokens(tokens))

    return res


class Completer:
    def __init__(self, m):
        self.m = m

    def complete(self, text, state):
        if state == 0:
            if text:
                self.matches = [s for s in self.m.vars if s.startswith(text)]
            else:
                self.matches = self.m.vars.keys()

        if len(self.matches) > state:
            return self.matches[state]


def setup_readline(m):
    histfile = os.path.join(os.path.expanduser("~"), ".carp_history")
    try:
        readline.read_history_file(histfile)
        readline.set_history_length(1000)
    except FileNotFoundError:
        pass

    atexit.register(readline.write_history_file, histfile)

    readline.set_completer(Completer(m).complete)


def repl():
    env = Env()
    setup_readline(env)
    while True:
        try:
            expr = input("> ")
        except EOFError:
            return

        if expr == ":q":
            print("vale.")
            return

        try:
            expr = parse(expr)
        except ParseError as e:
            print(e)
            continue

        try:
            print("=>", [env.evaluate(e) for e in expr][-1])
        except RunError as e:
            print(e)


def file_(name):
    with open(name) as f:
        m = Env()
        return [m.evaluate(e) for e in parse(f.read())][-1]


with open("prelude.carp") as f:
    PRELUDE = parse(f.read())


if __name__ == '__main__':
    if len(sys.argv) == 1:
        repl()
    elif len(sys.argv) == 2:
        file_(sys.argv[1])
    else:
        print("usage: ./mae.py <file>")
