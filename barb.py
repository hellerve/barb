#!/usr/bin/env python
import atexit
import os
import re
import readline
import sys


class ParseError(Exception):
    pass


class RunError(Exception):
    pass


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

    def __repr__(self):
        return f"<{self.__class__.__name__.lower()}>"


class Env(Expr):
    def __init__(self, parent=None, globalize=True):
        super().__init__()
        self.bindings = {}
        self.parent = parent

        if not parent and globalize:
            self.globalize()

    def globalize(self):
        self.bindings = {
            "decl": Primitive(decl, 1),
            "fn?": Primitive(isfn, 1),
            "fn": Primitive(fn, 2),
            "list": Primitive(list_),
            "quote": Primitive(quote, 1),
            "meta": Primitive(meta, 2),
            "meta-set!": Primitive(meta_set, 3),
            "do": Primitive(do),
            "eval": Primitive(eval_),
            "cons": Primitive(cons, 2),
            "if": Primitive(if_, 3),
            "prn": Primitive(prn),
            "let": Primitive(let, 2),
            "parent": Primitive(lambda e, env: e.evaluate(env).parent or List([]), 1),
            "current-env": Primitive(lambda env: env, 0),
            "make-env": Primitive(lambda _: Env.empty(), 0),
        }
        [self.evaluate(e) for e in PRELUDE]

    def lookup(self, k):
        fst = k[0]
        if fst in self.bindings:
            res = self.bindings[fst]
            if len(k) > 1:
                return res.lookup(k[1:])
            return res
        if self.parent:
            return self.parent.lookup(k)
        raise RunError(f"unknown variable: {'.'.join(k)}")

    def get_global(self):
        if not self.parent:
            return self
        return self.parent.get_global()

    def bind(self, k, v):
        self.bindings[k] = v

    def evaluate(self, expr):
        return expr.evaluate(self)

    def evaluate_in(self, expr, e):
        env = Env(parent=self)
        res = env.evaluate(expr)
        self.bindings[e.value] = env
        return res

    @staticmethod
    def empty():
        return Env(globalize=False)


class Value(Expr):
    def __init__(self, value):
        self.value = value
        super().__init__()

    def __repr__(self):
        return str(self.value)


class Number(Value):
    pass


class String(Value):
    pass


class Boolean(Value):
    def __bool__(self):
        return bool(self.value)


class Symbol(Value):
    def evaluate(self, env):
        if self.meta.get("value"):
            return self.meta["value"]
        if self.meta.get("dispatches"):
            raise RunError("TODO: what happens here?")
        return env.lookup(self.path())

    def apply(self, args, env):
        dispatches = self.meta.get("dispatches")

        if not dispatches:
            raise RunError(f"{self.value} is not a function, it has no dispatches!")

        arity = len(args)

        candidates = [cand for cand in dispatches if len(cand.args) == arity]

        if not candidates:
            raise RunError(f"{self.value} has no arity {arity} dispatch!")

        return candidates[0].apply(args, env, macro=self.meta.get("macro"))

    def path(self):
        return self.value.split(".")


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

    def apply(self, args, env, macro=None):
        return Closure(self, env).apply(args, env, macro=macro)


class Closure(Expr):
    def __init__(self, fn, env):
        self.fn = fn
        self.env = env
        super().__init__()

    def apply(self, args, env, macro=None):
        is_macro = macro or self.fn.meta.get("macro", False)
        if is_macro:
            e = env
        else:
            e = Env(parent=self.env)

        if len(args) != len(self.args):
            raise RunError(
                f"function called with {len(args)} arguments, but expected {len(self.args)}."
            )

        for k, v in zip(self.args, args):
            e.bind(k.value, v if is_macro else env.evaluate(v))
        return e.evaluate(self.body)

    @property
    def args(self):
        return self.fn.args

    @property
    def body(self):
        return self.fn.body


class Collection(Expr):
    def __init__(self, values):
        self.values = values
        super().__init__()

    def __repr__(self):
        return " ".join(str(v) for v in self.values)

    def __len__(self):
        return len(self.values)

    def __iter__(self):
        return self.values.__iter__()

    def __getitem__(self, items):
        return self.values.__getitem__(items)


class Array(Collection):
    def __repr__(self):
        return f"[{super().__repr__()}]"


class List(Collection):
    def __bool__(self):
        return len(self.values) != 0

    def __repr__(self):
        return f"({super().__repr__()})"

    def evaluate(self, env):
        if not self.values:
            raise RunError("Calling empty list!")
        return env.evaluate(self.values[0]).apply(self.values[1:], env)

    def head(self):
        return self.values[0] if self.values else List([])


class Primitive(Expr):
    def __init__(self, f, arity=None):
        self.f = f
        self.arity = arity
        super().__init__()

    def apply(self, args, env):
        if self.arity is not None:
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


def isfn(env, obj):
    obj = env.evaluate(obj)
    if isinstance(obj, Fn):
        return Boolean(True)
    return Boolean(False)


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
    e = env.lookup(s.path())

    return e.get_meta(k)


def meta_set(env, s, k, v):
    e = env.lookup(s.path())
    e.set_meta(k, env.evaluate(v))

    env.bind(s.value, e)

    return e


def do(env, args):
    return [env.evaluate(a) for a in args][-1]


def eval_(env, args):
    if len(args) == 1:
        return env.evaluate(env.evaluate(args[0]))
    elif len(args) == 2:
        where = env.evaluate(args[1])
        if isinstance(where, Env):
            return where.evaluate(env.evaluate(args[0]))
        return env.evaluate_in(env.evaluate(args[0]), where)
    else:
        raise RunError("eval expected one or two arguments, but got {len(args}")


def cons(env, e, l):
    e = env.evaluate(e)
    l = env.evaluate(l)
    n = l.values.copy()
    n.insert(0, e)
    return l.__class__(n)


def if_(env, cond, then, els):
    if env.evaluate(cond):
        return env.evaluate(then)
    return env.evaluate(els)


def let(env, bindings, body):
    e = Env(parent=env)

    for k, v in make_pairs(bindings):
        e.bind(k.value, e.evaluate(v))
    return e.evaluate(body)


def prn(env, args):
    print(*(env.evaluate(arg) for arg in args))
    return List([])


def tokenize(s):
    s = s.replace(",", " ").replace(":", " ")
    special = '(){}[]"'

    for c in special:
        s = s.replace(c, f" {c} ")

    return s.split()


def make_pairs(l):
    if len(l) % 2 != 0:
        raise ParseError("pair length not even.")
    for i in range(0, len(l), 2):
        yield l[i : i + 2]


def read_string(tokens):
    s = []
    while tokens:
        t = tokens.pop(0)
        if t == '"':
            return " ".join(s)
        if t.endswith("\\"):
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
        "{": lambda l: cons(Env.empty(), Symbol("Map.from-array"), List(make_pairs(l))),
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
            if not tokens:
                raise ParseError(f"Unclosed expression: {token}")
        tokens.pop(0)
        return build(l)
    elif token in "}])":
        raise ParseError(f"Unexpected expression close: {token}")
    elif token.isdigit():
        return Number(int(token))
    elif token == '"':
        return String(read_string(tokens))
    elif token == "true":
        return Boolean(True)
    elif token == "false":
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
            res = [env.evaluate(e) for e in expr][-1]
            print("=>", res.meta["value"] if "value" in res.meta else res)
        except RunError as e:
            print(e)


def file_(name):
    with open(name) as f:
        m = Env()
        return [m.evaluate(e) for e in parse(f.read())][-1]


with open("prelude.carp") as f:
    PRELUDE = parse(f.read())


if __name__ == "__main__":
    if len(sys.argv) == 1:
        repl()
    elif len(sys.argv) == 2:
        file_(sys.argv[1])
    else:
        print("usage: ./mae.py <file>")
