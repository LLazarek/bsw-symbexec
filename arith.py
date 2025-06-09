from enum import Enum
from typing import NamedTuple, Callable

## ---------- Language data definitions ----------

# An Expr is one of
class Num(NamedTuple):
    n: int

class BiNumOp(NamedTuple): # + - /
    l: 'Expr'
    r: 'Expr'
    op: Callable[[int, int], int]
    op_name: str

class Var(NamedTuple):
    name: str

class Let(NamedTuple):
    name: str
    ann: 'Type'
    val: 'Expr'
    body: 'Expr'

class Fun(NamedTuple):
    params: list[str]
    anns: list['Type']
    body: 'Expr'
class App(NamedTuple):
    fun: 'Expr'
    args: list['Expr']




# a Type is one of
class BaseType(Enum):
    INT = 1
class FunType(NamedTuple):
    dom: list['Type']
    rng: 'Type'



# Convenience defs for testing
def Add(a, b):
    return BiNumOp(a, b, lambda a,b: a+b, '+')
def Sub(a, b):
    return BiNumOp(a, b, lambda a,b: a-b, '-')
def Mul(a, b):
    return BiNumOp(a, b, lambda a,b: a*b, '*')






## ---------- Concrete execution ----------
# A Value is one of
# Num
class Closure(NamedTuple):
    fun: Fun
    env: 'Env'

# An Env is a dict[str, Value]

def interp(e: 'Expr', env: 'Env') -> 'Value':
    match e:
        case Num(n):
            return e
        case BiNumOp(l, r, op, op_name):
            lv = interp(l, env)
            rv = interp(r, env)
            assert isinstance(lv, Num) and isinstance(rv, Num), f"Bad argument types for {op_name}: {lv} and {rv}"
            return Num(op(lv.n, rv.n))
        case Var(name):
            return lookup(env, name)
        case Let(name, ann, expr, body):
            val = interp(expr, env)
            return interp(body, bind(env, [name], [val]))
        case Fun(args, types, body):
            return Closure(e, env)
        case App(f, args):
            fv = interp(f, env)
            argvs = [interp(arg, env) for arg in args]
            assert isinstance(fv, Closure), f"Bad app, expected function, got {fv}"
            assert len(args) == len(fv.fun.params), f"Arity error, expected {len(fv.fun.params)} arguments, got {len(args)}"
            return interp(fv.fun.body, bind(fv.env, fv.fun.params, argvs))

        case _:
            raise Exception(f"Unknown expr {e}")


def lookup(env: 'Env', name: str) -> 'Value':
    if name in env:
        return env[name]
    else:
        raise Exception(f"Unbound variable {name}")

def bind(env: 'Env', names: list[str], vals: list['Value']) -> 'Env':
    return env | dict(zip(names, vals))


# ## ---------- Symbolic execution ----------

# # A Formula is one of
# # Num
# class SymVar(NamedTuple):
#     name: str
#     t: BaseType

# class BinFExpr(NamedTuple):
#     l: 'Formula'
#     r: 'Formula'
#     op: str

# # A SymbEnv is an Env where values are Formulas, ie dict[str, Formula]

# def symb_exec(fun: 'Fun') -> 'Formula':
#     todo

# def symb_interp(e: 'Expr', env: 'SymbEnv') -> 'Formula':
#     match e:
#         case Num(n):
#             # return e
#         case BiNumOp(l, r, op, op_name):
#             # lv = interp(l, env)
#             # rv = interp(r, env)
#             # assert isinstance(lv, Num) and isinstance(rv, Num), f"Bad argument types for {op_name}: {lv} and {rv}"
#             # return Num(op(lv.n, rv.n))
#         case Var(name):
#             # return lookup(env, name)
#         case Let(name, ann, expr, body):
#             # val = interp(expr, env)
#             # return interp(body, bind(env, [name], [val]))
#         case Fun(args, types, body):
#             # return Closure(e, env)
#         case App(f, args):
#             # fv = interp(f, env)
#             # argvs = [interp(arg, env) for arg in args]
#             # assert isinstance(fv, Closure), f"Bad app, expected function, got {fv}"
#             # assert len(args) == len(fv.fun.params), f"Arity error, expected {len(fv.fun.params)} arguments, got {len(args)}"
#             # return interp(fv.fun.body, bind(fv.env, fv.fun.params, argvs))

#         case _:
#             raise Exception(f"Unknown expr {e}")

