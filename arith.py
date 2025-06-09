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
    dom: 'Type'
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
    todo






## ---------- Symbolic execution ----------

# A Formula is one of
# Num
class SymVar(NamedTuple):
    name: str
    t: BaseType

class BinFExpr(NamedTuple):
    l: 'Formula'
    r: 'Formula'
    op: str

class NegFExpr(NamedTuple):
    fe: 'Formula'

# A SymbEnv is an Env where values are Formulas, ie dict[str, Formula]

def symb_exec(fun: 'Fun') -> 'Formula':
    todo

def symb_interp(e: 'Expr', env: 'SymbEnv') -> 'Formula':
    todo

