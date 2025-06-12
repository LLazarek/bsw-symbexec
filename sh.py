from enum import Enum
from typing import NamedTuple, Callable
import z3


# A Script is one of
class Cmd(NamedTuple):
    binary: str
    args: list['Word']
class Seq(NamedTuple):
    first: 'Script'
    second: 'Script'
class Set(NamedTuple):
    var: str
    expr: 'Word'
class If(NamedTuple):
    tst: 'Test|Script'
    thn: 'Script'
    els: 'Script'


# A Word is one of
class Str(NamedTuple):
    s: str
    def make_z3(self, _, _2):
        return self.s
class Var(NamedTuple):
    name: str
class Concat(NamedTuple):
    l: 'Word'
    r: 'Word'



class Test(NamedTuple):
    expr: 'TestExpr'

# A TestExpr is one of
class StrCmp(NamedTuple):
    l: 'Word'
    r: 'Word'
    op: Callable[[str, str], bool]
    op_name: str
class BoolOp(NamedTuple):
    l: 'TestExpr'
    r: 'TestExpr'
    op: Callable[[bool, bool], bool]
    op_name: str
class Neg(NamedTuple):
    inner: 'TestExpr'
class FileCheck(NamedTuple):
    path: 'Word'
    op_name: 'FileState'



def interp(s: 'Script', env: 'Env') -> tuple[int, 'Env']:
    match s:
        case Cmd(binary, args):

        case Seq(s1, s2):

        case Set(name, expr):

        case If(tst, thn, els):


