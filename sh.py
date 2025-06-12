from enum import Enum
from typing import NamedTuple, Callable
import z3

# Concrete:
# inputs: input to our script (basically like arguments), but also now the environment (ie FS)
#
# symbolic:
# how do we reason about commands like grep? z3 can't give us formulas about those
# how do we reason about possible filesystems? -----> crappy dictionary thing
# how do we reason about how commands work differently based on the possible filesystems?
# no assertions -- we lost our easy, explicit, "there might be a bug here" points -- how are we going to think about bugs? -----> commands might fail
# there are way more commands than the fixed set of known operations that we had before

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

# if grep ....;
# if [ $1 = "hi" ];

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
class FileCheck(NamedTuple): # [ -f $path ] [ -d $path ]
    path: 'Word'
    state: 'FileState'

class FileState(Enum):
    File = 1
    Dir = 2
    Deleted = 3



def interp(s: 'Script', env: 'Env') -> tuple[int, 'Env']:
    match s:
        case Cmd(binary: str, args: list['Word']):
            # args could be literal strings or variables, or some combination
            expanded_args: list[str] = [expand(arg, env) for arg in args]
            exit_code = run_binary(binary, expanded_args)
            return exit_code, env

        case Seq(s1: 'Script', s2: 'Script'):
            exit_code1, env1 = interp(s1, env)
            exit_code2, env2 = interp(s2, env1)
            return exit_code2, env2

        case Set(name: str, expr: 'Word'):
            expanded_str = expand(expr, env)
            env2 = bind(env, [name], [expanded_str])
            return 0, env2

        case If(tst: 'Script|Test', thn: 'Script', els: 'Script'):
            match tst:
                case Test(expr):
                    if eval_test(expr, env):
                        return interp(thn, env2)
                    else:
                        return interp(els, env2)
                case s: # arbitrary script
                    ec, env2 = interp(s, env)
                    if ec == 0:
                        return interp(thn, env2)
                    else:
                        return interp(els, env2)

def eval_test(expr: 'TestExpr', env: 'Env') -> bool:
    match expr:
        case StrCmp(l: 'Word', r: 'Word', op, op_name):
            return op(expand(l, env),
                      expand(r, env))
        case BoolOp(l: 'TestExpr', r: 'TestExpr', op, op_name):
            return op(eval_test(l, env),
                      eval_test(r, env))
        case Neg(inner):
            return not eval_test(inner, env)
        case FileCheck(path: 'Word', state: 'FileState'):
            expanded_path = expand(path, env)
            match state:
                case FileState.File:
                    return os.path.isfile(expanded_path)
                case FileState.Dir:
                    return os.path.isdir(expanded_path)
                case FileState.Deleted:
                    return not (os.path.isfile(expanded_path) or os.path.isdir(expanded_path))

def expand(word: 'Word', env: 'Env') -> Str: # in the real world: result is more like list[Str]
    match word:
        case Str(s):
            return word
        case Var(name):
            if name in env:
                return env[name]
            else:
                # raise Exception(f"Unbound id {name}")
                return Str("") # POSIX specified
        case Concat(l: 'Word', r: 'Word'):
            return Str(expand(l, env) + expand(r, env))

def run_binary(binary_path: str, args: list['Str']):
    # Popen(binary_path, args)
    # fork, exec
    return random([0, 1])



# Unchanged from arith
def lookup(env, name):
    if name in env:
        return env[name]
    else:
        raise Exception(f"Unbound variable {name}")
def bind(env, names, vals):
    return env | dict(zip(names, vals))



# A SymbResult is
# tuple['SymbEC',
#       'SymbEnv',
#       'SymbFS',
#       'ConstraintSet', # current pathcond
#       'AssertionViolations' # pathconds of assertion violations
#      ]

# A SymbFS is a dictionary where keys are Formulas and values are FileStates, ie dict[Formula, FileState]

# A SymbEnv is an Env where values are Formulas, ie dict[str, Formula]

# A SymbEC is one of
# a SymVar of type INT
class EC(NamedTuple):
    n: int

class FSPredicate(NamedTuple):
    path: 'SymString'
    state: FileState


def symb_interp(s: 'Script',
                env: 'SymbEnv',
                fs: 'SymbFS',
                pathcond: 'ConstraintSet',
                avs: 'AssertionViolations') -> 'SymbResult':


