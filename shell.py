from enum import Enum
from typing import NamedTuple, Callable
import z3

# Goal: automatically catch the following bugs
# 1) rm $1; cat $1 -- def bad
# 2) rm $1; cat $2 -- could be bad
# 3) if [$1 != $2]; then rm $1; cat $2; fi -- safe
# 4) rm -rf $1/ -- could be bad
# 5) if [$1 != ""]; then rm -rf $1/; fi -- safe


# What's missing?
# Expansion here is waay simplified, missing: FS-based expansion (globs), command substitutions
# Not modeling command output
# Not modeling path aliasing!!




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
    def make_z3(self, _):
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


# An Env is a dict[str, Value]
# A Store is a dict[int, Value]

def interpN(es, env, k):
    ec = 0
    for e in es:
        ec, env = interp(e, env)
    return k(ec, env)


def interp(s: 'Script', env: 'Env') -> tuple[int, 'Env']:
    match e:
        case Cmd(binary, args):
            expanded_args = [expand(arg, env) for arg in args]
            exit_code = run_binary(binary, expanded_args)
            return exit_code, env

        case Seq(s1, s2):
            return interpN([s1, s2], env, tuple)

        case Set(name, expr):
            expanded_str = expand(expr, env)
            env2 = bind(env, [name], [expanded_str])
            return 0, env2

        case If(tst, thn, els):
            match tst:
                case Test(expr):
                    if eval_test(expr, env):
                        return interp(thn, env)
                    else:
                        return interp(els, env)
                case _:
                    ec, env2 = interp(tst, env)
                    if ec == 0:
                        return interp(thn, env2)
                    else:
                        return interp(els, env2)

def eval_test(expr, env):
    match expr:
        case StrCmp(l, r, op, op_name):
            return op(expand(l, env),
                      expand(r, env))
        case BoolOp(l, r, op, op_name):
            return op(eval_test(l, env),
                      eval_test(r, env))
        case Neg(inner):
            return not eval_test(inner, env)
        case FileCheck(path, state):
            expanded_path = expand(path, env)
            return True # todo

def run_binary(binary, args, store):
    return 0 # todo

def expand(word: 'Word', env: 'Env') -> Str:
    match word:
        case Str(s):
            return word
        case Var(name):
            if name in env:
                return env[name]
            else:
                return Str("") # Shell fun!
        case Concat(l, r):
            return expand(l, env) + expand(r, env)

class BaseType(Enum):
    INT = 1
    BOOL = 2
    STR = 3



# Unchanged from simple
def lookup(env, name):
    if name in env:
        return env[name]
    else:
        raise Exception(f"Unbound variable {name}")
def bind(env, names, vals):
    return env | dict(zip(names, vals))




# A SymString is one of
# Str
# SymVar of type STR
class SymConcat(NamedTuple):
    l: 'SymString'
    r: 'SymString'
    def make_z3(self, varmap):
        lmade = self.l.make_z3(varmap)
        rmade = self.r.make_z3(varmap)
        return lmade + rmade


class FileState(Enum):
    File = 1
    Dir = 2
    Deleted = 3
    Unknown = 4


# A Formula is one of
class FSPredicate(NamedTuple):
    path: 'SymString'
    state: FileState
    def make_z3(self, varmap):
        return z3_fs_state_funs[self.state](self.path.make_z3(varmap))

class Bool(NamedTuple):
    b: bool
    def make_z3(self, varmap):
        return self.b

class SymVar(NamedTuple):
    name: str
    t: BaseType

    def make_z3(self, varmap):
        if self.name not in varmap:
            match self.t:
                case BaseType.INT:
                    varmap[self.name] = z3.Int(self.name)
                case BaseType.BOOL:
                    varmap[self.name] = z3.Bool(self.name)
                case BaseType.STR:
                    varmap[self.name] = z3.String(self.name)
        return varmap[self.name]

class BoolFExpr(NamedTuple):
    l: 'Formula|SymString'
    r: 'Formula|SymString'
    op: str

    def make_z3(self, varmap):
        lmade = self.l.make_z3(varmap)
        rmade = self.r.make_z3(varmap)
        match self.op:
            case '=':
                return lmade == rmade
            case '!=':
                return lmade != rmade
            case 'and':
                return z3.And(lmade, rmade)
            case 'or':
                return z3.Or(lmade, rmade)
            case _:
                raise Exception(f"Unhandled smt conversion of op {op}")

class NegFExpr(NamedTuple):
    fe: 'Formula'

    def make_z3(self, varmap):
        return z3.Not(self.fe.make_z3(varmap))


# A SymbEC is one of
# a SymVar of type INT
class EC(NamedTuple):
    n: int

# A SymbResult is
# tuple['SymbEC',
#       'SymbEnv',
#       'SymbFS',
#       'ConstraintSet', # current pathcond
#       list['ConstraintSet'] # pathconds of assertion violations
#      ]

# A SymbEnv is an Env where values are Formulas, ie dict[str, Formula]
# A SymbStore is a Store where values are Formulas, ie dict[i, Formula]
# A SymbFS is a Store where keys are Formulas and values are FileStates, ie dict[Formula, FileState]


def symb_interpN(es: list['Script'], env: 'SymbEnv', fs: 'SymbFS', pathcond: 'ConstraintSet',
                 k: Callable[[list['SymbEC'],
                              'SymbEnv',
                              'SymbFS',
                              'ConstraintSet',
                              list['ConstraintSet']],
                             'SymbResult']):
    ecs = []
    violations = []
    for script in es:
        ec, env, fs, pathcond, avs = symb_interp(script, env, fs, pathcond)
        ecs.append(formula)
        violations.extend(avs)
    return k(ecs, env, fs, pathcond, violations)


neg_invariants = [FSPredicate('/', FileState.Deleted)]

last_ec_id = 0
def symb_interp(s: 'Script', env: 'SymbEnv', fs: 'SymbFS', pathcond: 'ConstraintSet') -> 'SymbResult':
    global last_ec_id
    match s:
        case Cmd(binary, args):
            expanded_args = [symb_expand(arg, env) for arg in args]
            preconds, effects = lookup_spec(binary, expanded_args)
            avs = []
            ec = SymVar(f'ec_{last_ec_id}', BaseType.INT)
            last_ec_id += 1
            if not satisfiable(pathcond + preconds, fs): # Guaranteed to fail
                avs = [pathcond + preconds]
                ec = EC(1)
                fs2 = fs
            elif not satisfiable(pathcond + [NegFExpr(c) for c in preconds], fs): # Guaranteed to succeed
                ec = EC(0)
                fs2 = effects(fs)
                avs = [pathcond] if satisfiable(pathcond + neg_invariants, fs2) else []
            else: # Could fail or succeed
                fs2 = effects(fs)
                avs = [pathcond] if satisfiable(pathcond + neg_invariants, fs2) else []
            return ec, env, fs2, pathcond, avs

        case Seq(s1, s2):
            return symb_interpN([s1, s2], env, fs, pathcond,
                                lambda ecs, env, fs, pathcond, avs: (ecs[1], env, fs, pathcond, avs))

        case Set(name, expr):
            expanded_formula = sym_expand(expr, env)
            env2 = bind(env, [name], [expanded_str])
            return 0, env2

        case If(tst, thn, els):
            match tst:
                case Test(expr):
                    formula = symb_eval_test(expr, env)
                    if not satisfiable(pathcond + [formula], fs): # Guaranteed to fail
                        ec3, env3, fs3, pc3, avs3 = symb_interp(els, env, fs, pathcond + [NegFExpr(formula)])
                        return ec3, env3, fs3, pc3, avs3
                    elif not satisfiable(pathcond + [NegFExpr(formula)], fs): # Guaranteed to succeed
                        ec3, env3, fs3, pc3, avs3 = symb_interp(thn, env, fs, pathcond + [formula])
                        return ec3, env3, fs3, pc3, avs3
                    else: # Could fail or succeed
                        _, _, _, _, avs_els = symb_interp(els, env, fs, pathcond + [NegFExpr(formula)])
                        ec3, env3, fs3, pc3, avs_thn = symb_interp(thn, env, fs, pathcond + [formula])
                        return ec3, env3, fs3, pc3, avs_thn + avs_els
                case _:
                    ec, env2, s2, fs2, pc2, avs2 = symb_interp(tst, env, fs, pathcond)
                    match ec:
                        case EC(0):
                             ec3, env3, fs3, pc3, avs3 = symb_interp(thn, env2, fs2, pc2)
                             return ec3, env3, fs3, pc3, avs2 + avs3
                        case EC(_):
                             ec3, env3, fs3, pc3, avs3 = symb_interp(els, env2, fs2, pc2)
                             return ec3, env3, fs3, pc3, avs2 + avs3
                        case SymVar(_, _):
                             _, _, _, _, avs3 = symb_interp(els, env2, fs2, pc2)
                             ec4, env4, fs4, pc4, avs4 = symb_interp(thn, env2, fs2, pc2)
                             return ec4, env4, fs4, pc4, avs2 + avs3 + avs4


def symb_eval_test(expr, env):
    match expr:
        case StrCmp(l, r, op, op_name):
            expanded_l = symb_expand(l, env)
            expanded_r = symb_expand(r, env)
            if isinstance(expanded_l, Str) and isinstance(expanded_r, Str):
                return expanded_l == expanded_r
            else:
                return BoolFExpr(expanded_l, expanded_r, op_name)
        case BoolOp(l, r, op, op_name):
            l_formula = symb_eval_test(l, env)
            r_formula = symb_eval_test(r, env)
            if isinstance(l_formula, Bool) and isinstance(r_formula, Bool):
                return op(l_formula.b, r_formula.b)
            else:
                return BoolFExpr(l_formula, r_formula, op_name)
        case Neg(inner):
            inner_formula = symb_eval_test(inner, env)
            if isinstance(inner_formula, Bool):
                return not inner_formula.b
            else:
                return NegFExpr(inner_formula)
        case FileCheck(path, state):
            path_formula = symb_expand(path, env)
            return FSPredicate(path_formula, state)

def symb_expand(word: 'Word', env: 'SymbEnv') -> 'SymString':
    match word:
        case Str(s):
            return word
        case Var(name):
            if name in env:
                return env[name]
            else:
                return SymVar(name, BaseType.STR)
        case Concat(l, r):
            le = symb_expand(l, env)
            re = symb_expand(r, env)
            if isinstance(le, Str) and isinstance(re, str):
                return Str(le.s + re.s)
            else:
                return SymConcat(le, re)

def lookup_spec(binary, arg_symstrs) -> tuple[list['Formula'], Callable[['FS'], 'FS']]:
    match binary:
        case 'echo':
            return [], lambda fs: fs
        case 'cat':
            return [FSPredicate(arg_path, FileState.File) for arg_path in arg_symstrs], \
                lambda fs: fs
        case 'touch':
            def effects(fs):
                newfs = fs | {}
                for arg_path in arg_symstrs:
                    if arg_path not in fs:
                        newfs = newfs | {arg_path: FileState.File}
                return newfs
            return [], effects
        case 'rm':
            def effects(fs):
                newfs = fs | {}
                for arg_path in arg_symstrs:
                    newfs = newfs | {arg_path: FileState.Deleted}
                return newfs
            return [FSPredicate(arg_path, FileState.File) for arg_path in arg_symstrs], \
                effects
        case 'rm-rf':
            def effects(fs):
                newfs = fs | {}
                for arg_path in arg_symstrs:
                    newfs = newfs | {arg_path: FileState.Deleted}
                return newfs
            return [BoolFExpr(FSPredicate(arg_path, FileState.File), FSPredicate(arg_path, FileState.Dir), 'or') for arg_path in arg_symstrs], \
                effects
        case _:
            print(f"Warning: optimistically assuming {binary} is safe and effect-free!")
            return [], lambda fs: fs


def symb_exec(script: 'Script') -> list['ConstraintSet']:
    ec, env, fs, pc, avs = symb_interp(script, {}, {}, [])
    return avs


z3_fs_state_funs = {
    FileState.File: z3.Function('isfile', z3.StringSort(), z3.BoolSort()),
    FileState.Dir: z3.Function('isdir', z3.StringSort(), z3.BoolSort()),
    FileState.Deleted: z3.Function('isdeleted', z3.StringSort(), z3.BoolSort())
}

# If a path is in a particular state, then it can't be in any other
_fs_rule_path = z3.String('_path')
FS_rules = [z3.ForAll(_fs_rule_path,
                      z3.Implies(z3_fs_state_funs[state](_fs_rule_path),
                                 z3.Not(z3.Or(*[z3_fs_state_funs[other_state](_fs_rule_path) \
                                                for other_state in z3_fs_state_funs \
                                                if other_state != state])))) \
            for state in z3_fs_state_funs]

def encode_fs_z3(fs: 'SymbFS') -> list['FSPredicate']:
    return FS_rules + \
        [FSPredicate(path_symstr, state) for path_symstr, state in fs.items()]

def satisfiable(constraints, fs):
    varmap = {}
    s = z3.Solver()
    s.add(*[formula.make_z3(varmap) for formula in constraints])
    s.add(*[fs_pred.make_z3(varmap) for fs_pred in encode_fs_z3(fs)])
    return s.check() == z3.sat

def get_model(constraints):
    varmap = {}
    s = z3.Solver()
    s.add(*[formula.make_z3(varmap) for formula in constraints])
    res = s.check()
    return res, s.model() if res == z3.sat else s.unsat_core()


avs = symb_exec(Seq(Cmd('rm', Var('d1')),
                    Cmd('cat', Var('d1'))))
print(avs)
for avpath in avs:
    print(get_model(avpath))


