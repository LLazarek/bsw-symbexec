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
        case Cmd(binary, args):
            # args could be literal strings or variables, or some combination
            expanded_args: list[str] = [expand(arg, env) for arg in args]
            exit_code = run_binary(binary, expanded_args)
            return exit_code, env

        case Seq(s1, s2):
            exit_code1, env1 = interp(s1, env)
            exit_code2, env2 = interp(s2, env1)
            return exit_code2, env2

        case Set(name, expr):
            expanded_str = expand(expr, env)
            env2 = bind(env, [name], [expanded_str])
            return 0, env2

        case If(tst, thn, els):
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
        case Concat(l, r):
            return Str(expand(l, env) + expand(r, env))

def run_binary(binary_path: str, args: list['Str']):
    # subprocess.run(binary_path, args)
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







### Annoying Z3 stuff
_path_names = 0
def fresh_path_constant_var_name():
    global _path_names
    _path_names += 1
    return f'_const_path_{_path_names}'

class rawZ3(NamedTuple):
    z3: any

    def make_z3(self, _, _2):
        return self.z3


### ------------------







# A SymString is one of
# Str
# SymVar of type STR
class SymConcat(NamedTuple):
    l: 'SymString'
    r: 'SymString'
    def make_z3(self, varmap, pathmap):
        lmade = self.l.make_z3(varmap, pathmap)
        rmade = self.r.make_z3(varmap, pathmap)
        return lmade + rmade



# A Formula is one of
# SymString
class FSPredicate(NamedTuple):
    path: 'SymString'
    state: FileState
    def make_z3(self, varmap, pathmap):
        statef = z3_fs_state_funs[self.state]
        if isinstance(self.path, Str):
            if self.path.s not in pathmap:
                fresh_const_path_var = z3.String(fresh_path_constant_var_name())
                pathmap[self.path.s] = fresh_const_path_var
            return statef(pathmap[self.path.s])
        else:
            return statef(self.path.make_z3(varmap, pathmap)) # == True

z3_fs_state_funs = {
    FileState.File: z3.Function('isfile', z3.StringSort(), z3.BoolSort()),
    FileState.Dir: z3.Function('isdir', z3.StringSort(), z3.BoolSort()),
    FileState.Deleted: z3.Function('isdeleted', z3.StringSort(), z3.BoolSort())
}


class Bool(NamedTuple):
    b: bool
    def make_z3(self, varmap, pathmap):
        return self.b

class BaseType(Enum):
    INT = 1
    BOOL = 2
    STR = 3

class SymVar(NamedTuple):
    name: str
    t: BaseType

    def make_z3(self, varmap, pathmap):
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

    def make_z3(self, varmap, pathmap):
        lmade = self.l.make_z3(varmap, pathmap)
        rmade = self.r.make_z3(varmap, pathmap)
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

    def make_z3(self, varmap, pathmap):
        return z3.Not(self.fe.make_z3(varmap, pathmap))

def Or(fexprs):
    fexpr = Bool(False)
    for fe in fexprs:
        fexpr = BoolFExpr(fexpr, fe, 'or')
    return fexpr




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

# An AssertionViolations is a list[tuple['ConstraintSet', 'SymbFS']]


# SMT solvers understand
# - integers, booleans, strings
# - arithmetic and boolean operations
# - string operations
# - uninterpreted functions -- declare f(int) -> int, assert f(1) = 5, f(x) = 10, ....,
#
# isfile(path) -> bool
# isdir(path) -> bool
# isdeleted(path) -> bool
# forall path in paths . isfile(path) xor isdir(path) xor isdeleted(path)

neg_invariants = [FSPredicate(Str('/'), FileState.Deleted)]

last_ec_id = 0
def symb_interp(s: 'Script',
                env: 'SymbEnv',
                fs: 'SymbFS',
                pathcond: 'ConstraintSet',
                avs: 'AssertionViolations') -> 'SymbResult':
    global last_ec_id
    match s:
        case Cmd(binary, args):
            expanded_args: list['Formula'] = [symb_expand(arg, env) for arg in args]
            preconds, effects, postconds = lookup_spec(binary, expanded_args)
            # preconds: list['Formula']
            # postconds: list['Formula']
            # effects: (SymbFS -> SymbFS)

            # Check preconds are satisfiable
            # if not satisfiable, there's a bug for sure
            #
            # cat $somefile --- does $somefile exist or not? don't know -- should we report a bug?
            # if we do, there might be tons of warnings
            # alternatively only warn if something is guaranteed to go wrong
            #
            # Check negation of preconds is satisfiable
            # if so, then there might be a bug
            #
            # commands might fail, but the script keeps going -- implicit branching
            # in one branch the command succeeded, and in another it failed --- (assume it succeeded?)
            #
            # apply the effects on our fs IF the command succeeded
            # add the postconds to our pathcondition
            #
            precond_success_conditions = pathcond + preconds
            precond_failure_conditions = pathcond + [Or([NegFExpr(c) for c in preconds])]

            if not satisfiable(precond_success_conditions, fs): # Guaranteed to fail
                # Precondition constraints that will fail
                avs += [(precond_failure_conditions, fs)]
                ec = EC(1)
                fs2 = fs
                # Nothing to add for effects of execution
            elif not satisfiable(precond_failure_conditions, fs): # Guaranteed to succeed
                # Nothing to add about failure conditions
                ec = EC(0)
                fs2 = effects(fs)
                # Effects of execution
                pathcond = pathcond + postconds
                # if avs_only_must and not satisfiable(pathcond + [NegFExpr(c) for c in neg_invariants], fs2):
                #     avs += [(pathcond + neg_invariants, fs2)]
                # el
                if satisfiable(pathcond + neg_invariants, fs2):
                    avs += [(pathcond + neg_invariants, fs2)]
            else: # Could fail or succeed
                # Precondition constraints that may fail
                avs += [(precond_failure_conditions, fs)]
                ec = SymVar(f'_ec_{last_ec_id}', BaseType.INT)
                last_ec_id += 1
                # NOTE: unsound choice! Really we should explore both possibilities of
                # cmd failing and succeeding, but we'll just model that it succeeded
                fs2 = effects(fs)
                # Effects of execution
                pathcond = pathcond + postconds
                # if avs_only_must and not satisfiable(pathcond + [NegFExpr(c) for c in neg_invariants], fs2):
                #     avs += [(pathcond + neg_invariants, fs2)]
                # el
                if satisfiable(pathcond + neg_invariants, fs2):
                    avs += [(pathcond + neg_invariants, fs2)]
            return ec, env, fs2, pathcond, avs

        case Seq(s1, s2):
            # exit_code1, env1 = interp(s1, env)
            # exit_code2, env2 = interp(s2, env1)
            # return exit_code2, env2
            exit_code1, env1, fs1, pc1, avs1 = symb_interp(s1, env, fs, pathcond, avs)
            exit_code2, env2, fs2, pc2, avs2 = symb_interp(s2, env1, fs1, pc1, avs1)
            return exit_code2, env2, fs2, pc2, avs2

        case Set(name, expr):
            # expanded_str = expand(expr, env)
            # env2 = bind(env, [name], [expanded_str])
            # return 0, env2
            expanded_str_formula = symb_expand(expr, env)
            env2 = bind(env, [name], [expanded_str_formula])
            return 0, env2, fs, pathcond, avs

        case If(tst, thn, els):
            match tst:
                case Test(expr):
                    test_formula = symb_eval_test(expr, env)
                    if not satisfiable(pathcond + [test_formula], fs):
                        # can't pass -- guaranteed to take the else branch
                        return symb_interp(els,
                                           env,
                                           fs,
                                           pathcond + [NegFExpr(test_formula)],
                                           avs)
                    elif not satisfiable(pathcond + [NegFExpr(test_formula)], fs):
                        # must pass -- guaranteed to take the then branch
                        return symb_interp(thn,
                                           env,
                                           fs,
                                           pathcond + [test_formula],
                                           avs)
                    else: # could pass or fail
                        _, _, _, _, avs_els = symb_interp(els,
                                                          env,
                                                          fs,
                                                          pathcond + [NegFExpr(test_formula)],
                                                          avs)
                        ec3, env3, fs3, pc3, avs_thn = symb_interp(thn,
                                                                  env,
                                                                  fs,
                                                                  pathcond + [test_formula],
                                                                  avs)
                        # unsound choice!
                        return ec3, env3, fs3, pc3, avs_thn + avs_els
                case s:
                    ec, env2, s2, fs2, pc2, avs2 = symb_interp(s, env, fs, pathcond, avs)
                    match ec:
                        case EC(0):
                             ec3, env3, fs3, pc3, avs3 = symb_interp(thn, env2, fs2, pc2, avs2)
                             return ec3, env3, fs3, pc3, avs3
                        case EC(_):
                             ec3, env3, fs3, pc3, avs3 = symb_interp(els, env2, fs2, pc2, avs2)
                             return ec3, env3, fs3, pc3, avs3
                        case symvar:
                             _, _, _, _, avs3 = symb_interp(els,
                                                            env2,
                                                            fs2,
                                                            pc2 + [BoolFExpr(symvar, EC(0), '!=')],
                                                            avs2)
                             ec4, env4, fs4, pc4, avs4 = symb_interp(thn,
                                                                     env2,
                                                                     fs2,
                                                                     pc2 + [BoolFExpr(symvar, EC(0), '=')],
                                                                     avs3)
                             return ec4, env4, fs4, pc4, avs4

def lookup_spec(binary: str, arg_symstrs: list['SymStr']) -> tuple[list['Formula'], #preconds
                                                                   Callable[['SymbFS'], 'SymbFS'],
                                                                   list['Formula'] #postconds
                                                                   ]:
    match binary:
        case 'echo':
            return [], lambda fs: fs, []
        case 'cat':
            preconds = [FSPredicate(arg_path, FileState.File) for arg_path in arg_symstrs]
            postconds = [FSPredicate(arg_path, FileState.File) for arg_path in arg_symstrs] + \
                [BoolFExpr(arg_path, Str(""), '!=') for arg_path in arg_symstrs]
            effects = lambda fs: fs
            return preconds, effects, postconds
        case 'touch':
            preconds = [BoolFExpr(arg_path, Str(""), '!=') for arg_path in arg_symstrs]
            effects = lambda fs: fs | {arg_path: FileState.File for arg_path in arg_symstrs}
            postconds = [BoolFExpr(arg_path, Str(""), '!=') for arg_path in arg_symstrs]
            return preconds, effects, postconds
        case 'rm':
            return [FSPredicate(arg_path, FileState.File) for arg_path in arg_symstrs] + \
                [BoolFExpr(arg_path, Str(""), '!=') for arg_path in arg_symstrs], \
                lambda fs: fs | {arg_path: FileState.Deleted for arg_path in arg_symstrs}, \
                [BoolFExpr(arg_path, Str(""), '!=') for arg_path in arg_symstrs]
        case 'rm-rf':
            return [BoolFExpr(FSPredicate(arg_path, FileState.File),
                              FSPredicate(arg_path, FileState.Dir),
                              'or') \
                    for arg_path in arg_symstrs] + \
                            [BoolFExpr(arg_path, Str(""), '!=') for arg_path in arg_symstrs], \
                lambda fs: fs | {arg_path: FileState.Deleted for arg_path in arg_symstrs}, \
                [BoolFExpr(arg_path, Str(""), '!=') for arg_path in arg_symstrs]
        case _:
            print(f"Warning: optimistically assuming {binary} is safe and effect-free!")
            return [], lambda fs: fs, []
        


def symb_eval_test(expr: 'TestExpr', env: 'SymbEnv') -> 'Formula':
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
            if isinstance(le, Str) and isinstance(re, Str):
                return Str(le.s + re.s)
            else:
                return SymConcat(le, re)
        case _:
            raise Exception(f"Unexpected word: {word!r}")



_fs_rule_path = z3.String('_path')
FS_rules = [rawZ3(z3.ForAll(_fs_rule_path,
                            z3.Implies(z3_fs_state_funs[state](_fs_rule_path),
                                       z3.Not(z3.Or(*[z3_fs_state_funs[other_state](_fs_rule_path) \
                                                for other_state in z3_fs_state_funs \
                                                if other_state != state]))))) \
            for state in z3_fs_state_funs] + \
                    [rawZ3(z3.ForAll(_fs_rule_path,
                                     z3.Or(*[state_fun(_fs_rule_path) for state_fun in z3_fs_state_funs.values()])))]


def encode_fs_z3(fs: 'SymbFS') -> list['FSPredicate']:
    return [FSPredicate(path_symstr, state) for path_symstr, state in fs.items()] + \
        FS_rules

def satisfiable(constraints: list['Formula'], fs: 'SymbFS') -> bool:
    s = z3.Solver()
    varmap = {}
    const_path_map = {}
    s.add(*[formula.make_z3(varmap, const_path_map) for formula in constraints])
    s.add(*[fs_pred.make_z3(varmap, const_path_map) for fs_pred in encode_fs_z3(fs)])
    s.add(*[constvar == path for path, constvar in const_path_map.items()])
    return s.check() != z3.unsat

def get_model(constraints, fs):
    varmap = {}
    const_path_map = {}
    s = z3.Solver()
    s.add(*[formula.make_z3(varmap, const_path_map) for formula in constraints])
    s.add(*[fs_pred.make_z3(varmap, const_path_map) for fs_pred in encode_fs_z3(fs)])
    # Note: order is important here! these constraints must be added last,
    # after the constant paths have been populated
    s.add(*[constvar == path for path, constvar in const_path_map.items()])
    res = s.check()
    return res, s.model() if res == z3.sat else None


def symb_exec(script: 'Script') -> list['ConstraintSet']:
    ec, env, fs, pc, avs = symb_interp(script,
                                       {},
                                       {Str('/'): FileState.Dir},
                                       [],
                                       [])
    return avs


avs = symb_exec(Seq(Cmd('rm', [Var('d1')]),
                    Cmd('cat', [Var('d1')])))
print(avs)
for avpath, fs in avs:
    print(get_model(avpath, fs))

avs = symb_exec(Seq(Set("d1", Str("")),
                    Cmd('rm-rf', [Concat(Var('d1'), Str('/'))])))
print(avs)
for avpath, fs in avs:
    print(get_model(avpath, fs))

avs = symb_exec(Cmd('rm-rf', [Concat(Var('d1'), Str('/'))]))
print(avs)
for avpath, fs in avs:
    print(get_model(avpath, fs))


