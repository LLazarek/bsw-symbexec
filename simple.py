## Plan -- finish @ 4.40pm
#
# Recap:
# - We implemented symbolic execution for plain arithmetic, wasn't much to it
# - We added boolean ops and assertions, and suddenly things started to get interesting
# - We specialized our execution engine to collect assertion violations, and to track
#   the "path condition" -- the conditions under which evaluation can reach a given expression
# - Then the assertion case basically tracked failed assertions by checking satisfiability,
#   recording violations, and recording the check in the path condition
# - We wrote this `satisfiable` helper that queries the SMT solver. Recap what a SMT solver is
# - I also added this helper to get the model from the solver, which we will use in tests
#
# 17. Write tests
# 17.1. Talk about testing/checking AV pathconds
# 17.2. Run the tests
#
#
# --
# Now the fun: If!
# 16. Exercise! Take 4min, implement interp If
#
# 17. Discussion: what do we need to do about symbolic if? Recall branching picture from board
# 18. Write some tests for symbolic if (pre-written programs, fill avs)
# 17. Implement symbolic if,
# --- Run tests: Interesting point in last test: weakness of our unsound design!
#
# 18. Recap weaknesses of our if implementation
# ---> DONE ,,
# 18. Exercise! Take 5-10min. Discuss with neighbors, what are some approaches to fix the soundness problem with `if`? Problems? Tradeoffs?
#     --> interpretation operates over multiple possible program states, and returns multiple possible results, all in parallel
#     --> just changing return type to multiple, cps'ing?
# ---> DONE ^^
# 18. (if time?) Exercise! Take 10-15min. A terminating program can cause `symb_interp` to run forever. Write such a program, and then propose ideas to address it.
#
#
# ---------- if time, state ----------
# 1. Boxes, get, set, seq, data defs
# 2. Finish pre-written tests
# 3. 


from enum import Enum
from typing import NamedTuple, Callable
import z3

# What's missing?
# No loops! Handling loops is hard in same way that ifs are hard, except can't even take the path of forking bc there are potentially infinite execution paths.
#   -- in practice, typical approach is the same as our workaround: sacrifice soundness by considering a fixed number of iterations (often small, 1-5).
# Our store is "nice", it's impossible to compute arbitrary references. Means we can treat them fully concretely. In langs like C (or we'll see later, in the shell) you can, and that means we have to model the store with symbolic keys as well as values. That means we often can't just use the same `store_get` function as the interpreter, we need a symbolic one that considers all cells that a symbolic ref might identify!
# No external function calls (e.g. libraries, FFIs). 

# An Expr is one of
class Num(NamedTuple):
    n: int
    def make_z3(self, _):
        return self.n

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

class Bool(NamedTuple):
    b: bool
    def make_z3(self, _):
        return self.b
class If(NamedTuple):
    tst: 'Expr'
    thn: 'Expr'
    els: 'Expr'
class BiNumCmp(NamedTuple): # < i=
    l: 'Expr'
    r: 'Expr'
    op: Callable[[int, int], bool]
    op_name: str
class BoolOp(NamedTuple): # and or xor b=
    l: 'Expr'
    r: 'Expr'
    op: Callable[[bool, bool], bool]
    op_name: str

class Assert(NamedTuple):
    tst: 'Expr'



class Str(NamedTuple):
    s: str
    def make_z3(self, _):
        return self.s
class Concat(NamedTuple):
    l: 'Expr'
    r: 'Expr'
class StrEq(NamedTuple):
    l: 'Expr'
    r: 'Expr'

class Fun(NamedTuple):
    params: list[str]
    anns: list['Type']
    body: 'Expr'
class App(NamedTuple):
    fun: 'Expr'
    args: list['Expr']

class Box(NamedTuple):
    val: 'Expr'
class Get(NamedTuple):
    box: 'Expr'
class Set(NamedTuple):
    box: 'Expr'
    val: 'Expr'
class Seq(NamedTuple):
    first: 'Expr'
    second: 'Expr'



# a Type is one of
class BaseType(Enum):
    INT = 1
    BOOL = 2
    STR = 3
class FunType(NamedTuple):
    dom: 'Type'
    rng: 'Type'
class BoxType(NamedTuple):
    inner: 'Type'



def Add(a, b):
    return BiNumOp(a, b, lambda a,b: a+b, '+')
def Sub(a, b):
    return BiNumOp(a, b, lambda a,b: a-b, '-')
def Mul(a, b):
    return BiNumOp(a, b, lambda a,b: a*b, '*')
def Eq(a, b):
    return BiNumCmp(a, b, lambda a,b: a==b, '=')
def Neq(a, b):
    return BiNumCmp(a, b, lambda a,b: a!=b, '!=')
def Lt(a, b):
    return BiNumCmp(a, b, lambda a,b: a<b, '<')
def Gt(a, b):
    return BiNumCmp(a, b, lambda a,b: a>b, '>')
def And(a, b):
    return BoolOp(a, b, lambda a,b: a and b, 'and')
def Not(a):
    return BoolOp(a, Bool(True), lambda a,b: a != b, '!=')





# A Value is one of
# Num
# Bool
# Str
class Closure(NamedTuple):
    fun: Fun
    env: 'Env'
class Ref(NamedTuple):
    i: int

# An Env is a dict[str, Value]
# A Store is a dict[int, Value]

class AssertionFailure(Exception):
    pass

def interpN(es, env, store, k):
    vs = []
    s = store
    for e in es:
        v, s = interp(e, env, s)
        vs.append(v)
    return k(vs, s)

def interp2(l, r, env, store, k):
    # lv, s2 = interp(l, env, store)
    # rv, s3 = interp(r, env, s2)
    # return k(lv, rv, s3)
    return interpN([l, r], env, store, lambda lr, s: k(lr[0], lr[1], s))

def interp_op_2(l, r, op, arg_t, res_t, env, store):
    def k(lv, rv, s3):
        assert isinstance(lv, arg_t) and isinstance(rv, arg_t), \
            f"Bad argument types for op {op}: expected {arg_t}, got {lv} and {rv}"
        return res_t(op(lv, rv)), s3
    return interp2(l, r, env, store, k)

def interp(e: 'Expr', env: 'Env', store: 'Store') -> tuple['Value', 'Store']:
    match e:
        case Num(n):
            return e, store
        case BiNumOp(l, r, op, op_name):
            return interp_op_2(l, r, lambda a, b: op(a.n, b.n),
                               Num, Num,
                               env, store)
        case Var(name):
            return lookup(env, name), store
        case Let(name, ann, val, body):
            v, s2 = interp(val, env, store)
            return interp(body, env | {name: v}, s2)


        case Bool(b):
            return e, store
        case If(tst, thn, els):
            tstv, s2 = interp(tst, env, store)
            match tstv:
                case Bool(True):
                    return interp(thn, env, s2)
                case Bool(False):
                    return interp(els, env, s2)
                case _:
                    raise Exception("bad program")
            raise Exception("never get here")
        case BiNumCmp(l, r, op):
            return interp_op_2(l, r, lambda a, b: op(a.n, b.n),
                               Num, Bool,
                               env, store)
        case BoolOp(l, r, op):
            return interp_op_2(l, r, lambda a, b: op(a.b, b.b),
                               Bool, Bool,
                               env, store)


        case Str(s):
            return e, store
        case Concat(l, r):
            return interp_op_2(l, r, lambda a, b: a.s + b.s,
                               Str, Str,
                               env, store)
        case StrEq(l, r):
            return interp_op_2(l, r, lambda a, b: a.s == b.s,
                               Str, Bool,
                               env, store)


        case Fun(a, t, b):
            return Closure(e, env), store
        case App(f, a):
            def do_app(vs, s3):
                fv = vs[0]
                argvs = vs[1:]
                assert isinstance(fv, Closure), f"Bad App, expected a function, got {fv}"
                assert len(fv.fun.params) == len(argvs), f"Arity error, expected {len(fv.fun.params)} arguments, got {len(argvs)}"
                return interp(fv.fun.body, bind(fv.env, fv.fun.params, argvs), s3)
            return interpN([f, *a], env, store, do_app)


        case Box(e):
            v, s2 = interp(e, env, store)
            ref = malloc(s2)
            return ref, store_set(s2, ref, v)
        case Get(e):
            ref, s2 = interp(e, env, store)
            assert isinstance(ref, Ref), f"Bad Get, expected a Ref, got {ref}"
            return store_lookup(s2, ref), s2
        case Set(b, e):
            def do_set(ref, newv, s3):
                assert isinstance(ref, Ref), f"Bad Get, expected a Ref, got {ref}"
                return newv, store_set(s3, ref, newv)
            return interp2(b, e, env, store, do_set)
        case Seq(e1, e2):
            return interp2(e1, e2, env, store, lambda _, v2, s3: (v2, s3))


        case Assert(e):
            v, s2 = interp(e, env, store)
            assert isinstance(v, Bool), f"Bad Assert, expected a Bool, got {v}"
            if not v.b:
                raise AssertionFailure(f"Assertion failure: {e}")
            return v, s2


        case _:
            raise Exception(f"Unknown expression type: {e}")

def lookup(env, name):
    if name in env:
        return env[name]
    else:
        raise Exception(f"Unbound variable {name}")
def bind(env, names, vals):
    return env | dict(zip(names, vals))
def malloc(store):
    if not store:
        return Ref(0)
    else:
        return Ref(max(store.keys()) + 1)
def store_lookup(store, ref):
    return store[ref.i]
def store_set(store, ref, newv):
    return store | {ref.i: newv}




# A Formula is one of
# Num
# Bool
# Str
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
class BinFExpr(NamedTuple):
    l: 'Formula'
    r: 'Formula'
    op: str

    def make_z3(self, varmap):
        lmade = self.l.make_z3(varmap)
        rmade = self.r.make_z3(varmap)
        match self.op:
            case '+':
                return lmade + rmade
            case '-':
                return lmade - rmade
            case '*':
                return lmade * rmade
            case '/':
                return lmade / rmade
            case '=':
                return lmade == rmade
            case '!=':
                return lmade != rmade
            case '<':
                return lmade < rmade
            case '>':
                return lmade > rmade
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


# A SymbResult is
# tuple['Formula',
#       'SymbStore',
#       'ConstraintSet', # current pathcond
#       list['ConstraintSet'] # pathconds of assertion violations
#      ]

def symb_interpN(es: list['Expr'], env: 'SymbEnv', store: 'SymbStore', pathcond: 'ConstraintSet',
                 k: Callable[[list['Formula'],
                              'SymbStore',
                              'ConstraintSet',
                              list['ConstraintSet']],
                             'SymbResult']):
    fs = []
    s = store
    pc = pathcond
    violations = []
    for e in es:
        formula, s, pc, vs = symb_interp(e, env, s, pc)
        fs.append(formula)
        violations.extend(vs)
    return k(fs, s, pc, violations)

def make_fexpr_k(fexpr_maker):
    return lambda fs, s, pc, violations: (fexpr_maker(fs), s, pc, violations)
# A ConstraintSet is a list[Constraint]

def symb_exec_v1(fun: 'Fun') -> 'Formula':
    for t in fun.anns:
        assert not (isinstance(t, FunType) or isinstance(t, BoxType)), \
            f"Inputs can only be first order, but got an input of type {t}"
    symvars = [SymVar(p, t) for p, t in zip(fun.params, fun.anns)]
    return symb_interp(fun.body, bind({}, fun.params, symvars), {}, [])[0]

def symb_exec(fun: 'Fun') -> list['ConstraintSet']:
    for t in fun.anns:
        assert not (isinstance(t, FunType) or isinstance(t, BoxType)), \
            f"Inputs can only be first order, but got an input of type {t}"
    symvars = [SymVar(p, t) for p, t in zip(fun.params, fun.anns)]
    return symb_interp(fun.body, bind({}, fun.params, symvars), {}, [])

# A SymbEnv is an Env where values are Formulas, ie dict[str, Formula]
# A SymbStore is a Store where values are Formulas, ie dict[i, Formula]

take_els = False
def cook_the_books():
    global take_els
    take_els = True

def symb_interp(e: 'Expr', env: 'SymbEnv', store: 'SymbStore',
                pathcond: 'ConstraintSet') -> 'SymbResult':
    match e:
        case Num(n):
            return e, store, pathcond, []
        case BiNumOp(l, r, op, op_name): # small diff
            return symb_interpN([l, r], env, store, pathcond,
                                make_fexpr_k(lambda fs: BinFExpr(fs[0], fs[1], op_name) \
                                             if not (isinstance(fs[0], Num) and isinstance(fs[1], Num)) \
                                             else Num(op(fs[0].n, fs[1].n))))
        case Var(name):
            return lookup(env, name), store, pathcond, []
        case Let(name, ann, val, body):
            v, s2, pc2, avs = symb_interp(val, env, store, pathcond)
            res, s3, pc3, more_avs = symb_interp(body, env | {name: v}, s2, pc2)
            return res, s3, pc3, avs + more_avs

        case Bool(b):
            return e, store, pathcond, []
        case If(tst, thn, els): # diff!
            tst_formula, s2, pc2, avs = symb_interp(tst, env, store, pathcond)
            # Design decision: unsoundness!
            # We arbitrarily choose to continue analysis with just one of the branch results.
            # This avoids exponential blowup, and significant complexity, to do the right thing
            avs_thn = []
            avs_els = []
            result_thn = None
            s3_thn = None
            pc3_thn = None
            if satisfiable(pc2 + [tst_formula]):
                result_thn, s3_thn, pc3_thn, avs_thn = symb_interp(thn, env, s2,
                                                                   pc2 + [tst_formula])
            if satisfiable(pc2 + [NegFExpr(tst_formula)]):
                result_els, s3_els, pc3_els, avs_els = symb_interp(els, env, s2,
                                                                   pc2 + [NegFExpr(tst_formula)])
            assert result_thn is not None or result_els is not None, f"Impossible? Neither case of an if are satisfiable?"

            
            # return (result_thn, s3_thn, pc3_thn, avs_thn + avs_els) if result_thn \
            #     else (result_els, s3_els, pc3_els, avs_thn + avs_els)

            
            global take_els
            if (take_els and result_els is not None) or result_thn is None:
                take_els = False
                return result_els, s3_els, pc3_els, avs_thn + avs_els
            else:
                return result_thn, s3_thn, pc3_thn, avs_thn + avs_els
        case BiNumCmp(l, r, op, op_name): # small diff
            return symb_interpN([l, r], env, store, pathcond,
                                make_fexpr_k(lambda fs: BinFExpr(fs[0], fs[1], op_name) \
                                             if not (isinstance(fs[0], Num) and isinstance(fs[1], Num)) \
                                             else Bool(op(fs[0].n, fs[1].n))))
        case BoolOp(l, r, op, op_name): # small diff
            return symb_interpN([l, r], env, store, pathcond,
                                make_fexpr_k(lambda fs: BinFExpr(fs[0], fs[1], op_name) \
                                             if not (isinstance(fs[0], Bool) and isinstance(fs[1], Bool)) \
                                             else Bool(op(fs[0].n, fs[1].n))))


        case Str(s):
            return e, store, pathcond, []
        case Concat(l, r): # small diff
            return symb_interpN([l, r], env, store, pathcond,
                                make_fexpr_k(lambda fs: BinFExpr(fs[0], fs[1], '++') \
                                             if not (isinstance(fs[0], Str) and isinstance(fs[1], Str)) \
                                             else Str(fs[0].s + fs[1].s)))
        case StrEq(l, r): # small diff
            return symb_interpN([l, r], env, store, pathcond,
                                make_fexpr_k(lambda fs: BinFExpr(fs[0], fs[1], '=') \
                                             if not (isinstance(fs[0], Str) and isinstance(fs[1], Str)) \
                                             else Bool(fs[0].s == fs[1].s)))


        case Fun(a, t, b):
            return Closure(e, env), store, pathcond, []
        case App(f, a):
            def do_app(vs, s3, pc, avs):
                fv = vs[0]
                argvs = vs[1:]
                assert isinstance(fv, Closure), f"Bad App, expected a function, got {fv}"
                assert len(fv.fun.params) == len(argvs), f"Arity error, expected {len(fv.fun.params)} arguments, got {len(argvs)}"
                result, s4, pc2, more_avs = symb_interp(fv.fun.body, bind(fv.env, fv.fun.params, argvs), s3, pc)
                return result, s4, pc2, avs + more_avs
            return symb_interpN([f, *a], env, store, pathcond, do_app)


        case Box(e):
            v, s2, pc, avs = symb_interp(e, env, store, pathcond)
            ref = malloc(s2)
            return ref, store_set(s2, ref, v), pc, avs
        case Get(e):
            ref, s2, pc, avs = symb_interp(e, env, store, pathcond)
            assert isinstance(ref, Ref), f"Bad Get, expected a Ref, got {ref}"
            return store_lookup(s2, ref), s2, pc, avs
        case Set(b, e):
            def do_set(fs, s3, pc, avs):
                ref, newv = fs
                assert isinstance(ref, Ref), f"Bad Get, expected a Ref, got {ref}"
                return newv, store_set(s3, ref, newv), pc, avs
            return symb_interpN([b, e], env, store, pathcond, do_set)
        case Seq(e1, e2):
            return symb_interpN([e1, e2], env, store, pathcond,
                                lambda fs, s3, pc, avs: (fs[1], s3, pc, avs))


        case Assert(e):
            formula, s2, pc, avs = symb_interp(e, env, store, pathcond)
            if satisfiable(pc + [NegFExpr(formula)]):
                return formula, s2, pc + [formula], avs + [[*pc, NegFExpr(formula)]]
            else:
                return formula, s2, pc, avs


        case SymVar(_, _):
            return e, store, pathcond, []


        case _:
            raise Exception(f"Unknown expression type: {e}")

def vars_in(formula):
    match formula:
        case SymVar(_, _):
            return [formula]
        case BinFExpr(l, r, _):
            return vars_in(l) + vars_in(r)
        case NegFExpr(inner):
            return vars_in(inner)

def satisfiable(constraints):
    varmap = {}
    s = z3.Solver()
    s.add(*[formula.make_z3(varmap) for formula in constraints])
    return s.check() != z3.unsat

def get_model(constraints):
    varmap = {}
    s = z3.Solver()
    s.add(*[formula.make_z3(varmap) for formula in constraints])
    assert s.check() != z3.unsat
    return s.model()


# fun(a: bool, b: int, c: bool) {
#   x, y, z = 0
#   if a {
#     x = -2
#   }
#   if b < 5 {
#     if !a && c {
#       y = 1
#     }
#     z = 2
#   }
#   assert x + y + z != 3
# }
# a = false, b < 5, c = true
# cook_the_books()
# f, _, _, avs = \
#     symb_exec(Fun(['a', 'b', 'c'],
#                 [BaseType.BOOL, BaseType.INT, BaseType.BOOL],
#                 Let('x', BaseType.INT, Box(Num(0)),
#                     Let('y', BaseType.INT, Box(Num(0)),
#                         Let('z', BaseType.INT, Box(Num(0)),
#                             Seq(If(Var('a'),
#                                    Set(Var('x'), Num(-2)),
#                                    Bool(False)),
#                                 Seq(If(Lt(Var('b'), Num(5)),
#                                        Seq(If(And(Neq(Var('a'), Bool(True)),
#                                                   Var('c')),
#                                               Set(Var('y'), Num(1)),
#                                               Bool(False)),
#                                            Set(Var('z'), Num(2))),
#                                        Bool(False)),
#                                     Assert(Neq(Add(Get(Var('x')),
#                                                    Add(Get(Var('y')),
#                                                        Get(Var('z')))),
#                                                Num(3))))))))))
# print(avs)
# for avpath in avs:
#     m = get_model(avpath)
#     print(f"{m!r}")
#     for var in m:
#         print(f"{var} : {m[var]}")
