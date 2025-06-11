from enum import Enum
from typing import NamedTuple, Callable
import z3

## ---------- Language data definitions ----------

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

class Fun(NamedTuple):
    params: list[str]
    anns: list['Type']
    body: 'Expr'
class App(NamedTuple):
    fun: 'Expr'
    args: list['Expr']


class Bool(NamedTuple):
    b: bool
    def make_z3(self, _):
        return self.b
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



# a Type is one of
class BaseType(Enum):
    INT = 1
    BOOL = 2
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



class AssertionFailure(Exception):
    pass


## ---------- Concrete execution ----------
# A Value is one of
# Num
# Bool
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

        case Bool(b):
            return e
        case BiNumCmp(l, r, op, op_name):
            lv = interp(l, env)
            rv = interp(r, env)
            assert isinstance(lv, Num) and isinstance(rv, Num), f"Bad argument types for {op_name}: {lv} and {rv}"
            return Bool(op(lv.n, rv.n))
        case BoolOp(l, r, op, op_name):
            lv = interp(l, env)
            rv = interp(r, env)
            assert isinstance(lv, Bool) and isinstance(rv, Bool), f"Bad argument types for {op_name}: {lv} and {rv}"
            return Bool(op(lv.b, rv.b))
        case Assert(tst):
            tst_v = interp(tst, env)
            assert isinstance(tst_v, Bool)
            if not tst_v.b:
                raise AssertionFailure(f"Assertion failed: {e}")
            return tst_v

        case _:
            raise Exception(f"Unknown expr {e}")


def lookup(env: 'Env', name: str) -> 'Value':
    if name in env:
        return env[name]
    else:
        raise Exception(f"Unbound variable {name}")

def bind(env: 'Env', names: list[str], vals: list['Value']) -> 'Env':
    return env | dict(zip(names, vals))


## ---------- Symbolic execution ----------

# A Formula is one of
# Num
# Bool
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



# A SymbEnv is an Env where values are Formulas, ie dict[str, Formula]

# A ConstraintSet is list['Formula']

# A PathCondition is a ConstraintSet

# A SymbResult is a tuple of
# 'Formula',
# 'PathCondition',
# list['ConstraintSet']

def symb_exec_v1(fun: 'Fun') -> 'Formula':
    for t in fun.anns:
        assert not isinstance(t, FunType), f"Inputs can only be first-order, but got an input of type {t}"
    symvars = [SymVar(p, t) for p, t in zip(fun.params, fun.anns)]
    formula, pc, avs = symb_interp(fun.body, bind({}, fun.params, symvars), [], [])
    return formula

def symb_exec(fun: 'Fun') -> 'Formula':
    for t in fun.anns:
        assert not isinstance(t, FunType), f"Inputs can only be first-order, but got an input of type {t}"
    symvars = [SymVar(p, t) for p, t in zip(fun.params, fun.anns)]
    formula, pc, avs = symb_interp(fun.body, bind({}, fun.params, symvars), [], [])
    return formula, avs


def symb_interpN(es: list['Expr'],
                 env: 'SymbEnv',
                 pathcond: 'PathCondition',
                 avs: 'ConstraintSet',
                 k: Callable[[list['Formula'], 'PathCondition', 'ConstraintSet'],
                             'SymbResult']) -> 'SymbResult':
    result_formulas = []
    for e in es:
        formula, pathcond, avs = symb_interp(e, env, pathcond, avs)
        result_formulas.append(formula)
    return k(result_formulas, pathcond, avs)

def symb_interp(e: 'Expr',
                env: 'SymbEnv',
                pathcond: 'PathCondition',
                avs: list['ConstraintSet']) -> 'SymbResult':
    match e:
        case Num(n):
            # return e
            return e, pathcond, avs
        case BiNumOp(l, r, op, op_name):
            # lv = interp(l, env)
            # rv = interp(r, env)
            # assert isinstance(lv, Num) and isinstance(rv, Num), f"Bad argument types for {op_name}: {lv} and {rv}"
            # return Num(op(lv.n, rv.n))
            def k(formulas, pathcond, avs):
                l_formula, r_formula = formulas
                if isinstance(l_formula, Num) and isinstance(r_formula, Num):
                    return Num(op(l_formula.n, r_formula.n)), pathcond, avs
                else:
                    return BinFExpr(l_formula, r_formula, op_name), pathcond, avs
            return symb_interpN([l, r], env, pathcond, avs, k)
        case Var(name):
            # return lookup(env, name)
            return lookup(env, name), pathcond, avs
        case Let(name, ann, expr, body):
            # val = interp(expr, env)
            # return interp(body, bind(env, [name], [val]))
            formula, pc2, avs2 = symb_interp(expr, env, pathcond, avs)
            formula_result, pc3, avs3 = symb_interp(body,
                                                    bind(env, [name], [formula]),
                                                    pc2,
                                                    avs2)
            return formula_result, pc2, avs3
        case Fun(args, types, body):
            # return Closure(e, env)
            return Closure(e, env), pathcond, avs
        case App(f, args):
            # fv = interp(f, env)
            # argvs = [interp(arg, env) for arg in args]
            # assert isinstance(fv, Closure), f"Bad app, expected function, got {fv}"
            # assert len(args) == len(fv.fun.params), f"Arity error, expected {len(fv.fun.params)} arguments, got {len(args)}"
            # return interp(fv.fun.body, bind(fv.env, fv.fun.params, argvs))
            def k(formulas, pathcond, avs):
                fv = formulas[0]
                argfs = formulas[1:]
                assert isinstance(fv, Closure), f"Bad app, expected function, got {fv}"
                assert len(args) == len(fv.fun.params), f"Arity error, expected {len(fv.fun.params)} arguments, got {len(args)}"
                return symb_interp(fv.fun.body,
                                   bind(fv.env, fv.fun.params, argfs),
                                   pathcond,
                                   avs)
            return symb_interpN([f, *args], env, pathcond, avs, k)
        case Bool(b):
            # return e
            return e, pathcond, avs
        case BiNumCmp(l, r, op, op_name):
            # lv = interp(l, env)
            # rv = interp(r, env)
            # assert isinstance(lv, Num) and isinstance(rv, Num), f"Bad argument types for {op_name}: {lv} and {rv}"
            # return Bool(op(lv.n, rv.n))
            def k(formulas, pathcond, avs):
                l_formula, r_formula = formulas
                if isinstance(l_formula, Num) and isinstance(r_formula, Num):
                    return Bool(op(l_formula.n, r_formula.n)), pathcond, avs
                else:
                    return BinFExpr(l_formula, r_formula, op_name), pathcond, avs
            return symb_interpN([l, r], env, pathcond, avs, k)
        case BoolOp(l, r, op, op_name):
            # lv = interp(l, env)
            # rv = interp(r, env)
            # assert isinstance(lv, Bool) and isinstance(rv, Bool), f"Bad argument types for {op_name}: {lv} and {rv}"
            # return Bool(op(lv.b, rv.b))
            def k(formulas, pathcond, avs):
                l_formula, r_formula = formulas
                if isinstance(l_formula, Bool) and isinstance(r_formula, Bool):
                    return Bool(op(l_formula.b, r_formula.b)), pathcond, avs
                else:
                    return BinFExpr(l_formula, r_formula, op_name), pathcond, avs
            return symb_interpN([l, r], env, pathcond, avs, k)

        case Assert(tst):
            # tst_v = interp(tst, env)
            # assert isinstance(tst_v, Bool)
            # if not tst_v.b:
            #     raise AssertionFailure(f"Assertion failed: {e}")
            # return tst_v

            # Plan: look at tst, if it could fail, add it to the assertion violations we've found

            # Fun([a, b],
            #   Let(x, Assert(b > 0),
            #       Let(y, Assert(a > 5),
            #           Assert(a + b > -1))))
            # --> implicit branching! The last assertion actually can't fail, because the prior asserts must have passed
            # solution: path conditions = all of the conditions under which we get to a certain point in the code

            formula, pc2, avs2 = symb_interp(tst, env, pathcond, avs)
            if satisfiable(pc2 + [NegFExpr(formula)]):
                # NOTE difference: The assertion could fail, but any code after this will only run if it passed, so add it to the path condition
                return formula, pc2 + [formula], avs2 + [(pc2 + [NegFExpr(formula)])]
            else:
                # The assertion must succeed
                return formula, pc2 + [formula], avs2


        case _:
            raise Exception(f"Unknown expr {e}")

def satisfiable(constraints: 'ConstraintSet') -> bool:
    varmap = {}
    s = z3.Solver()
    s.add(*[formula.make_z3(varmap) for formula in constraints])
    # NOTE difference: solver might say "dunno", so the right choice is to check against unsat
    return s.check() != z3.unsat

def get_model(constraints):
    varmap = {}
    s = z3.Solver()
    s.add(*[formula.make_z3(varmap) for formula in constraints])
    assert s.check() != z3.unsat
    return s.model()

