import unittest
import z3

from arith import *

def set_eq(l1, l2):
    if len(l1) != len(l2):
        return False
    for elt in l1:
        if elt not in l2:
            return False
    return True

def make_const(v):
    if isinstance(v, z3.IntNumRef):
        return Num(v.as_long())
    elif isinstance(v, z3.BoolRef):
        return Bool(str(v) == "True")
    elif isinstance(v, z3.StringRef):
        return Str(v.as_string())
def arbitrary_const(typ):
    match typ:
        case BaseType.INT:
            return Num(1000)
        case BaseType.BOOL:
            return Bool(False)

class TestInterp(unittest.TestCase):
    def test_concrete(self):
        self.assertEqual(interp(Num(5), {}),
                         Num(5))
        self.assertEqual(interp(Add(Num(5), Num(-1)), {}),
                         Num(4))
        self.assertEqual(interp(Let("x", BaseType.INT,
                                    Num(0),
                                    Mul(Var("x"), Num(2))),
                                {}),
                         Num(0))
        self.assertEqual(interp(
            Let("f", FunType([BaseType.INT, BaseType.INT],
                             BaseType.INT),
                Fun(["x", "y"],
                    [BaseType.INT, BaseType.INT],
                    Add(Var("x"), Var("y"))),
                App(Var("f"),
                    [Num(5), Add(Num(2), Num(3))])),
            {}),
                         interp(Mul(Num(2), Num(5)), {}))

        # Ideas:
        # Intra-procedural strategy where we basically approximate the results of function calls with new symbolic vars
        # Gas=1000: don't run too long, set a timeout
        # Don't recur into a function we're already inside (don't go down recursive self calls, maybe simplest?)
        # Never symbolic interpret the same code twice if the pathconditions are the same
        #
        # Detect guaranteed infinite loops and stop
        self.assertEqual(symb_exec(
            Fun(["a"],
                [BaseType.INT],
                Let("omega", FunType([BaseType.INT, BaseType.INT],
                                     BaseType.INT),
                    Fun(["x"], [BaseType.INT],
                        If(Stop?,
                           answer,
                           App(Var("x"), Var("x")))),
                    App(Var("omega"), Var("omega"))))),
                         Num(0))


        self.assertEqual(interp(App(Let("x", BaseType.INT, Num(5),
                                        Fun(["y"], [BaseType.INT],
                                            Add(Var("x"), Var("y")))),
                                    [Num(7)]),
                                {}),
                         Num(12))
        self.assertEqual(interp(Let("x", BaseType.INT, Num(100),
                                    App(Let("x", BaseType.INT, Num(5),
                                            Fun(["y"], [BaseType.INT],
                                                Add(Var("x"), Var("y")))),
                                        [Num(7)])),
                                {}),
                         Num(12))


        # --- bools, assert ---
        self.assertEqual(interp(Eq(Num(7), Num(5)),
                                {}),
                         Bool(False))
        self.assertEqual(interp(Lt(Num(2), Num(5)),
                                {}),
                         Bool(True))
        self.assertEqual(interp(Assert(Lt(Num(2), Num(5))),
                                {}),
                         Bool(True))
        with self.assertRaises(AssertionFailure):
            interp(Assert(Not(Lt(Num(2), Num(5)))),
                   {})


    def test_symb_interp(self):
        def symb_interp_t(e):
            f, _, _ = symb_interp(e, {}, [], [])
            return f
        self.assertEqual(symb_interp_t(Num(5)),
                         Num(5))
        self.assertEqual(symb_interp_t(Add(Num(5), Num(-1))),
                         Num(4))
        self.assertEqual(symb_interp_t(Let("x", BaseType.INT,
                                    Num(0),
                                    Mul(Var("x"), Num(2)))),
                         Num(0))
        self.assertEqual(symb_interp_t(
            Let("f", FunType([BaseType.INT, BaseType.INT],
                             BaseType.INT),
                Fun(["x", "y"],
                    [BaseType.INT, BaseType.INT],
                    Add(Var("x"), Var("y"))),
                App(Var("f"),
                    [Num(5), Add(Num(2), Num(3))]))),

                         interp(Mul(Num(2), Num(5)), {}))

        self.assertEqual(symb_interp_t(App(Let("x", BaseType.INT, Num(5),
                                        Fun(["y"], [BaseType.INT],
                                            Add(Var("x"), Var("y")))),
                                    [Num(7)])),

                         Num(12))
        self.assertEqual(symb_interp_t(Let("x", BaseType.INT, Num(100),
                                    App(Let("x", BaseType.INT, Num(5),
                                            Fun(["y"], [BaseType.INT],
                                                Add(Var("x"), Var("y")))),
                                        [Num(7)]))),

                         Num(12))





    def assertSetEq(self, actual, expected, msg=None):
        if not set_eq(actual, expected):
            self.fail(self._formatMessage(msg, f"Assertion violation sets differ:\nactual:   {actual!r}\nvs\nexpected: {expected!r}"))

    # symb_exec `fun`, check that it identifies `num_avs` assertion violation path conditions,
    # and check that executing `fun` with the inputs the SMT solver provides for those
    # path conditions actually causes an assertion violation
    def symb_exec_and_check_avs(self, fun, num_avs):
        f, avs = symb_exec(fun)
        self.assertEqual(len(avs),
                         num_avs,
                         f"Expected {num_avs} assertion violations but got {avs}")
        for av_path in avs:
            model = get_model(av_path)
            param_to_type = {name: typ for name, typ in zip(fun.params, fun.anns)}
            param_to_val = {str(var): make_const(model[var]) for var in model}
            with self.assertRaises(AssertionFailure,
                                   msg=f"Counter-example {model} does not cause an assertion failure!"):
                interp(App(fun,
                           [(param_to_val[name] if name in param_to_val \
                             else arbitrary_const(param_to_type[name])) \
                            for name in fun.params]),
                       {})
        return f, avs



    def test_symb_exec(self):
        self.assertEqual(symb_exec_v1(
            Fun(["a", "b", "c"],
                [BaseType.INT, BaseType.INT, BaseType.INT],
                Let("f", FunType([BaseType.INT, BaseType.INT],
                                 BaseType.INT),
                    Fun(["x", "y"],
                        [BaseType.INT, BaseType.INT],
                        Add(Var("x"), Var("y"))),
                    App(Var("f"),
                        [Var("a"), Add(Var("b"), Var("c"))])))),

                         # a + (b + c)
                         BinFExpr(SymVar("a", BaseType.INT),
                                  BinFExpr(SymVar("b", BaseType.INT), SymVar("c", BaseType.INT), '+'),
                                  '+'))

        self.assertEqual(symb_exec_v1(
            Fun(["a"],
                [BaseType.INT],
                App(Let("x", BaseType.INT, Num(5),
                        Fun(["y"], [BaseType.INT],
                            Mul(Var("x"), Var("y")))),
                    [Var("a")]))),

                         # 5a
                         BinFExpr(Num(5), SymVar("a", BaseType.INT), '*'))
        self.assertEqual(symb_exec_v1(
            Fun(["a"],
                [BaseType.INT],
                Let("x", BaseType.INT, Num(100),
                    App(Let("x", BaseType.INT, Var("a"),
                            Fun(["y"], [BaseType.INT],
                                Sub(Var("x"), Var("y")))),
                        [Num(7)])))),

                         # a - 7
                         BinFExpr(SymVar("a", BaseType.INT), Num(7), '-'))

        # --- bool ops ---
        self.assertEqual(symb_exec_v1(
            Fun(["a"],
                [BaseType.INT],
                Eq(Num(7), Var("a")))),

                         BinFExpr(Num(7), SymVar("a", BaseType.INT), '='))
        self.assertEqual(symb_exec_v1(
            Fun(["a"],
                [BaseType.BOOL],
                And(Bool(True), Var("a")))),

                         BinFExpr(Bool(True), SymVar("a", BaseType.BOOL), 'and'))







        # --- assert ---
        # Note `Seq(e1, e2)` == `Let("dummy", INT, e1, e2)`
        f, assertion_violation_pathconds = symb_exec(
            Fun(['x', 'y'],
                [BaseType.INT, BaseType.INT],
                BiNumOp(Var('x'), Num(2), lambda x, y: x * y, '*')))
        self.assertEqual(f, BinFExpr(SymVar('x', BaseType.INT), Num(2), '*'))
        self.assertEqual(assertion_violation_pathconds,

                         [])

        f, assertion_violation_pathconds = self.symb_exec_and_check_avs(
            Fun(['x', 'y'],
                [BaseType.INT, BaseType.INT],
                Seq(Assert(Eq(Var('x'), Num(0))),
                    Mul(Var('x'), Num(2)))),
            1)
        self.assertEqual(f, BinFExpr(SymVar('x', BaseType.INT), Num(2), '*'))
        self.assertEqual(assertion_violation_pathconds,

                         [[NegFExpr(BinFExpr(SymVar('x', BaseType.INT), Num(0), '='))]])

        f, avs = self.symb_exec_and_check_avs(
            Fun(['x', 'y'],
                [BaseType.INT, BaseType.INT],
                Seq(Assert(Eq(Var('x'), Num(0))),
                    Let('z', BaseType.INT, Mul(Var('x'), Num(2)),
                        Assert(Gt(Var('z'), Num(1)))))),
            2)
        self.assertSetEq(avs,
                         [[NegFExpr(BinFExpr(SymVar('x', BaseType.INT), Num(0), '='))],

                          [BinFExpr(SymVar('x', BaseType.INT), Num(0), '='),
                           NegFExpr(BinFExpr(BinFExpr(SymVar('x', BaseType.INT), Num(2), '*'), Num(1), '>'))]])

        f, avs = self.symb_exec_and_check_avs(
            Fun(['I'],
                [BaseType.INT],
                Let(
                    'f', None, Fun(['x'], [BaseType.INT],
                                   Seq(Assert(Lt(Var('x'), Num(5))),
                                       Add(Var('x'), Num(1)))),
                    App(Var('f'), [Var('I')])
                )),
            1)
        self.assertSetEq(avs,
                         [[NegFExpr(BinFExpr(SymVar('I', BaseType.INT), Num(5), '<'))]])




        # --- If ---
        f, avs = self.symb_exec_and_check_avs(
            Fun(['a', 'b'],
                [BaseType.INT, BaseType.INT],
                If(Lt(Var('a'), Var('b')),
                   Assert(Neq(Var('a'), Var('b'))),
                   Bool(False))),
            0)
        f, avs = self.symb_exec_and_check_avs(
            Fun(['a', 'b'],
                [BaseType.INT, BaseType.INT],
                If(Lt(Var('a'), Var('b')),
                   Bool(False),
                   Assert(Neq(Var('a'), Var('b'))))),
             1)
        f, avs = self.symb_exec_and_check_avs(
            Fun(['a', 'b'],
                [BaseType.INT, BaseType.INT],
                If(Lt(Var('a'), Var('b')),
                   If(Eq(Var('a'), Var('b')),
                      Assert(Eq(Var('a'), Num(0))),
                      Bool(False)),
                   Bool(False))),
             0)
        f, avs = self.symb_exec_and_check_avs(
            Fun(['a', 'b'],
                [BaseType.INT, BaseType.INT],
                If(Lt(Var('a'), Var('b')),
                   If(Eq(Var('a'), Var('b')),
                      Bool(False),
                      Assert(Eq(Var('a'), Num(0)))),
                   Bool(False))),
             1)
        f, avs = self.symb_exec_and_check_avs(
            Fun(['a', 'b'],
                [BaseType.INT, BaseType.INT],
                Seq(If(Lt(Var('a'), Var('b')),
                       Assert(Eq(Var('b'), Num(0))),
                       Bool(False)),
                    If(Gt(Var('b'), Num(5)),
                       Bool(False),
                       Assert(Eq(Var('a'), Num(5)))))),
            # We can...
            #
            # take the then branch of the first conditional. In that case...
            #   Hit the first assert. It could...
            #   Pass:
            #     Then we can take the then branch of the second conditional:
            #       all good
            #     Then we can take the else branch of the second conditional:
            #       a < b & b = 0 & !(b > 5) && !(a = 5) -- possible 1
            #    Fail:
            #      a < b && !(b = 0) -- possible 1
            #
            # ======= unsoundness strikes again! We didn't explore this whole set of paths ======
            # take the else branch of the first conditional. In that case...
            #   Take the then branch of the second conditional. In that case...
            #     Nothing happened.
            #   Take the else branch of the second conditional. In that case...
            #     Hit second assert. It could...
            #     !(a < 5) & !(b > 5) & !(a = 5) -- possible 1
            #
            #
            # Note to self the sound answer is 3, but we're not sound :)
            2)


if __name__ == "__main__":
    unittest.main()

