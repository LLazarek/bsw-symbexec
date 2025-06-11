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

        # self.assertEqual(interp(
        #     Let("omega", FunType([BaseType.INT, BaseType.INT],
        #                          BaseType.INT),
        #         Fun(["x"], [BaseType.INT], App(Var("x"), Var("x"))),
        #         App(Var("omega"), Var("omega")))),
        #                  Num(0))


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
        f, asservtion_violation_pathconds = self.symb_exec_and_check_avs(
            Fun(['x', 'y'],
                [BaseType.INT, BaseType.INT],
                Let("_", BaseType.BOOL, Assert(Eq(Var('x'), Num(0))),
                    Mul(Var('x'), Num(2)))),
            1)
        self.assertEqual(f, BinFExpr(SymVar('x', BaseType.INT), Num(2), '*'))
        self.assertEqual(asservtion_violation_pathconds,
                         [[NegFExpr(BinFExpr(SymVar('x', BaseType.INT), Num(0), '='))]])

        f, avs = self.symb_exec_and_check_avs(
            Fun(['x', 'y'],
                [BaseType.INT, BaseType.INT],
                Let("_", BaseType.BOOL, Assert(Eq(Var('x'), Num(0))),
                    Let('z', BaseType.INT, Mul(Var('x'), Num(2)),
                        Assert(Gt(Var('z'), Num(1)))))),
            2)
        self.assertSetEq(avs,
                         [[NegFExpr(BinFExpr(SymVar('x', BaseType.INT), Num(0), '='))],

                          [BinFExpr(SymVar('x', BaseType.INT), Num(0), '='),
                           NegFExpr(BinFExpr(BinFExpr(SymVar('x', BaseType.INT),
                                                      Num(2),
                                                      '*'),
                                             Num(1),
                                             '>'))]])


if __name__ == "__main__":
    unittest.main()

