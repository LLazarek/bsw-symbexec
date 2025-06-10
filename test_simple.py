import unittest

from simple import *

class TestInterp(unittest.TestCase):
    def setUp(self):
        self.empty_env = {}
        self.empty_store = {}

    def test_num(self):
        v, s = interp(Num(5), self.empty_env, self.empty_store)
        self.assertEqual(v, Num(5))
        self.assertEqual(s, self.empty_store)

    def test_bi_num_op(self):
        expr = BiNumOp(Num(2), Num(3), lambda x, y: x + y, '+')
        v, s = interp(expr, self.empty_env, self.empty_store)
        self.assertEqual(v, Num(5))

    def test_var(self):
        env = {'x': Num(7)}
        v, s = interp(Var('x'), env, self.empty_store)
        self.assertEqual(v, Num(7))

    def test_let(self):
        expr = Let('x', None, Num(10), BiNumOp(Var('x'), Num(2), lambda x, y: x * y, '*'))
        v, s = interp(expr, self.empty_env, self.empty_store)
        self.assertEqual(v, Num(20))

    def test_bool(self):
        v, s = interp(Bool(True), self.empty_env, self.empty_store)
        self.assertEqual(v, Bool(True))

    def test_if_true(self):
        expr = If(Bool(True), Num(1), Num(2))
        v, s = interp(expr, self.empty_env, self.empty_store)
        self.assertEqual(v, Num(1))

    def test_if_false(self):
        expr = If(Bool(False), Num(1), Num(2))
        v, s = interp(expr, self.empty_env, self.empty_store)
        self.assertEqual(v, Num(2))

    def test_bi_num_cmp(self):
        expr = BiNumCmp(Num(2), Num(3), lambda x, y: x < y, '<')
        v, s = interp(expr, self.empty_env, self.empty_store)
        self.assertEqual(v, Bool(True))

    def test_bool_op(self):
        expr = BoolOp(Bool(True), Bool(False), lambda x, y: x and y, 'and')
        v, s = interp(expr, self.empty_env, self.empty_store)
        self.assertEqual(v, Bool(False))

    def test_str(self):
        v, s = interp(Str("hi"), self.empty_env, self.empty_store)
        self.assertEqual(v, Str("hi"))

    def test_concat(self):
        expr = Concat(Str("a"), Str("b"))
        v, s = interp(expr, self.empty_env, self.empty_store)
        self.assertEqual(v, Str("ab"))

    def test_str_eq(self):
        expr = StrEq(Str("a"), Str("a"))
        v, s = interp(expr, self.empty_env, self.empty_store)
        self.assertEqual(v, Bool(True))

    def test_fun_and_app(self):
        fun = Fun(['x'], [BaseType.INT], BiNumOp(Var('x'), Num(1), lambda x, y: x + y, '+'))
        app = App(fun, [Num(5)])
        v, s = interp(app, self.empty_env, self.empty_store)
        self.assertEqual(v, Num(6))

    def test_box_get_set(self):
        # Entire program: let b = box(42); set(b, 99); get(b)
        expr = Let(
            'b', None, Box(Num(42)),
            Seq(Set(Var('b'), Num(99)),
                Get(Var('b'))
            )
        )
        v, s = interp(expr, self.empty_env, self.empty_store)
        self.assertEqual(v, Num(99))

    def test_seq(self):
        expr = Seq(Num(1), Num(2))
        v, s = interp(expr, self.empty_env, self.empty_store)
        self.assertEqual(v, Num(2))

    def test_assert_true(self):
        expr = Assert(Bool(True))
        v, s = interp(expr, self.empty_env, self.empty_store)
        self.assertEqual(v, Bool(True))

    def test_assert_false_raises(self):
        expr = Assert(Bool(False))
        with self.assertRaises(Exception):
            interp(expr, self.empty_env, self.empty_store)

    def test_nested_let_fun_app(self):
        # let x = 10 in let f = fun y -> x + y in f(5)
        expr = Let(
            'x', None, Num(10),
            Let(
                'f', None, Fun(['y'], [BaseType.INT], BiNumOp(Var('x'), Var('y'), lambda x, y: x + y, '+')),
                App(Var('f'), [Num(5)])
            )
        )
        v, s = interp(expr, self.empty_env, self.empty_store)
        self.assertEqual(v, Num(15))

    def test_box_fun_set_get(self):
        # let b = box(1) in let inc = fun _ -> set(b, BiNumOp(get(b), Num(1), +)) in
        # inc(); inc(); get(b)
        expr = Let(
            'b', None, Box(Num(1)),
            Let(
                'inc', None, Fun(['_'], [BaseType.INT],
                    Set(Var('b'), BiNumOp(Get(Var('b')), Num(1), lambda x, y: x + y, '+'))
                ),
                Seq(
                    App(Var('inc'), [Num(0)]),
                    Seq(
                        App(Var('inc'), [Num(0)]),
                        Get(Var('b'))
                    )
                )
            )
        )
        v, s = interp(expr, self.empty_env, self.empty_store)
        self.assertEqual(v, Num(3))

    def test_if_with_let_and_fun(self):
        # if (let x = 5 in x < 10) then (fun y -> y + 1)(2) else 0
        expr = If(
            Let('x', None, Num(5), BiNumCmp(Var('x'), Num(10), lambda x, y: x < y, '<')),
            App(Fun(['y'], [BaseType.INT], BiNumOp(Var('y'), Num(1), lambda x, y: x + y, '+')), [Num(2)]),
            Num(0)
        )
        v, s = interp(expr, self.empty_env, self.empty_store)
        self.assertEqual(v, Num(3))

    def test_str_concat_in_fun_and_if(self):
        # let greet = fun name -> "hi, " + name in
        # if true then greet("bob") else "bye"
        expr = Let(
            'greet', None, Fun(['name'], [BaseType.STR], Concat(Str("hi, "), Var('name'))),
            If(
                Bool(True),
                App(Var('greet'), [Str("bob")]),
                Str("bye")
            )
        )
        v, s = interp(expr, self.empty_env, self.empty_store)
        self.assertEqual(v, Str("hi, bob"))

    def test_assert_in_fun_and_seq(self):
        # let f = fun x -> assert(x < 5); x + 1 in f(3)
        expr = Let(
            'f', None, Fun(['x'], [BaseType.INT],
                Seq(
                    Assert(BiNumCmp(Var('x'), Num(5), lambda x, y: x < y, '<')),
                    BiNumOp(Var('x'), Num(1), lambda x, y: x + y, '+')
                )
            ),
            App(Var('f'), [Num(3)])
        )
        v, s = interp(expr, self.empty_env, self.empty_store)
        self.assertEqual(v, Num(4))

    def test_assert_in_fun_and_seq_raises(self):
        # let f = fun x -> assert(x < 5); x + 1 in f(7)
        expr = Let(
            'f', None, Fun(['x'], [BaseType.INT],
                Seq(
                    Assert(BiNumCmp(Var('x'), Num(5), lambda x, y: x < y, '<')),
                    BiNumOp(Var('x'), Num(1), lambda x, y: x + y, '+')
                )
            ),
            App(Var('f'), [Num(7)])
        )
        with self.assertRaises(Exception):
            interp(expr, self.empty_env, self.empty_store)

    def test_shadowing_in_let(self):
        # let x = 10 in let x = 20 in x + 5
        expr = Let(
            'x', None, Num(10),
            Let(
                'x', None, Num(20),
                BiNumOp(Var('x'), Num(5), lambda x, y: x + y, '+')
            )
        )
        v, s = interp(expr, self.empty_env, self.empty_store)
        self.assertEqual(v, Num(25))

    def test_closure_capture(self):
        # let x = 10 in let f = fun y -> x + y in f(5)
        expr = Let(
            'x', None, Num(10),
            Let(
                'f', None, Fun(['y'], [BaseType.INT], BiNumOp(Var('x'), Var('y'), lambda x, y: x + y, '+')),
                App(Var('f'), [Num(5)])
            )
        )
        v, s = interp(expr, self.empty_env, self.empty_store)
        self.assertEqual(v, Num(15))

    def test_box_in_fun(self):
        # let b = box(1) in
        # let inc = fun _ -> set(b, BiNumOp(get(b), Num(1), +)) in
        # inc(); get(b)
        expr = Let(
            'b', None, Box(Num(1)),
            Let(
                'inc', None, Fun(['_'], [BaseType.INT],
                    Set(Var('b'), BiNumOp(Get(Var('b')), Num(1), lambda x, y: x + y, '+'))
                ),
                Seq(
                    App(Var('inc'), [Num(0)]),
                    Get(Var('b'))
                )
            )
        )
        v, s = interp(expr, self.empty_env, self.empty_store)
        self.assertEqual(v, Num(2))

    def test_box_aliasing(self):
        # let b1 = box(1) in
        # let b2 = b1 in
        # set(b2, Num(2)); get(b1)
        expr = Let(
            'b1', None, Box(Num(1)),
            Let(
                'b2', None, Var('b1'),
                Seq(
                    Set(Var('b2'), Num(2)),
                    Get(Var('b1'))
                )
            )
        )
        v, s = interp(expr, self.empty_env, self.empty_store)
        self.assertEqual(v, Num(2))
    
    def test_nested_boxes(self):
        # let b1 = box(box(1)) in
        # let b2 = get(b1) in
        # set(b2, Num(2)); get(get(b1))
        expr = Let(
            'b1', None, Box(Box(Num(1))),
            Let(
                'b2', None, Get(Var('b1')),
                Seq(
                    Set(Var('b2'), Num(2)),
                    Get(Get(Var('b1')))
                )
            )
        )
        v, s = interp(expr, self.empty_env, self.empty_store)
        self.assertEqual(v, Num(2))

    def test_unbound_variable(self):
        # Attempt to use an unbound variable
        expr = Var('x')
        with self.assertRaises(Exception):
            interp(expr, self.empty_env, self.empty_store)

def set_eq(l1, l2):
    if len(l1) != len(l2):
        return False
    for elt in l1:
        if elt not in l2:
            return False
    return True

class TestSymbInterp(unittest.TestCase):
    def setUp(self):
        self.empty_env = {}
        self.empty_store = {}

    def test_direct(self):
        f, _, _, avs = symb_interp(Num(5), {}, {}, [])
        self.assertEqual(f, Num(5))
        self.assertEqual(avs, [])
        f, _, _, avs = symb_interp(BiNumOp(Num(2), Num(3), lambda x, y: x + y, '+'),
                                   {}, {}, [])
        self.assertEqual(f, Num(5))
        self.assertEqual(avs, [])
        f, _, _, avs = symb_interp(Let('x', None, Num(10), BiNumOp(Var('x'), Num(2), lambda x, y: x * y, '*')),
                                   {}, {}, [])
        self.assertEqual(f, Num(20))
        self.assertEqual(avs, [])
        f, _, _, avs = symb_interp(BiNumOp(SymVar('x', BaseType.INT), Num(2), lambda x, y: x * y, '*'),
                                   {}, {}, [])
        self.assertEqual(f, BinFExpr(SymVar('x', BaseType.INT), Num(2), '*'))
        self.assertEqual(avs, [])

    def assertSetEq(self, actual, expected, msg=None):
        if not set_eq(actual, expected):
            self.fail(self._formatMessage(msg, f"Assertion violation sets differ:\nactual:   {actual!r}\nvs\nexpected: {expected!r}"))

    def symb_exec_and_check_avs(self, fun, num_avs):
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
        f, _, _, avs = symb_exec(fun)
        self.assertEqual(len(avs), num_avs, f"Expected {num_avs} assertion violations but got {avs}")
        for av_path in avs:
            model = get_model(av_path)
            param_to_type = {name: typ for name, typ in zip(fun.params, fun.anns)}
            param_to_val = {str(var): make_const(model[var]) for var in model}
            with self.assertRaises(AssertionFailure, msg=f"Counter-example {model} does not cause an assertion failure!"):
                interp(App(fun, [(param_to_val[name] if name in param_to_val else arbitrary_const(param_to_type[name])) \
                                 for name in fun.params]),
                       {}, {})
        return f, avs

    def test_exec(self):
        f, _, _, avs = symb_exec(Fun(['x', 'y'],
                                     [BaseType.INT, BaseType.INT],
                                     BiNumOp(Var('x'), Num(2), lambda x, y: x * y, '*')))
        self.assertEqual(f, BinFExpr(SymVar('x', BaseType.INT), Num(2), '*'))
        self.assertEqual(avs, [])

        f, avs = self.symb_exec_and_check_avs(
            Fun(['x', 'y'],
                [BaseType.INT, BaseType.INT],
                Seq(Assert(BiNumCmp(Var('x'), Num(0), lambda x, y: x == y, '=')),
                    BiNumOp(Var('x'), Num(2), lambda x, y: x * y, '*'))),
            1)
        self.assertEqual(f, BinFExpr(SymVar('x', BaseType.INT), Num(2), '*'))
        self.assertEqual(avs, [[NegFExpr(BinFExpr(SymVar('x', BaseType.INT), Num(0), '='))]])

        f, avs = self.symb_exec_and_check_avs(
            Fun(['x', 'y'],
                [BaseType.INT, BaseType.INT],
                Seq(Assert(BiNumCmp(Var('x'), Num(0), lambda x, y: x == y, '=')),
                    Let('z', BaseType.INT, BiNumOp(Var('x'), Num(2), lambda x, y: x * y, '*'),
                        Assert(BiNumCmp(Var('z'), Num(1), lambda a, b: a > b, '>'))))),
            2)
        self.assertSetEq(avs, [[NegFExpr(BinFExpr(SymVar('x', BaseType.INT), Num(0), '='))],
                               [BinFExpr(SymVar('x', BaseType.INT), Num(0), '='),
                                NegFExpr(BinFExpr(BinFExpr(SymVar('x', BaseType.INT), Num(2), '*'), Num(1), '>'))]])

        f, avs = self.symb_exec_and_check_avs(
            Fun(['I'],
                [BaseType.INT],
                Let(
                    'f', None, Fun(['x'], [BaseType.INT],
                                   Seq(
                                       Assert(BiNumCmp(Var('x'), Num(5), lambda x, y: x < y, '<')),
                                       BiNumOp(Var('x'), Num(1), lambda x, y: x + y, '+')
                                   )
                                   ),
                    App(Var('f'), [Var('I')])
                )),
            1)
        self.assertSetEq(avs, [[NegFExpr(BinFExpr(SymVar('I', BaseType.INT), Num(5), '<'))]])
        f, avs = self.symb_exec_and_check_avs(
            Fun(['I'],
                [BaseType.INT],
                Let(
                    'b', None, Box(Num(1)),
                    Let(
                        'inc', None, Fun(['_'], [BaseType.INT],
                                         Set(Var('b'), BiNumOp(Get(Var('b')), Num(1), lambda x, y: x + y, '+'))
                                         ),
                        Seq(
                            App(Var('inc'), [Num(0)]),
                            Seq(
                                App(Var('inc'), [Num(0)]),
                                Assert(BiNumCmp(Get(Var('b')), Var('I'), lambda a, b: a == b, '='))
                            )
                        )
                    )
                )),
            1)
        self.assertSetEq(avs, [[NegFExpr(BinFExpr(Num(3), SymVar('I', BaseType.INT), '='))]])



        f, avs = self.symb_exec_and_check_avs(
            Fun(['a', 'b'],
                [BaseType.INT, BaseType.INT],
                Let('x', BaseType.INT, Box(Num(1)),
                    Let('y', BaseType.INT, Box(Num(0)),
                        Seq(If(Neq(Var('a'), Num(0)),
                               Seq(Set(Var('y'), Add(Num(3), Get(Var('x')))),
                                                        If(Eq(Var('b'), Num(0)),
                                                           Seq(Set(Var('x'), Mul(Num(2), Add(Var('a'), Var('b')))),
                                                               Bool(False)),
                                                           Bool(False))),
                               Bool(False)),
                            Assert(Neq(Sub(Get(Var('x')), Get(Var('y'))), Num(0),)))))),
            1)
        self.assertSetEq(avs, [[
            BinFExpr(SymVar('a', BaseType.INT), Num(0), '!='), # a != 0
            BinFExpr(SymVar('b', BaseType.INT), Num(0), '='),  # b == 0
            # ! (2*(a + b) - 4 != 0)
            # ie 2*(a + b) - 4 == 0
            NegFExpr(BinFExpr(BinFExpr(BinFExpr(Num(2),
                                                BinFExpr(SymVar('a', BaseType.INT),
                                                         SymVar('b', BaseType.INT),
                                                         '+'),
                                                '*'),
                                       Num(4),
                                       '-'),
                              Num(0),
                              '!='))]]
)

        cook_the_books()
        f, avs = self.symb_exec_and_check_avs(
            Fun(['a', 'b', 'c'],
                [BaseType.BOOL, BaseType.INT, BaseType.BOOL],
                Let('x', BaseType.INT, Box(Num(0)),
                    Let('y', BaseType.INT, Box(Num(0)),
                        Let('z', BaseType.INT, Box(Num(0)),
                            Seq(If(Var('a'),
                                   Set(Var('x'), Num(-2)),
                                   Bool(False)),
                                Seq(If(Lt(Var('b'), Num(5)),
                                       Seq(If(And(Not(Var('a')),
                                                  Var('c')),
                                              Set(Var('y'), Num(1)),
                                              Bool(False)),
                                           Set(Var('z'), Num(2))),
                                       Bool(False)),
                                    Assert(Neq(Add(Get(Var('x')),
                                                   Add(Get(Var('y')),
                                                       Get(Var('z')))),
                                               Num(3))))))))),
            1)




if __name__ == "__main__":
    unittest.main()
