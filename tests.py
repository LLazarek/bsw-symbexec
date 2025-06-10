import unittest

from arith import *

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


    def test_symb(self):
        self.assertEqual(symb_interp(Num(5), {}),
                         Num(5))
        self.assertEqual(symb_interp(Add(Num(5), Num(-1)), {}),
                         Num(4))
        self.assertEqual(symb_interp(Let("x", BaseType.INT,
                                    Num(0),
                                    Mul(Var("x"), Num(2))),
                                {}),
                         Num(0))
        self.assertEqual(symb_interp(
            Let("f", FunType([BaseType.INT, BaseType.INT],
                             BaseType.INT),
                Fun(["x", "y"],
                    [BaseType.INT, BaseType.INT],
                    Add(Var("x"), Var("y"))),
                App(Var("f"),
                    [Num(5), Add(Num(2), Num(3))])),
            {}),
                         interp(Mul(Num(2), Num(5)), {}))

        self.assertEqual(symb_interp(App(Let("x", BaseType.INT, Num(5),
                                        Fun(["y"], [BaseType.INT],
                                            Add(Var("x"), Var("y")))),
                                    [Num(7)]),
                                {}),
                         Num(12))
        self.assertEqual(symb_interp(Let("x", BaseType.INT, Num(100),
                                    App(Let("x", BaseType.INT, Num(5),
                                            Fun(["y"], [BaseType.INT],
                                                Add(Var("x"), Var("y")))),
                                        [Num(7)])),
                                {}),
                         Num(12))

if __name__ == "__main__":
    unittest.main()

