import unittest

from arith import *

class TestInterp(unittest.TestCase):
    def test_thing(self):
        self.assertEqual(interp(Num(5), {}),
                         Num(5))
    def test_thing2(self):
        self.assertEqual(interp(Add(Num(5), Num(-1)), {}),
                         Num(4))
    def test_thing3(self):
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


        # App(Let("x", 5, Fun(["y"], Add(x, y))), 7) == 12
        # Let("x", 100, App(Let("x", 5, Fun(["y"], Add(x, y))), 7)) == 12

if __name__ == "__main__":
    unittest.main()

