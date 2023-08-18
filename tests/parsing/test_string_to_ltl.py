from unittest import TestCase

from parsing.string_to_ltl import string_to_ltl


class Test(TestCase):
    def test_string_to_ltl_00(self):
        ltl = string_to_ltl("a | !a & p")
        print(ltl)
        ltl = string_to_ltl("(a & (a | (a | (a | (a | ((a | (a | (a | (a | !aa)))) | !a))))) | !a & (a & ((a | (a | (a | ((a & (a | aa) | !a & (a & aa)) | !a)))) | !a) | !a) & (a & (a | (a & (a | (a | (a | (a | (aa | !a))))) | !a & ((a & (a | (a & (a | aa) | !a & (a & aa))) | !a & (a | (a | aa))) | !a))) | !a & (a & (a | (a | (a | (a | (a | (aa | !a)))))) | !a & (a | ((a | (a | (a | aa))) | !a)))))")
        print(ltl)
        ltl = string_to_ltl("a | !a | p")
        print(ltl)
        ltl = string_to_ltl("a & a | !a")
        print(ltl)
        ltl = string_to_ltl("p & q -> r")
        print(ltl)
        ltl = string_to_ltl("p -> q & q")
        print(ltl)
        ltl = string_to_ltl("p -> (q & q) -> p")
        print(ltl)
        if ltl is None:
            self.fail()

    def test_string_to_ltl_1(self):
        ltl = string_to_ltl("(a) & (a)")
        print(ltl)
        if ltl is None:
            self.fail()

    def test_string_to_ltl_2(self):
        ltl = string_to_ltl("G (a) & (a)")
        print(ltl)
        if ltl is None:
            self.fail()

    def test_string_to_ltl_3(self):
        ltl = string_to_ltl("G (a & a)")
        print(ltl)
        if ltl is None:
            self.fail()

    def test_string_to_ltl_3(self):
        ltl = string_to_ltl("G (A && A)")
        print(ltl)
        if ltl is None:
            self.fail()

    def test_string_to_ltl_4(self):
        ltl = string_to_ltl("F (ROOMCLEAN && (X F !INROOM) && (X F ! DOORLOCKED))")
        print(ltl)
        if ltl is None:
            self.fail()

    def test_string_to_ltl_5(self):
        ltl = string_to_ltl("(((done2 & !room1) | (done1 & room1)) & granting)")
        print(ltl)
        if ltl is None:
            self.fail()

    def test_string_to_ltl_6(self):
        ltl = string_to_ltl(
            "((request & (! decrement)) | ((! request) & (! decrement)) | (decrement & (! request)) | (decrement & request))")
        print(ltl)
        if ltl is None:
            self.fail()
