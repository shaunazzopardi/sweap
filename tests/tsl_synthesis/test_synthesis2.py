from unittest import TestCase

from prop_lang.util import conjunct_formula_set, implies
from synthesis.synthesis import abstract_synthesis_loop, synthesize
from parsing.string_to_ltlmt import ToProgram, string_to_ltlmt
from programs.typed_valuation import TypedValuation
from prop_lang.variable import Variable


class Test(TestCase):
    def test_abstract_synthesis_loop(self):
        ltlmt_formula = "(!(x > 0) && !(x < 0)) -> (G([x := x + 1]) & F(!(x > 5) && !(x < 5)))"
        ltlmt = string_to_ltlmt(ltlmt_formula)

        boolean_in_acts = []
        boolean_out_acts = [Variable("a")]
        state_vars = [Variable("x")]

        symbol_table = {}
        symbol_table["a"] = TypedValuation("a", "bool", None)
        symbol_table["x"] = TypedValuation("x", "int", None)

        real, _ = abstract_synthesis_loop(ltlmt, boolean_in_acts, [], boolean_out_acts, state_vars, symbol_table)
        self.assertTrue(real)

    def test_repeated_reachability(self):
        ltlmt_formula = "(0 <= x) -> (F(x < 0) & G([x := x + 1] | [x := x - 1]))"
        ltlmt = string_to_ltlmt(ltlmt_formula)

        boolean_in_acts = []
        boolean_out_acts = []
        state_vars = [Variable("x")]

        symbol_table = {}
        symbol_table["x"] = TypedValuation("x", "int", None)

        real, _ = abstract_synthesis_loop(ltlmt, boolean_in_acts, [], boolean_out_acts, state_vars, symbol_table)
        self.assertTrue(real)


    def test_repeated_reachability2(self):
        ltlmt_formula = ("(target = 0 & x = 0 & G(no > 0)) -> (X F x == target & " + \
                         "G((x > target || x < target) -> ([target := target])) &&" + \
                         "G(!(x > target || x < target) -> ([target := no])) &&" + \
                         "G([x := x + 1] | [x := x - 1] | [x := x]) &&" + \
                         "G((target > x & ([x := x + 1] && [target := target]) W (x == target)) -> F x == target) &&" + \
                         "G((target < x & ([x := x - 1] && [target := target]) W (x == target)) -> F x == target))"
                         )
        # ltlmt_formula = ("(target = 0 & x = 0 & G(no > 0)) -> (X F !(x > target || x < target) & " + \
        #                  "G((x > target || x < target) -> ([target := target])) &&" + \
        #                  "G(!(x > target || x < target) -> ([x := 0] & [target := no])) &&" + \
        #                  "G([x := x + 1]))")
        ltlmt = string_to_ltlmt(ltlmt_formula)

        boolean_in_acts = []
        boolean_out_acts = []
        state_vars = [Variable("x"), Variable("target")]
        numerical_in_acts = [Variable("no")]

        symbol_table = {}
        symbol_table["no"] = TypedValuation("no", "int", None)
        symbol_table["target"] = TypedValuation("target", "int", None)
        symbol_table["x"] = TypedValuation("x", "int", None)

        real, _ = abstract_synthesis_loop(ltlmt, boolean_in_acts, numerical_in_acts, boolean_out_acts, state_vars, symbol_table)
        self.assertTrue(real)

    def test_arbiter(self):
        ltlmt_formula = """(G(no > 0) && G F tasks_set) -> ((tasks == 0) -> (G ( 
                                                ((tasks_set && tasks <= 0) -> [tasks := no]) &
                                                (!(tasks_set && tasks <= 0) -> ([tasks := tasks] | ([tasks := tasks - 1]))) &
                                                F tasks <= 0)))"""
        ltlmt = string_to_ltlmt(ltlmt_formula)

        boolean_in_acts = [Variable("tasks_set")]
        numerical_in_acts = [Variable("no")]
        boolean_out_acts = []
        state_vars = [Variable("tasks")]  # , Variable("max")]

        symbol_table = {}
        symbol_table["tasks_set"] = TypedValuation("tasks_set", "bool", None)
        symbol_table["no"] = TypedValuation("no", "int", None)
        symbol_table["tasks"] = TypedValuation("tasks", "int", None)

        real, _ = abstract_synthesis_loop(ltlmt, boolean_in_acts, numerical_in_acts, boolean_out_acts, state_vars,
                                          symbol_table)
        self.assertTrue(real)

    def test_abstract_synthesis_loop_env(self):
        ltlmt_formula = "(x = 0) -> (G([x := x + 1]) & F(x == 5))"
        ltlmt = string_to_ltlmt(ltlmt_formula)

        boolean_in_acts = []
        boolean_out_acts = [Variable("a")]
        state_vars = [Variable("x")]

        symbol_table = {}
        symbol_table["a"] = TypedValuation("a", "bool", None)
        symbol_table["x"] = TypedValuation("x", "int", None)

        real, _ = abstract_synthesis_loop(ltlmt, boolean_in_acts, [], boolean_out_acts, state_vars, symbol_table)
        self.assertTrue(real)

    def test_abstract_synthesis_loop_env2(self):
        ltlmt_formula = "G(x > 5 <-> !(x < 5)) -> (!(x < 0 | x > 0) -> (G([x := x + 1]) & F!(x > 5 | x < 5)))"
        ltlmt = string_to_ltlmt(ltlmt_formula)

        boolean_in_acts = []
        boolean_out_acts = [Variable("a")]
        state_vars = [Variable("x")]

        symbol_table = {}
        symbol_table["a"] = TypedValuation("a", "bool", None)
        symbol_table["x"] = TypedValuation("x", "int", None)

        real, _ = abstract_synthesis_loop(ltlmt, boolean_in_acts, [], boolean_out_acts, state_vars, symbol_table)
        self.assertTrue(real)

    def test_repeated_reachability_env(self):
        ltlmt_formula = "0 <= x -> (F(x < 0) & G([x := x + 1] | [x := x - 1]))"
        ltlmt = string_to_ltlmt(ltlmt_formula)

        boolean_in_acts = []
        boolean_out_acts = []
        state_vars = [Variable("x")]

        symbol_table = {}
        symbol_table["x"] = TypedValuation("x", "int", None)

        real, _ = abstract_synthesis_loop(ltlmt, boolean_in_acts, [], boolean_out_acts, state_vars, symbol_table)
        self.assertTrue(real)

    def test_arbiter_env(self):
        ltlmt_formula = """((tasks = 0) & G(no > 0 & (tasks != 0 -> !tasks_set))) -> 
		((G ((tasks_set -> [tasks := no]) &
             (!tasks_set -> ([tasks := tasks] | (tasks > 0 & [tasks := tasks - 1]))) &
              F tasks == 0 &
					tasks >= 0)))"""
        ltlmt = string_to_ltlmt(ltlmt_formula)

        boolean_in_acts = [Variable("tasks_set")]
        numerical_in_acts = [Variable("no")]
        boolean_out_acts = []
        state_vars = [Variable("tasks")]#, Variable("max")]

        symbol_table = {}
        symbol_table["tasks_set"] = TypedValuation("tasks_set", "bool", None)
        symbol_table["no"] = TypedValuation("no", "int", None)
        symbol_table["tasks"] = TypedValuation("tasks", "int", None)

        real, _ = abstract_synthesis_loop(ltlmt, boolean_in_acts, numerical_in_acts, boolean_out_acts, state_vars, symbol_table)
        self.assertTrue(real)

    def test_elevator(self):
        # TODO signal is not recognized as a variable
        ltlmt_formula = """(at_floor > 0 & at_floor < max + 1 & target = 0 &
                            G(signal > -1 & signal < max + 1 & (target != 0 -> signal = 0))) -> G(
                            ([at_floor := at_floor] | [at_floor := at_floor - 1] | [at_floor := at_floor + 1]) &
                            ((signal != 0 & (at_floor > target | at_floor < target)) -> [target := signal]) &
                            ((signal = 0 & (at_floor > target | at_floor < target)) -> [target := target]) &
                            at_floor >= 1 & at_floor < max + 1 & (F ((target != 0 -> !(at_floor > target | at_floor < target)))))"""
        ltlmt = string_to_ltlmt(ltlmt_formula.replace("max", "3"))
        tp = ToProgram()
        tp.walk(ltlmt)
        prog, ltl = tp.generateProgram(ltlmt)
        print(prog.to_prog(ltl))

        real, mm = synthesize(prog, ltl, None, False)
        self.assertTrue(real)
        print(mm)


    # def test_elevator1(self):
    #     ltlmt_formula = """(at_floor = 0 & target = 0 & signal = 0 &
    #                         G(signal >= 0 & signal <= max_floor & max_floor = 3)) -> G(
    #                         ([at_floor := at_floor] | [at_floor := at_floor - 1] | [at_floor := at_floor + 1]) &
    #                         ((at_floor != target) <-> [target := target]) &
    #                         ((at_floor == target) <-> ([target := signal])) &
    #                         at_floor >= 1 & at_floor <= max_floor & (target != 0 -> F (!(at_floor > target | at_floor < target))))"""
    #     ltlmt = string_to_ltlmt(ltlmt_formula)
    #     # ltlmt = string_to_ltlmt(ltlmt_formula.replace("max", "3"))

    #     boolean_in_acts = []
    #     numerical_in_acts = [Variable("signal")]
    #     boolean_out_acts = []
    #     state_vars = [Variable("max_floor"), Variable("target"), Variable("at_floor")]#, Variable("max")]

    #     symbol_table = {}
    #     symbol_table["max_floor"] = TypedValuation("max_floor", "int", None)
    #     symbol_table["target"] = TypedValuation("target", "int", None)
    #     symbol_table["signal"] = TypedValuation("signal", "int", None)
    #     symbol_table["at_floor"] = TypedValuation("at_floor", "int", None)

    #     real, _ = abstract_synthesis_loop(ltlmt, boolean_in_acts, numerical_in_acts, boolean_out_acts, state_vars, symbol_table)
    #     self.assertTrue(real)

    def test_elevator_steps(self):
        ltlmt_formula = """(at_floor = 0 & target = 0 &
                            G((env_done -> env_done W !((at_floor > target) | (at_floor < target))) & max_floor = 3)) -> G(
                            ([at_floor := at_floor] | [at_floor := at_floor - 1] | [at_floor := at_floor + 1]) &
                            ((env_inc & !env_done & target < max_floor) -> [target := target + 1]) &
                            ((!env_inc & !env_done & target > 0) -> [target := target - 1]) &
                            ((env_done) -> [target := target]) &
                            at_floor >= 0 & at_floor <= max_floor & (target != 0 -> F (!((at_floor > target) | (at_floor < target)))))"""
        ltlmt = string_to_ltlmt(ltlmt_formula)
        tp = ToProgram()
        tp.walk(ltlmt)
        prog, ltl = tp.generateProgram(ltlmt)
        print(prog.to_prog(ltl))

        real, mm = synthesize(prog, ltl, None, False)
        self.assertTrue(real)
        print(mm)

    # def test_elevator_steps_small(self):
    #     assumptions = ["floor = 0",
    #                    "target = 0",
    #                    "G(max_floor = 3)",
    #                    "G(0 <= target)",
    #                    "G(target < max_floor)",
    #                    "G(stutter_target W (target = floor))",
    #                    ]
    #     guarantees = ["G(stutter_target -> [target := target])",
    #                   "G(!stutter_target -> ([floor := floor] & ((inc & [target := target + 1]) | (!inc & [target := target - 1]))))",
    #                   "G(0 <= floor)",
    #                   "G(floor < max_floor)",
    #                   "G(stutter_target -> F target = floor)",
    #                   "G(stutter_target -> ([floor := floor + 1] | [floor := floor - 1]))"]

    #     parsed_a = map(string_to_ltlmt, assumptions)
    #     parsed_g = map(string_to_ltlmt, guarantees)
    #     ltlmt = implies(conjunct_formula_set(parsed_a), conjunct_formula_set(parsed_g))
    #     # ltlmt = string_to_ltlmt(ltlmt_formula.replace("max", "3"))

    #     boolean_in_acts = []
    #     numerical_in_acts = []
    #     boolean_out_acts = []
    #     state_vars = [Variable("max_floor"), Variable("target"), Variable("floor")]#, Variable("max")]

    #     symbol_table = {}
    #     symbol_table["max_floor"] = TypedValuation("max_floor", "int", None)
    #     symbol_table["target"] = TypedValuation("target", "int", None)
    #     symbol_table["floor"] = TypedValuation("at_floor", "int", None)

    #     real, _ = abstract_synthesis_loop(ltlmt, boolean_in_acts, numerical_in_acts, boolean_out_acts, state_vars, symbol_table)
    #     self.assertTrue(real)

    def test_pong_100(self):
        ltlmt_formula = """ G(
                            ([loc := loc + 1] -> ([loc := loc + 1] W (!(loc > 100 | loc < 100))))
                            && ([loc := loc - 1] -> ([loc := loc - 1] W (!(loc > 0 | loc < 0))))
                            && (!(loc > 0 | loc < 0) -> [loc := loc + 1])
                            && (!(loc > 100 | loc < 100) -> [loc := loc - 1])
                            )"""
        ltlmt = string_to_ltlmt(ltlmt_formula)
        tp = ToProgram()
        tp.walk(ltlmt)
        prog, ltl = tp.generateProgram(ltlmt)
        print(prog.to_prog(ltl))

        real, mm = synthesize(prog, ltl, None, False)
        self.assertTrue(real)
        print(mm)

    def test_cfs(self):
        ltlmt_formula = """
        (G (!(enq1 && deq1) && !(enq2 && deq2))) -> (
            (![nx := 1] W enq1)
            &&
            (![nx := 2] W enq2)
            &&
            G([nx := 0] || [nx := 1] || [nx := 2])
            &&
            G(enq1 -> (F [nx := 1] || F deq1) )
            &&
            G(enq2 -> (F [nx := 2] || F deq2) )
            &&
            G(deq1 -> (![nx := 1] W enq1))
            &&
            G(deq2 -> (![nx := 2] W enq2))
            &&
            G(enq2 -> ((rt1 > rt2) -> ![nx := 1]) W deq2)
            &&
            G(enq1 -> ((rt2 > rt1) -> ![nx := 2]) W deq1)
            &&
            G([nx := 1] <-> [rt1 := rt1 + 1])
            &&
            G([nx := 2] <-> [rt2 := rt2 + 1])
        )"""
        ltlmt = string_to_ltlmt(ltlmt_formula)
        tp = ToProgram()
        tp.walk(ltlmt)
        prog, ltl = tp.generateProgram(ltlmt)
        print(prog.to_prog(ltl))

        real, mm = synthesize(prog, ltl, None, False)
        self.assertTrue(real)
        print(mm)

    def test_rr(self):
        ltlmt_formula = """
        G (
            ([ptr := ptr + 1] || [ptr := ptr -1])
            &&
            (G F [nx := 0])
            &&
            (G F [nx := 1])
            &&
            ((!(ptr > 0 | ptr < 0)) -> [nx := 0])
            &&
            ((!(ptr > 1 | ptr < 1)) -> [nx := 1])
        )"""
        ltlmt = string_to_ltlmt(ltlmt_formula)
        tp = ToProgram()
        tp.walk(ltlmt)
        prog, ltl = tp.generateProgram(ltlmt)
        print(prog.to_prog(ltl))

        real, mm = synthesize(prog, ltl, None, False)
        self.assertTrue(real)
        print(mm)

    def test_escalator_smart(self):
        ltlmt_formula = """
        (G(botqueue >= 0 & topqueue >= 0)) -> G (
            (!([topqueue := topqueue - 1] && [botqueue := botqueue - 1]))
            &&
            (F (!(topqueue > 0 | topqueue < 0)))
            &&
            (F (!(botqueue > 0 | botqueue < 0)))
            &&
            ((botqueue > topqueue) -> [botqueue := botqueue - 1])
            &&
            ((!(botqueue > topqueue)) -> [topqueue := topqueue - 1])
        )
        """
        ltlmt = string_to_ltlmt(ltlmt_formula)
        tp = ToProgram()
        tp.walk(ltlmt)
        prog, ltl = tp.generateProgram(ltlmt)
        print(prog.to_prog(ltl))

        real, mm = synthesize(prog, ltl, None, False)
        self.assertTrue(real)
        print(mm)

    def test_preemptive(self):
        ltlmt_formula = """
        (G !(run1 && run2)) -> G (
            ([nx := 1] || [nx := 2])
            &&
            (run1 -> [nx := 1])
            &&
            (run2 -> [nx := 2])
            &&
            ([nx := 1] <-> [rt1 := rt1 + 1])
            &&
            ([nx := 2] <-> [rt2 := rt2 + 1])
            &&
            ((!run1 && !run2) -> (rt2 > rt1) -> [nx := 1])
            &&
            ((!run1 && !run2) -> (rt1 > rt2) -> [nx := 2])
            &&
            ((G (!run1 && !run2))-> ((G F [nx := 1]) && (G F [nx := 2])))
        )
        """
        ltlmt = string_to_ltlmt(ltlmt_formula)
        tp = ToProgram()
        tp.walk(ltlmt)
        prog, ltl = tp.generateProgram(ltlmt)
        print(prog.to_prog(ltl))

        real, mm = synthesize(prog, ltl, None, False)
        self.assertTrue(real)
        print(mm)

    def test_load_balancer(self):
        ltlmt_formula = """
        G (
            ((enqueue && (cpu1 > cpu0)) -> [cpu0 := cpu0 + 1])
            &&
            ((enqueue && (cpu0 > cpu1)) -> [cpu1 := cpu1 + 1])
            &&
            ((!enqueue && (cpu1 > cpu0)) -> ([cpu0 := cpu0 + 1] && [cpu1 := cpu1 + 1]))
            &&
            ((!enqueue && (cpu0 > cpu1)) -> ([cpu0 := cpu0 - 1] && [cpu1 := cpu1 + 1]))
            &&
            !(G (cpu0 > cpu1))
            &&
            !(G (cpu1 > cpu0))
        )
        """
        ltlmt = string_to_ltlmt(ltlmt_formula)
        tp = ToProgram()
        tp.walk(ltlmt)
        prog, ltl = tp.generateProgram(ltlmt)
        print(prog.to_prog(ltl))

        real, mm = synthesize(prog, ltl, None, False)
        self.assertTrue(real)
        print(mm)
