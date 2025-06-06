from prop_lang.formula import Formula
from prop_lang.variable import Variable
from synthesis.ltl_synthesis_problem import LTLSynthesisProblem


class AbstractLTLSynthesisProblem:
    pure_env_props: [Variable]
    program_out_props: [Variable]
    program_pred_props: [Variable]
    con_props: [Variable]
    ltl_synthesis_problem: LTLSynthesisProblem
    tlsf: str

    def __init__(
        self,
        pure_env_props: [Variable],
        program_out_props: [Variable],
        program_pred_props: [Variable],
        con_props: [Variable],
        assumptions: [Formula],
        guarantees: [Formula],
    ):
        self.pure_env_props = pure_env_props
        self.program_out_props = program_out_props
        self.program_pred_props = program_pred_props
        self.con_props = con_props
        self.ltl_synthesis_problem = LTLSynthesisProblem(
            pure_env_props + program_out_props + program_pred_props,
            con_props,
            assumptions,
            guarantees,
        )
        self.tlsf = self.ltl_synthesis_problem.tlsf

    def get_env_props(self):
        return self.pure_env_props

    def get_con_props(self):
        return self.con_props

    def get_program_out_props(self):
        return self.program_out_props

    def get_program_pred_props(self):
        return self.program_pred_props

    def get_assumptions(self):
        return self.ltl_synthesis_problem.get_assumptions()

    def get_guarantees(self):
        return self.ltl_synthesis_problem.get_guarantees()
