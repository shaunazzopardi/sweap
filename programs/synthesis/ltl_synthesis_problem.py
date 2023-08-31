from prop_lang.formula import Formula
from prop_lang.variable import Variable


class LTLSynthesisProblem():
    env_props: [Variable]
    con_props: [Variable]
    assumptions: [Formula]
    guarantees: [Formula]

    def __init__(self,
                 env_props: [Variable],
                 con_props: [Variable],
                 assumptions: [Formula],
                 guarantees: [Formula]):
        self.env_props = env_props
        self.con_props = con_props
        self.assumptions = assumptions
        self.guarantees = guarantees

    def get_env_props(self):
        return self.env_props

    def get_con_props(self):
        return self.con_props

    def get_assumptions(self):
        return self.assumptions

    def get_guarantees(self):
        return self.guarantees

    def to_tlsf(self):
        env_acts_lowered = [str(a) for a in self.env_props]
        con_acts_lowered = [str(a) for a in self.con_props]

        assumptions_tlsf = [str(a).replace("TRUE", "true") \
                                .replace("True", "true") \
                                .replace("FALSE", "false") \
                                .replace("False", "false") \
                                .replace(" & ", " && ") \
                                .replace(" | ", " || ") \
                                .replace("\"", "") for a in self.assumptions]

        guarantees_tlsf = [str(g).replace("TRUE", "true") \
                               .replace("True", "true") \
                               .replace("FALSE", "false") \
                               .replace("False", "false") \
                               .replace(" & ", " && ") \
                               .replace(" | ", " || ") \
                               .replace("\"", "") for g in self.guarantees]

        info = "INFO {\n" + \
               '\tTITLE:       ""\n' + \
               '\tDESCRIPTION: ""\n' + \
               "\tSEMANTICS:   Mealy\n" + \
               "\tTARGET:      Mealy\n" + \
               "}\n"

        main = "MAIN {\n"
        main += "\tINPUTS { \n\t\t"
        main += ";\n\t\t".join(map(str, env_acts_lowered))
        main += "\n\t}\n"
        main += "\tOUTPUTS { \n\t\t"
        main += ";\n\t\t".join(map(str, con_acts_lowered))
        main += "\n\t}\n"
        main += "\tASSUMPTIONS {\n\t\t"
        main += ";\n\n\t\t".join(map(str, assumptions_tlsf))
        main += "\n\t}\n"
        main += "\tGUARANTEES { \n\t\t"
        main += ";\n\n\t\t".join(map(str, guarantees_tlsf))
        main += "\n\t}\n"
        main += "}"

        return info + main

