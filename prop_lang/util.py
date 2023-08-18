import re

from pysmt.shortcuts import And, serialize, simplify
from sympy.logic.boolalg import to_dnf, simplify_logic, to_cnf, is_dnf
from sympy.parsing.sympy_parser import parse_expr

from parsing.string_to_prop_logic import string_to_prop
from programs.analysis.smt_checker import SMTChecker
from programs.typed_valuation import TypedValuation
from prop_lang.atom import Atom
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.mathexpr import MathExpr
from prop_lang.uniop import UniOp
from prop_lang.value import Value
from prop_lang.variable import Variable


def true():
    return Value("TRUE")


def false():
    return Value("FALSE")


def conjunct(left: Formula, right: Formula):
    if isinstance(left, Value):
        if left.is_true():
            return right
    if isinstance(right, Value):
        if right.is_true():
            return left

    if isinstance(left, Value):
        if left.is_false():
            return left
    if isinstance(right, Value):
        if right.is_false():
            return right

    return BiOp(left, "&", right)


def conjunct_formula_set(s) -> Formula:
    ret = true()
    for f in s:
        ret = conjunct(f, ret)
    return ret


def conjunct_typed_valuation_set(s: set[TypedValuation]) -> Formula:
    ret = true()
    for f in s:
        ret = conjunct(ret, BiOp(Variable(f.name), "=", Value(f.value)))
    return ret


def disjunct(left: Formula, right: Formula):
    if isinstance(left, Value):
        if left.is_false():
            return right
    if isinstance(right, Value):
        if right.is_false():
            return left

    if isinstance(left, Value):
        if left.is_true():
            return left
    if isinstance(right, Value):
        if right.is_true():
            return right

    return BiOp(left, "|", right);


def disjunct_formula_set(s) -> Formula:
    ret = false()
    for f in s:
        ret = disjunct(f, ret)
    return ret


def implies(left: Formula, right: Formula):
    return BiOp(left, "->", right);


def iff(left: Formula, right: Formula):
    return BiOp(left, "<->", right);


def U(left: Formula, right: Formula):
    return BiOp(left, "U", right);


def neg(ltl: Formula):
    if isinstance(ltl, UniOp):
        if ltl.op == "!":
            return ltl.right

    return UniOp("!", ltl);


def G(ltl: Formula):
    return UniOp("G", ltl);


def F(ltl: Formula):
    return UniOp("F", ltl);


def X(ltl: Formula):
    return UniOp("X", ltl);


def nnf(prop: Formula) -> Formula:
    if isinstance(prop, Atom):
        return prop
    elif isinstance(prop, UniOp):
        if prop.op == "!":
            if isinstance(prop.right, Atom):
                return prop
            elif isinstance(prop.right, UniOp) and prop.right.op == "!":
                return nnf(prop.right)
    elif isinstance(prop, BiOp):
        if re.match("<(-|=)>", prop.op):
            return nnf(conjunct(
                implies(prop.left, prop.right),
                implies(prop.right, prop.left)))
        elif re.match("(-|=)>", prop.op):
            return nnf(disjunct(neg(prop.left), prop.right))
        elif re.match("&&*", prop.op):
            return conjunct(nnf(prop.left), nnf(prop.right))
        elif re.match("\|\|?", prop.op):
            return disjunct(nnf(prop.left), nnf(prop.right))
        else:  # math expression
            return prop
    else:
        return NotImplemented


def sat(formula: Formula, symbol_table: dict, solver: SMTChecker) -> bool:
    return solver.check(And(*formula.to_smt(symbol_table)))


def is_tautology(formula: Formula, symbol_table: dict, solver: SMTChecker) -> bool:
    return not solver.check(And(*neg(formula).to_smt(symbol_table)))


def is_contradictory(formula: Formula, symbol_table: dict, solver: SMTChecker) -> bool:
    return not solver.check(And(*formula.to_smt(symbol_table)))


def negation_closed(predicates: [Formula]):
    for p in predicates:
        if neg(p) not in predicates:
            return False
    return True


def prime_action(acts: [BiOp]) -> Formula:
    if len(acts) == 0:
        return acts
    else:
        primed_acts = []
        for act in acts:
            primed_acts.append(BiOp(Atom(act.left.name + "_next"), "=", act.right))
    return conjunct_formula_set(primed_acts)


def push_negation(f: Formula):
    if isinstance(f, Atom):
        return f
    elif isinstance(f, BiOp):
        return BiOp(push_negation(f.left), f.op, push_negation(f.right))
    elif isinstance(f, UniOp):
        if isinstance(f.right, Value) or isinstance(f.right, Variable):
            return f
        elif f.op != "!":
            return UniOp("!", push_negation(f.right))
        else:
            if isinstance(f.right, UniOp) and f.right.op == "!":
                return push_negation(f.right.right)
            elif isinstance(f.right, UniOp) and f.right.op != "!":
                return UniOp("!", push_negation(f.right))
            elif isinstance(f.right, BiOp):
                if f.right.op in ["&", "&&"]:
                    return BiOp(push_negation(UniOp("!", f.right.left)), "|",
                                push_negation(UniOp("!", f.right.right)))
                elif f.right.op in ["|", "||"]:
                    return BiOp(push_negation(UniOp("!", f.right.left)), "&",
                                push_negation(UniOp("!", f.right.right)))
                elif f.right.op in ["->", "=>"]:
                    return BiOp(push_negation(f.right.left), "&", push_negation(UniOp("!", f.right.right)))
                elif f.right.op in ["<->", "<=>"]:
                    return BiOp(
                        BiOp(push_negation(f.right.left), "&", push_negation(UniOp("!", f.right.right)),
                             "|",
                             BiOp(push_negation(UniOp("!", f.right.left)), "&", push_negation(f.right.right))))
                else:
                    return UniOp(f.op, push_negation(f.right))
    else:
        return f


def only_dis_or_con_junctions(f: Formula):
    if isinstance(f, Atom):
        return f
    elif isinstance(f, UniOp):
        return UniOp(f.op, only_dis_or_con_junctions(f.right))
    elif isinstance(f, BiOp):
        if f.op in ["&", "&&", "|", "||"]:
            return BiOp(only_dis_or_con_junctions(f.left), f.op, only_dis_or_con_junctions(f.right))
        elif f.op in ["->", "=>"]:
            return BiOp(UniOp("!", only_dis_or_con_junctions(f.left)), "&", only_dis_or_con_junctions(f.right))
        elif f.op in ["<->", "<=>"]:
            return BiOp(only_dis_or_con_junctions(BiOp(f.left, "->", f.right)), "&",
                        only_dis_or_con_junctions(BiOp(f.right, "->", f.left)))
        else:
            # check if math expr? math expr should be abstracted out before manipulating formulas also for dnf
            # print("only_dis_or_con_junctions: I do not know how to handle " + str(f) + ", treating it as math expression.")
            return MathExpr(f)
    else:
        return f


dnf_cache = {}


def simplify_formula_with_math(formula, symbol_table):
    simple_f_without_math, dic = formula.replace_math_exprs(symbol_table)
    return string_to_prop(serialize(simplify(And(*formula.to_smt(symbol_table | dic))))).replace(
        [BiOp(Variable(key), ":=", value) for key, value in dic.items()])


def simplify_formula_without_math(formula, symbol_table=None):
    if symbol_table == None:
        symbol_table = {str(v): TypedValuation(str(v), "bool", None) for v in formula.variablesin()}

    return string_to_prop(serialize(simplify(And(*formula.to_smt(symbol_table)))))


def cnf(f: Formula, symbol_table: dict = None):
    if symbol_table == None:
        symbol_table = {str(v): TypedValuation(str(v), "bool", None) for v in f.variablesin()}
    try:
        if f in dnf_cache.keys():
            return dnf_cache[f]
        simple_f = only_dis_or_con_junctions(f)
        simple_f = propagate_negations(simple_f).simplify()
        simple_f_without_math, dic = simple_f.replace_math_exprs(symbol_table)
        simple_f_without_math = simplify_formula_without_math(simple_f_without_math).to_nuxmv()
        for_sympi = parse_expr(str(simple_f_without_math).replace("!", " ~"), evaluate=True)
        if isinstance(for_sympi, int):
            return f
        # if formula has more than 8 variables it can take a long time, dnf is exponential
        in_cnf = to_cnf(for_sympi, simplify=True, force=True)
        # print(str(f) + " after cnf becomes " + str(in_cnf).replace("~", "!"))
        in_dnf_formula = string_to_prop(str(in_cnf).replace("~", "!"))
        in_dnf_math_back = in_dnf_formula.replace([BiOp(Variable(key), ":=", value) for key, value in dic.items()])

        dnf_cache[f] = in_dnf_math_back

        return in_dnf_math_back
    except Exception as e:
        raise Exception("dnf: I do not know how to handle " + str(f) + ", cannot turn it into dnf." + str(e))


def dnf(f: Formula, symbol_table: dict=None, simplify=True):
    if isinstance(f, Value) or isinstance(f, MathExpr):
        return f

    if symbol_table == None:
        symbol_table = {str(v): TypedValuation(str(v), "bool", None) for v in f.variablesin()}

    try:
        if f in dnf_cache.keys():
            return dnf_cache[f]
        simple_f = only_dis_or_con_junctions(f)
        simple_f = propagate_negations(simple_f)
        if simplify:
            simple_f = simple_f.simplify()
        simple_f = simple_f.to_nuxmv()
        simple_f_without_math, dic = simple_f.replace_math_exprs(symbol_table, 0)

        if isinstance(f, Value):
            return simple_f

        for_sympi = parse_expr(str(simple_f_without_math).replace("!", " ~"), evaluate=simplify)
        if isinstance(for_sympi, int):
            return f
        if simplify:
            for_sympi = simplify_logic(for_sympi)
        # if formula has more than 8 variables it can take a long time, dnf is exponential
        if is_dnf(for_sympi):
            in_dnf = for_sympi
        else:
            in_dnf = to_dnf(for_sympi, simplify=simplify, force=simplify)
        print(str(f) + " after dnf becomes " + str(in_dnf).replace("~", "!"))
        in_dnf_formula = string_to_prop(str(in_dnf).replace("~", "!"))
        in_dnf_math_back = in_dnf_formula.replace([BiOp(key, ":=", value) for key, value in dic.items()])

        dnf_cache[f] = in_dnf_math_back

        return in_dnf_math_back
    except:
        dnf(f, symbol_table, simplify)
        raise Exception("dnf: I do not know how to handle " + str(f) + ", cannot turn it into dnf.")


def append_to_variable_name(formula, vars_names, suffix):
    return formula.replace([BiOp(Variable(v), ":=", Variable(v + suffix)) for v in vars_names])


def mutually_exclusive_rules(states):
    return [str(s) + " -> " + str(conjunct_formula_set([neg(Variable(str(ss))) for ss in states if ss != s])) for s in
            states]


def is_boolean(var, tvs):
    return any(tv for tv in tvs if tv.name == str(var) and re.match("bool(ean)?", str(tv.type)))


def infinite_type(var, tvs):
    return any(tv for tv in tvs if tv.name == str(var) and re.match("(nat(ural)?|int(eger)?|real|rat(ional)?)", str(tv.type)))


def related_to(v, F: Formula):
    related_to = set()
    done = set()
    current = {v}
    while len(current) > 0:
        next = set()
        for to_do in current:
            for sf in F.sub_formulas_up_to_associativity():
                atom_set = set(sf.variablesin())
                if to_do in atom_set:
                    related_to |= atom_set
                    next |= {a for a in atom_set if a not in done}
                done |= next
        current = next
    return related_to


def type_constraints(formula, symbol_table):
    return conjunct_formula_set(set({type_constraint(v, symbol_table) for v in formula.variablesin()}))


def type_constraints_acts(acts : [BiOp], symbol_table):
    return conjunct_formula_set(set({type_constraint(act.left, symbol_table).replace([BiOp(act.left, ":=", act.right)]) for act in acts}))


def type_constraint(variable, symbol_table):
    if str(variable) not in symbol_table.keys():
        raise Exception(f"{str(variable)} not in symbol table.")
    typed_val = symbol_table[str(variable)]

    if isinstance(variable, Variable):
        if typed_val.type == "int" or typed_val.type == "integer":
            return Value("TRUE")
        elif typed_val.type == "bool" or typed_val.type == "boolean":
            return Value("TRUE")
        elif typed_val.type == "nat" or typed_val.type == "natural":
            return BiOp(variable, ">=", Value("0"))
        elif re.match("[0-9]+..+[0-9]+", typed_val.type):
            split = re.split("..+", typed_val.type)
            lower = split[0]
            upper = split[1]
            return BiOp(BiOp(variable, ">=", Value(lower)), "&&", BiOp(variable, "<=", Value(upper)))
        else:
            raise NotImplementedError(f"Type {typed_val.type} unsupported.")
    else:
        raise Exception(f"{str(variable)} not a variable.")


def propagate_negations(formula):
    if isinstance(formula, UniOp):
        if formula.op == "!":
            return negate(formula.right)
    elif isinstance(formula, BiOp):
        return BiOp(propagate_negations(formula.left), formula.op, propagate_negations(formula.right))
    else:
        return formula


def negate(formula):
    if isinstance(formula, UniOp):
        if formula.op == "!":
            return formula.right
        else:
            return UniOp(formula.op, negate(formula.right))
    elif isinstance(formula, BiOp):
        if formula.op == "&" or formula.op == "&&":
            return BiOp(negate(formula.left), "|", negate(formula.right))
        elif formula.op == "|" or formula.op == "||":
            return BiOp(negate(formula.left), "&", negate(formula.right))
        elif formula.op == "->" or formula.op == "=>":
            return BiOp(formula.left, "&", negate(formula.right))
        elif formula.op == "<->" or formula.op == "<=>":
            return BiOp(BiOp(formula.left, "&", negate(formula.right)), "|", BiOp(negate(formula.left), "&", formula.right))
        else:
            return UniOp("!", formula)
    elif isinstance(formula, MathExpr):
        return MathExpr(negate(formula.formula))
    else:
        return UniOp("!", formula)