import logging
import re
from multiprocessing import Queue, Process

import sympy
from pysmt.environment import Environment
from pysmt.fnode import FNode
from pysmt.shortcuts import And, simplify, serialize
from sympy import Basic
from sympy.logic.boolalg import to_dnf, to_cnf

from parsing.string_to_prop_logic import string_to_prop
from analysis.smt_checker import check
from programs.typed_valuation import TypedValuation
from prop_lang.atom import Atom
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.mathexpr import MathExpr
from prop_lang.nondet import NonDeterministic
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


def conjunct_formula_set(s, sort=False) -> Formula:
    if sort:
        s = sorted(list({p for p in s}), key=lambda x : str(x))

    ret = true()
    for f in s:
        ret = conjunct(f, ret)
    return ret


def conjunct_typed_valuation_set(s: set[TypedValuation]) -> Formula:
    ret = true()
    for f in s:
        if isinstance(f.value, NonDeterministic):
            continue
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

    return BiOp(left, "|", right)


def disjunct_formula_set(s) -> Formula:
    ret = false()
    for f in s:
        ret = disjunct(f, ret)
    return ret


def implies(left: Formula, right: Formula):
    return BiOp(left, "->", right)


def iff(left: Formula, right: Formula):
    return BiOp(left, "<->", right)


def U(left: Formula, right: Formula):
    return BiOp(left, "U", right)


def W(left: Formula, right: Formula):
    return BiOp(left, "W", right)


def neg(ltl: Formula):
    if isinstance(ltl, UniOp):
        if ltl.op == "!":
            return ltl.right

    return UniOp("!", ltl)


def G(ltl: Formula):
    return UniOp("G", ltl)


def F(ltl: Formula):
    return UniOp("F", ltl)


def X(ltl: Formula):
    return UniOp("X", ltl)


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


def sat(formula: Formula, symbol_table: dict = None, add_missing_vars:bool=False) -> bool:
    if symbol_table == None:
        symbol_table = {str(v): TypedValuation(str(v), "bool", None) for v in formula.variablesin()}
    if add_missing_vars:
        symbol_table.update({str(v): TypedValuation(str(v), "bool", None) for v in formula.variablesin()
                                if str(v) not in symbol_table.keys()})
    try:
        return check(And(*formula.to_smt(symbol_table)))
    except Exception as e:
        logging.info(str(formula))
        return check(And(*formula.to_smt(symbol_table)))

def equivalent(formula1: Formula, formula2: Formula, symbol_table: dict = None) -> bool:
    if symbol_table == None:
        symbol_table = {str(v): TypedValuation(str(v), "bool", None) for v in formula1.variablesin()}
        symbol_table |= {str(v): TypedValuation(str(v), "bool", None) for v in formula2.variablesin()}
    return not check(And(*neg(iff(formula1, formula2)).to_smt(symbol_table)))


def is_tautology(formula: Formula, symbol_table: dict = None) -> bool:
    if symbol_table == None:
        symbol_table = {str(v): TypedValuation(str(v), "bool", None) for v in formula.variablesin()}
    return not check(And(*neg(formula).to_smt(symbol_table)))


def is_contradictory(formula: Formula, symbol_table: dict = None) -> bool:
    if symbol_table == None:
        symbol_table = {str(v): TypedValuation(str(v), "bool", None) for v in formula.variablesin()}
    return not check(And(*formula.to_smt(symbol_table)))


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


def propagate_nexts(formula, add_next=False):
    if isinstance(formula, Value) or isinstance(formula, Variable):
        if add_next:
            return X(formula)
    if isinstance(formula, UniOp):
        if formula.op == "X":
            return propagate_nexts(formula.right, True)
        else:
            return UniOp(formula.op, propagate_nexts(formula.right, add_next))
    elif isinstance(formula, BiOp):
        return BiOp(propagate_nexts(formula.left, add_next), formula.op, propagate_nexts(formula.right, add_next))
    else:
        return formula


def only_dis_or_con_junctions(f: Formula):
    if isinstance(f, Atom):
        return f
    elif isinstance(f, UniOp):
        return UniOp(f.op, only_dis_or_con_junctions(f.right))
    elif isinstance(f, BiOp):
        if f.op in ["&", "&&", "|", "||"]:
            return BiOp(only_dis_or_con_junctions(f.left), f.op, only_dis_or_con_junctions(f.right))
        elif f.op in ["->", "=>"]:
            return BiOp(UniOp("!", only_dis_or_con_junctions(f.left)), "|", only_dis_or_con_junctions(f.right))
        elif f.op in ["<->", "<=>"]:
            return BiOp(only_dis_or_con_junctions(BiOp(f.left, "->", f.right)), "&",
                        only_dis_or_con_junctions(BiOp(f.right, "->", f.left)))
        else:
            # check if math expr? math expr should be abstracted out before manipulating formulas also for dnf
            # logging.info("only_dis_or_con_junctions: I do not know how to handle " + str(f) + ", treating it as math expression.")
            return MathExpr(f)
    else:
        return f


dnf_cache = {}

def fnode_to_formula(fnode: FNode) -> Formula:
    if fnode.is_constant():
        return Value(fnode.constant_value())
    elif fnode.is_symbol():
        return Variable(fnode.symbol_name())
    else:
        args = [fnode_to_formula(x) for x in fnode.args()]
        if fnode.is_le():
            return MathExpr(BiOp(args[0], "<=", args[1]))
        elif fnode.is_lt():
            return MathExpr(BiOp(args[0], "<", args[1]))
        elif fnode.is_plus():
            return MathExpr(BiOp(args[0], "+", args[1]))
        elif fnode.is_minus():
            return MathExpr(BiOp(args[0], "-", args[1]))
        elif fnode.is_div():
            return MathExpr(BiOp(args[0], "/", args[1]))
        elif fnode.is_times():
            return MathExpr(BiOp(args[0], "*", args[1]))
        elif fnode.is_and():
            return conjunct_formula_set({fnode_to_formula(arg) for arg in fnode.args()})
        elif fnode.is_or():
            return disjunct_formula_set({fnode_to_formula(arg) for arg in fnode.args()})
        elif fnode.is_not():
            return neg(fnode_to_formula(fnode.arg(0)))
        elif fnode.is_implies():
            return implies(fnode_to_formula(fnode.arg(0)), fnode_to_formula(fnode.arg(1)))
        elif fnode.is_iff():
            return iff(fnode_to_formula(fnode.arg(0)), fnode_to_formula(fnode.arg(1)))
        elif fnode.is_symbol():
            return Variable(fnode.symbol_name())
        else:
            return string_to_prop(serialize(fnode))


def sympi_to_formula(basic: Basic):
    if isinstance(basic, sympy.logic.boolalg.Not):
        return neg(sympi_to_formula(basic.args[0]))
    elif isinstance(basic, sympy.logic.boolalg.And):
        return conjunct_formula_set({sympi_to_formula(arg) for arg in list(basic.args)})
    elif isinstance(basic, sympy.logic.boolalg.Or):
        return disjunct_formula_set({sympi_to_formula(arg) for arg in list(basic.args)})
    elif isinstance(basic, sympy.logic.boolalg.Implies):
        return implies(sympi_to_formula(basic.args[0]), sympi_to_formula(basic.args[1]))
    elif isinstance(basic, sympy.logic.boolalg.Equivalent):
        return iff(sympi_to_formula(basic.args[0]), sympi_to_formula(basic.args[1]))
    else:
        return string_to_prop(str(basic))


def simplify_formula_with_math(formula, symbol_table):
    with Environment() as environ:
        simplified = environ.simplifier.simplify(And(*formula.to_smt(symbol_table)))
        try:
            to_formula = fnode_to_formula(simplified)
        except Exception as e:
            to_formula = fnode_to_formula(simplified)
            logging.info(str(e))
        return to_formula


def simplify_formula_without_math(formula, symbol_table=None):
    with Environment() as environ:
        if symbol_table == None:
            symbol_table = {str(v): TypedValuation(str(v), "bool", None) for v in formula.variablesin()}

        simplified = environ.simplifier.simplify(And(*formula.to_smt(symbol_table)))
        to_formula = fnode_to_formula(simplified)
        return to_formula


def formula_with_next_to_without(formula):
    X_propagated_to_atoms = propagate_nexts(formula.to_strix())

    formula_with_no_nexts = X_propagated_to_atoms.replace_formulas(lambda x: None
                                    if not (isinstance(x, UniOp) and x.op == "X")
                                    else Variable("next_" + (x.right.name)))

    return formula_with_no_nexts


def simplify_formula_with_next(formula, symbol_table=None):
    with Environment() as environ:
        if symbol_table == None:
            symbol_table = {str(v): TypedValuation(str(v), "bool", None) for v in formula.variablesin()}

        formula_with_no_nexts = formula_with_next_to_without(formula)

        replacings = [BiOp(Variable("next_" + v.name), ":=", X(Variable(v.name))) for v in formula.variablesin()]
        replacings.append(BiOp(Variable("next_true"), ":=", X(Value("true"))))
        replacings.append(BiOp(Variable("next_false"), ":=", X(Value("false"))))

        symbol_table |= {str(r.left): TypedValuation(str(r.left), "bool", None) for r in replacings}

        simplified = environ.simplifier.simplify(And(*formula_with_no_nexts.to_smt(symbol_table)))
        to_formula = fnode_to_formula(simplified)
        to_formula = to_formula.replace(replacings)
        return to_formula


def simplify_ltl_formula(formula, symbol_table=None):
    ltl_to_prop = ltl_to_propositional(formula)
    if symbol_table == None:
        symbol_table = {str(v): TypedValuation(str(v), "bool", None) for v in ltl_to_prop.variablesin()}

    simplified = string_to_prop(serialize(simplify(And(*ltl_to_prop.to_smt(symbol_table)))))

    simplified_ltl = simplified.replace([BiOp(Variable(str(v)), ":=", X(Variable(str(v).split("_next")[0])))
                                         for v in simplified.variablesin() if str(v).endswith("_next")])
    return simplified_ltl


def ltl_to_propositional(formula):
    if isinstance(formula, Value) or isinstance(formula, Variable):
        return formula
    elif isinstance(formula, BiOp):
        return BiOp(ltl_to_propositional(formula.left), formula.op, ltl_to_propositional(formula.right))
    elif isinstance(formula, UniOp):
        if formula.op == "X":
            vars = formula.right.variablesin()
            to_next = [BiOp(v, ":=", Variable(str(v) + "_next")) for v in vars]
            return ltl_to_propositional(formula.right.replace(to_next))
        else:
            return UniOp(formula.op, ltl_to_propositional(formula.right))
    else:
        raise Exception("ltl_to_propositional: I do not know how to handle " + str(formula))


def dnf_safe(f: Formula, symbol_table: dict = None, simplify=True, timeout=0.3):
    if f in dnf_cache.keys():
        return dnf_cache[f]

    f_vars = f.variablesin()
    if len(f_vars) == 0:
        return f
    elif len(f_vars) <= 6:
        result = dnf(f, symbol_table)
        dnf_cache[f] = result
        return result
    else:
        return dnf_with_timeout(f, symbol_table, simplify, timeout)


def dnf(f: Formula, symbol_table: dict = None, simplify=True):
    if isinstance(f, Value) or isinstance(f, MathExpr):
        return f

    if symbol_table == None:
        symbol_table = {str(v): TypedValuation(str(v), "bool", None) for v in f.variablesin()}
    try:
        simple_f = only_dis_or_con_junctions(f)
        simple_f = propagate_negations(simple_f)
        simple_f_without_math, dic = simple_f.replace_math_exprs(symbol_table)
        if simplify:
            simple_f_without_math = simplify_formula_without_math(simple_f_without_math)

        if isinstance(simple_f_without_math, BiOp) and simple_f_without_math.op[0] == "|":
            disjuncts = simple_f_without_math.sub_formulas_up_to_associativity()
        else:
            disjuncts = [simple_f_without_math]

        new_disjuncts = []
        for disjunct in disjuncts:
            if not is_dnf(disjunct):
                for_sympi = disjunct.to_sympy()
                if isinstance(for_sympi, int):
                    return simple_f
            # if formula has more than 8 variables it can take a long time, dnf is exponential
                in_dnf = to_dnf(for_sympi, simplify=simplify, force=True)
                new_disjunct = sympi_to_formula(in_dnf)
            else:
                new_disjunct = disjunct
            # print(str(f) + " after dnf becomes " + str(in_dnf).replace("~", "!"))
            new_disjunct = new_disjunct.replace([BiOp(Variable(key), ":=", value) for key, value in dic.items()])

            new_disjuncts.append(new_disjunct)

        in_dnf_math_back = disjunct_formula_set(new_disjuncts)

        return in_dnf_math_back
    except Exception as e:
        raise Exception("dnf: I do not know how to handle " + str(f) + ", cannot turn it into dnf. " + str(e))


def dnf_with_timeout(f: Formula, symbol_table: dict = None, simplify=True, timeout=0.3):
    if isinstance(f, Value) or isinstance(f, MathExpr):
        return f

    if symbol_table == None:
        symbol_table = {str(v): TypedValuation(str(v), "bool", None) for v in f.variablesin()}

    success, ret = run_with_timeout(dnf, [f, symbol_table, simplify], timeout=timeout)

    if success:
        dnf_cache[f] = ret
        return ret
    else:
        return f


def cnf_with_timeout(f: Formula, symbol_table: dict = None, simplify=True, timeout=0.3):
    if isinstance(f, Value) or isinstance(f, MathExpr):
        return f

    if symbol_table == None:
        symbol_table = {str(v): TypedValuation(str(v), "bool", None) for v in f.variablesin()}

    success, ret = run_with_timeout(cnf, [f, symbol_table], timeout=timeout)
    if success:
        cnf_cache[f] = ret
        return ret
    else:
        return f


def cnf_safe(f: Formula, symbol_table: dict = None, simplify=True, timeout=0.3):
    f_vars = f.variablesin()
    if len(f_vars) == 0:
        return f
    elif f in cnf_cache.keys():
        return cnf_cache[f]
    elif len(f_vars) <= 6:
        result = cnf(f, symbol_table)
        cnf_cache[f] = result
        return result
    else:
        return cnf_with_timeout(f, symbol_table, simplify, timeout)

cnf_cache = {}

def cnf(f: Formula, symbol_table: dict = None):
    if symbol_table == None:
        symbol_table = {str(v): TypedValuation(str(v), "bool", None) for v in f.variablesin()}
    try:
        simple_f = only_dis_or_con_junctions(f)
        simple_f = propagate_negations(simple_f).simplify()
        simple_f_without_math, dic = simple_f.replace_math_exprs(symbol_table)
        simple_f_without_math = simplify_formula_without_math(simple_f_without_math).to_nuxmv()
        for_sympi = simple_f_without_math.to_sympy()
        if isinstance(for_sympi, int):
            return f
        # if formula has more than 8 variables it can take a long time, cnf is exponential
        in_cnf = to_cnf(for_sympi, simplify=True, force=True)
        # print(str(f) + " after cnf becomes " + str(in_cnf).replace("~", "!"))
        try:
            in_cnf_formula = sympi_to_formula(in_cnf)
        except Exception as e:
            raise e
        in_cnf_math_back = in_cnf_formula.replace([BiOp(Variable(key), ":=", value) for key, value in dic.items()])

        cnf_cache[f] = in_cnf_math_back

        return in_cnf_math_back
    except Exception as e:
        raise Exception("cnf: I do not know how to handle " + str(f) + ", cannot turn it into cnf." + str(e))


def append_to_variable_name(formula, vars_names, suffix):
    return formula.replace([BiOp(Variable(v), ":=", Variable(v + suffix)) for v in vars_names])


def mutually_exclusive_rules(states):
    return [str(s) + " -> " + str(conjunct_formula_set([neg(Variable(str(ss))) for ss in states if ss != s])) for s in
            states]


def is_boolean(var, tvs):
    return any(tv for tv in tvs if tv.name == str(var) and re.match("bool(ean)?", str(tv.type)))


def infinite_type(var, tvs):
    return any(
        tv for tv in tvs if tv.name == str(var) and re.match("(nat(ural)?|int(eger)?|real|rat(ional)?)", str(tv.type)))


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


def type_constraints_acts(transition, symbol_table):
    acts = transition.action
    constraints = []
    for act in acts:
        if act.right != act.left:
            constraint = type_constraint(act.left, symbol_table).replace([BiOp(act.left, ":=", act.right)])
            if sat(conjunct(transition.condition, neg(constraint)), symbol_table):
                constraints.append(constraint)
    return conjunct_formula_set(constraints)


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
            return MathExpr(BiOp(variable, ">=", Value("0")))
        elif re.match("[0-9]+..+[0-9]+", typed_val.type):
            split = re.split("..+", typed_val.type)
            lower = split[0]
            upper = split[1]
            return BiOp(MathExpr(BiOp(variable, ">=", Value(lower))), "&&",
                        MathExpr(BiOp(variable, "<=", Value(upper))))
        else:
            raise NotImplementedError(f"Type {typed_val.type} unsupported.")
    else:
        raise Exception(f"{str(variable)} not a variable.")


def propagate_negations(formula):
    if isinstance(formula, UniOp):
        if formula.op == "!":
            return negate(propagate_negations(formula.right))
        else:
            return UniOp(formula.op, propagate_negations(formula))
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
            return BiOp(BiOp(formula.left, "&", negate(formula.right)), "|",
                        BiOp(negate(formula.left), "&", formula.right))
        else:
            return UniOp("!", formula)
    elif isinstance(formula, MathExpr):
        return MathExpr(negate(formula.formula))
    else:
        return UniOp("!", formula).simplify()


def keep_only_vars(formula, vars_to_keep, make_program_choices_explicit=False):
    to_project_out = [v for v in formula.variablesin() if v not in vars_to_keep]
    return project_out_vars_int(propagate_negations(formula), to_project_out, True, make_program_choices_explicit)


def keep_only_vars_inverse(formula, vars_to_keep):
    to_project_out = [v for v in formula.variablesin() if v not in vars_to_keep]
    return project_out_vars_int(propagate_negations(formula), to_project_out, False)


def project_out_vars_inverse(formula, vars_to_project_out):
    return project_out_vars_int(propagate_negations(formula), vars_to_project_out, False)


def project_out_vars(formula, vars_to_project_out, make_program_choices_explicit=False):
    return project_out_vars_int(propagate_negations(formula), vars_to_project_out, True, make_program_choices_explicit)


def project_out_vars_int(formula, vars_to_project_out, make_true, make_program_choices_explicit=False):
    program_choice = Variable("program_choice") if make_program_choices_explicit else Value("FALSE")
    if isinstance(formula, Value):
        return formula
    elif isinstance(formula, Variable):
        if formula in vars_to_project_out:
            return Value("TRUE") if make_true else program_choice
        else:
            return formula
    elif isinstance(formula, UniOp):
        if not isinstance(formula.right, Value) and not isinstance(formula.right, Variable):
            raise Exception("propagate negations before calling project_out_vars")
        if formula.right in vars_to_project_out:
            return Value("TRUE") if make_true else program_choice
        else:
            return formula
    elif isinstance(formula, BiOp):
        vars_in_formula = formula.variablesin()
        if not any(v not in vars_to_project_out for v in vars_in_formula):
            return Value("TRUE") if make_true else program_choice
        elif not any(v in vars_to_project_out for v in vars_in_formula):
            return formula
        else:
            make_true = formula.op[0] == "&"  # if make_true else formula.op[0] == "|"
            return BiOp(project_out_vars_int(formula.left, vars_to_project_out, make_true),
                        formula.op, project_out_vars_int(formula.right, vars_to_project_out, make_true))
    else:
        raise Exception("not implemented")


def partially_evaluate(formula, true_vars: [Variable], false_vars: [Variable], symbol_table):
    new_formula = formula
    for v in true_vars:
        if not isinstance(v, Variable):
            raise Exception("partially_evaluate: element " + str(v) + " of true_vars is not a variable")
        new_formula = new_formula.replace([BiOp(v, ":=", true())])
    for v in false_vars:
        if not isinstance(v, Variable):
            raise Exception("partially_evaluate: element " + str(v) + " of false_vars is not a variable")
        new_formula = new_formula.replace([BiOp(v, ":=", false())])

    new_formula_simplified = new_formula.simplify()
    new_formula_simplified_more = simplify_formula_with_math(new_formula_simplified, symbol_table)

    return new_formula_simplified_more


def is_atomic(f):
    return isinstance(f, Variable) or isinstance(f, Value) or isinstance(f, MathExpr) or (
                isinstance(f, UniOp) and is_atomic(f.right))


def is_conjunction_of_atoms(formula):
    if isinstance(formula, BiOp) and formula.op[0] == "&":
        for f in formula.sub_formulas_up_to_associativity():
            if is_atomic(f):
                continue
            if isinstance(f, BiOp) and f.op[0] == "&":
                if any(not is_atomic(ff)
                       for ff in f.sub_formulas_up_to_associativity()):
                    return False
            else:
                return False
        return True
    elif is_atomic(formula):
        return True
    else:
        return False


def is_disjunction_of_atoms(formula):
    if isinstance(formula, BiOp) and formula.op[0] == "|":
        for f in formula.sub_formulas_up_to_associativity():
            if is_atomic(f):
                continue
            if isinstance(f, BiOp) and f.op[0] == "|":
                if any(not is_atomic(ff)
                       for ff in f.sub_formulas_up_to_associativity()):
                    return False
            else:
                return False
        return True
    elif is_atomic(formula):
        return True
    else:
        return False


def is_dnf(formula):
    if isinstance(formula, BiOp):
        if formula.op == "||":
            for f in formula.sub_formulas_up_to_associativity():
                if not is_conjunction_of_atoms(f):
                    return False
        elif formula.op[0] == "&":
            return is_conjunction_of_atoms(formula)
        else:
            return is_atomic(formula)
    else:
        return is_atomic(formula)


def abstract_out_conjunctions_of_atoms(formula, dict) -> (Formula, dict):
    # traverse the syntax tree, abstract out all conjunction of atoms
    dict = {}
    if is_atomic(formula):
        return formula, dict
    elif is_conjunction_of_atoms(formula):
        var_name = "conj_" + str(len(dict))
        dict[var_name] = formula
        return Variable(var_name), dict
    elif isinstance(formula, BiOp):
        left_form, new_dict = abstract_out_conjunctions_of_atoms(formula.left, dict)
        right_form, new_dict = abstract_out_conjunctions_of_atoms(formula.right, new_dict)
        return BiOp(left_form,
                    formula.op,
                    right_form), new_dict
    elif isinstance(formula, UniOp):
        right_form, new_dict = abstract_out_conjunctions_of_atoms(formula.right, dict)
        return UniOp(formula.op, right_form), new_dict
    else:
        return formula, dict


def abstract_out_disjunctions_of_atoms(formula, dict={}) -> (Formula, dict):
    # traverse the syntax tree, abstract out all conjunction of atoms
    if is_atomic(formula):
        return formula, dict
    elif is_disjunction_of_atoms(formula):
        var_name = "disj_" + str(len(dict))
        dict[var_name] = formula
        return Variable(var_name), dict
    elif isinstance(formula, BiOp):
        left_form, new_dict = abstract_out_disjunctions_of_atoms(formula.left, dict)
        right_form, new_dict = abstract_out_disjunctions_of_atoms(formula.right, new_dict)
        return BiOp(left_form,
                    formula.op,
                    right_form), new_dict
    elif isinstance(formula, UniOp):
        right_form, new_dict = abstract_out_disjunctions_of_atoms(formula.right, dict)
        return UniOp(formula.op, right_form), new_dict
    else:
        return formula, dict


def depth_of_formula(formula):
    if isinstance(formula, BiOp):
        return 1 + max(depth_of_formula(formula.left), depth_of_formula(formula.right))
    elif isinstance(formula, UniOp):
        return 1 + depth_of_formula(formula.right)
    else:
        return 0


def atomic_predicates(formula):
    if isinstance(formula, Value) or isinstance(formula, Variable) or isinstance(formula, MathExpr):
        return {formula}
    else:
        if isinstance(formula, UniOp):
            return atomic_predicates(formula.right)
        elif isinstance(formula, BiOp):
            return atomic_predicates(formula.left) | atomic_predicates(formula.right)
        else:
            raise Exception("atoms: not implemented for " + str(formula))


def run_with_timeout(f, args, timeout=-1):
    if timeout == -1:
        return f(args)
    else:
        queue = Queue()
        params = tuple([f] + [tuple(args + [queue])])
        p1 = Process(target=evaluate_and_queue, name=f.__name__, args=params)
        p1.start()
        p1.join(timeout)
        if p1.is_alive():
            p1.terminate()
            return False, None
        else:
            return True, queue.get()


def evaluate_and_queue(function, args):
    result = function(*args[:-1])
    print(result)
    args[-1].put(result)


def flatten_effects(effects: [(frozenset[Formula], frozenset[frozenset[Formula]])], preds, rename_pred):
    nows = [set(now) for now, _ in effects]
    common_nows = set.intersection(*nows)

    reduced_effects = [(now.difference(common_nows), nexts) for now, nexts in effects]
    common_now_preds = list({p for p in preds for now, _ in reduced_effects if p in now or neg(p) in now})
    common_now_preds.sort(key=lambda p : abs(len([p for now, _ in reduced_effects if p in now]) - len([p for now, _ in reduced_effects if neg(p) in now])), )

    nexts = [set(next) for _, nexts in reduced_effects for next in nexts]
    common_nexts = set.intersection(*nexts)
    reduced_effects = [(now, {next.difference(common_nexts)}) for now, nexts in reduced_effects for next in nexts]

    precondition = conjunct_formula_set([rename_pred(p) for p in common_nows])
    postcondition = conjunct_formula_set([rename_pred(p) for p in common_nexts])
    formula = take_out_predicate(reduced_effects, common_now_preds, rename_pred)
    formula = conjunct(conjunct(precondition, postcondition), formula)
    # TODO remove X TRUE
    return formula


def take_out_predicate(effects: [(frozenset[Formula], frozenset[frozenset[Formula]])], preds : list, rename_pred):
    if len(preds) == 0:
        formula = disjunct_formula_set([conjunct(conjunct_formula_set([rename_pred(n) for n in now]),
                                                      disjunct_formula_set([X(conjunct_formula_set([rename_pred(n) for n in next])) for next in nexts]))
                                             for now, nexts in effects])
    else:
        p = preds[0]
        p_true = [(now.difference({p}), nexts) for now, nexts in effects if p in now]
        p_false = [(now.difference({neg(p)}), nexts) for now, nexts in effects if neg(p) in now]
        true_formula = take_out_predicate(p_true, preds[1:], rename_pred)
        false_formula = take_out_predicate(p_false, preds[1:], rename_pred)

        true_formula = simplify_formula_with_next(true_formula)
        false_formula = simplify_formula_with_next(false_formula)
        true_formula = true_formula.replace_formulas(lambda x : Value("true") if isinstance(x, UniOp) and x.op == "X" and isinstance(x.right, Value) and x.right.is_true() else None)
        false_formula = false_formula.replace_formulas(lambda x : Value("true") if isinstance(x, UniOp) and x.op == "X" and isinstance(x.right, Value) and x.right.is_true() else None)

        if true_formula == false_formula:
            formula = true_formula
        else:
            formula = disjunct(conjunct(rename_pred(p), true_formula),
                               conjunct(neg(rename_pred(p)), false_formula))

    formula = simplify_formula_with_next(formula)
    return formula

def take_out_pred(disjuncts_of_conjuncts: [[Variable]], pred: Variable):
    true_at = set()
    false_at = set()
    others_at = set()
    for disjunct in disjuncts_of_conjuncts:
        if pred in disjunct:
            true_at.add(frozenset({d for d in disjunct if d != pred}))
        elif neg(pred) in disjunct:
            false_at.add(frozenset({d for d in disjunct if d != neg(pred)}))
        else:
            others_at.add(disjunct)

    return true_at, false_at, others_at



def take_out_preds(disjuncts_of_conjuncts: [[Variable]], preds: [Variable]):
    def associated_formula_dict_to_formula(associated_formula):
        return disjunct_formula_set([conjunct(conjunct_formula_set(preds),
                                         disjunct_formula_set([conjunct_formula_set(r) for r in rest]))
                                 for preds, rest in associated_formula.items()])
    associated_formula = {frozenset(): disjuncts_of_conjuncts}

    if len(preds) == 0:
        return associated_formula_dict_to_formula(associated_formula)

    common_preds = set(v for D in disjuncts_of_conjuncts for d in D for v in d.variablesin() if v in preds)
    preds = common_preds
    # sort according to most common
    preds = sorted(preds, key=lambda p: sum(1 for D in disjuncts_of_conjuncts if p in D), reverse=True)

    logging.info("Trying to take out preds from dnf formula")
    prev_formula = associated_formula_dict_to_formula(associated_formula)
    cnt = 0
    for pred in preds:
        new_associated_formula = {}

        for prev_preds, set_of_disjuncts in associated_formula.items():
            pred_true_disjuncts, pred_false_disjuncts, others_at = take_out_pred(set_of_disjuncts, pred)
            if len(pred_true_disjuncts) > 0:
                if frozenset(prev_preds | {pred}) not in new_associated_formula.keys():
                    new_associated_formula[frozenset(prev_preds | {pred})] = set()
                new_associated_formula[frozenset(prev_preds | {pred})].update(pred_true_disjuncts)

            if len(pred_false_disjuncts) > 0:

                if frozenset(prev_preds | {neg(pred)}) not in new_associated_formula.keys():
                    new_associated_formula[frozenset(prev_preds | {neg(pred)})] = set()
                new_associated_formula[frozenset(prev_preds | {neg(pred)})].update(pred_false_disjuncts)

            if len(others_at) > 0:
                if frozenset(prev_preds) not in new_associated_formula.keys():
                    new_associated_formula[frozenset(prev_preds)] = set()
                new_associated_formula[frozenset(prev_preds)].update(others_at)
        logging.info(len(new_associated_formula))
        associated_formula = new_associated_formula
        current_formula = associated_formula_dict_to_formula(associated_formula)
        cnt += 1
        if len(str(prev_formula)) > len(str(current_formula)):
            prev_formula = current_formula
            logging.info(str(cnt) + ": " + str(prev_formula))
    logging.info("final  " + str(cnt) + ": " + str(prev_formula))

    return prev_formula


def take_out_pred_sat(disjuncts: [Formula], pred: Variable, symbol_table):
    true_at = set()
    false_at = set()
    others_at = set()
    for disjunct in disjuncts:
        if not sat(conjunct(disjunct, neg(pred)), symbol_table):
            true_at.add(disjunct.replace([BiOp(pred, ":=", true())]))
        elif not sat(conjunct(disjunct, pred), symbol_table):
            false_at.add(disjunct.replace([BiOp(pred, ":=", false())]))
        else:
            others_at.add(disjunct)

    return true_at, false_at, others_at


def take_out_preds_sat(disjuncts: [Formula], preds: [Formula], symbol_table):
    def associated_formula_dict_to_formula(associated_formula):
        return disjunct_formula_set([conjunct(conjunct_formula_set(preds),
                                         disjunct_formula_set(rest))
                                 for preds, rest in associated_formula.items()])
    associated_formula = {frozenset(): disjuncts}

    if len(preds) == 0:
        return associated_formula_dict_to_formula(associated_formula)

    logging.info("Trying to take out preds from disjunction of formulas")
    prev_formula = associated_formula_dict_to_formula(associated_formula)
    cnt = 0
    for pred in preds:
        new_associated_formula = {}

        for prev_preds, set_of_disjuncts in associated_formula.items():
            pred_true_disjuncts, pred_false_disjuncts, others_at = take_out_pred_sat(set_of_disjuncts, pred, symbol_table)
            if len(pred_true_disjuncts) > 0:
                if frozenset(prev_preds | {pred}) not in new_associated_formula.keys():
                    new_associated_formula[frozenset(prev_preds | {pred})] = set()
                new_associated_formula[frozenset(prev_preds | {pred})].update(pred_true_disjuncts)

            if len(pred_false_disjuncts) > 0:

                if frozenset(prev_preds | {neg(pred)}) not in new_associated_formula.keys():
                    new_associated_formula[frozenset(prev_preds | {neg(pred)})] = set()
                new_associated_formula[frozenset(prev_preds | {neg(pred)})].update(pred_false_disjuncts)

            if len(others_at) > 0:
                if frozenset(prev_preds) not in new_associated_formula.keys():
                    new_associated_formula[frozenset(prev_preds)] = set()
                new_associated_formula[frozenset(prev_preds)].update(others_at)
        logging.info(len(new_associated_formula))
        associated_formula = new_associated_formula
        current_formula = associated_formula_dict_to_formula(associated_formula)
        cnt += 1
        if len(str(prev_formula)) > len(str(current_formula)):
            prev_formula = current_formula
            logging.info(str(cnt) + ": " + str(prev_formula))
    logging.info("final  " + str(cnt) + ": " + str(prev_formula))

    return prev_formula


def project_out_props(env_cond: Formula, env_props: [Variable]):
    return simplify_formula_without_math(project_out_vars(env_cond, env_props))
