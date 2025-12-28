import logging
import re
import sympy

from pysmt.environment import Environment
from pysmt.fnode import FNode
from pysmt.shortcuts import And, simplify, serialize
from sympy import Basic
from sympy.logic.boolalg import to_dnf, to_cnf

from analysis.smt_checker import check, bdd_simplify, find_unsat_core
from parsing.string_to_prop_logic import string_to_prop
from prop_lang.atom import Atom
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.types.ops_and_rels import BoolBiOps, MathOps, MathRels
from prop_lang.update import Update
from prop_lang.mathexpr import MathExpr
from prop_lang.types.types import (
    BaseNumberTypes,
    Type,
    BOOLEAN,
    is_finite,
    Number,
    NATURAL,
    INTEGER,
    interval_range,
)
from prop_lang.types.values import BoolAtoms
from prop_lang.uniop import UniOp
from prop_lang.value import Value
from prop_lang.variable import Variable


def true():
    return Value(BoolAtoms.TRUE)


def false():
    return Value(BoolAtoms.FALSE)


def is_true(f):
    if isinstance(f, Value):
        return f.is_true()
    else:
        return False


def conjunct(left: Formula, right: Formula) -> Formula:
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
        s = sorted(list({p for p in s}), key=lambda x: str(x))

    ret = true()
    if not hasattr(s, "__iter__"):
        raise Exception(
            "conjunct_formula_set: needs an iterable." + str(s) + " is not."
        )
    for f in s:
        ret = conjunct(f, ret)
    return ret


def conjunct_typed_valuation_set(s: dict[str, Value]) -> Formula:
    ret = true()
    for name, value in s.items():
        ret = conjunct(ret, BiOp(Variable(name), "=", value))
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
        if re.match("<([-=])>", prop.op):
            return nnf(
                conjunct(
                    implies(prop.left, prop.right),
                    implies(prop.right, prop.left),
                )
            )
        elif re.match("([-=])>", prop.op):
            return nnf(disjunct(neg(prop.left), prop.right))
        elif re.match("&+", prop.op):
            return conjunct(nnf(prop.left), nnf(prop.right))
        elif re.match(r"\|\|?", prop.op):
            return disjunct(nnf(prop.left), nnf(prop.right))
        else:  # math expression
            return prop
    else:
        return NotImplemented


def sat_parallel(arg):
    formula, symbol_table = arg
    try:
        return check(And(*formula.to_smt(symbol_table)))
    except:
        return check(And(*formula.to_smt(symbol_table)))


def unsat_core(
    formula: Formula,
    symbol_table: dict,
) -> set[Formula]:
    core = find_unsat_core(And(*formula.to_smt(symbol_table)))
    core_formulas = set()
    for fnode in core:
        core_formulas.add(fnode_to_formula(fnode))
    return core_formulas


def sat(
    formula: Formula,
    symbol_table: dict,
) -> bool:
    try:
        return check(And(*formula.to_smt(symbol_table)))
    except Exception as e:
        logging.info(str(formula))
        return check(And(*formula.to_smt(symbol_table)))


def equivalent(formula1: Formula, formula2: Formula, symbol_table: dict = None) -> bool:
    return not check(And(*neg(iff(formula1, formula2)).to_smt(symbol_table)))


def is_tautology(formula: Formula, symbol_table: dict = None) -> bool:
    return not check(And(*neg(formula).to_smt(symbol_table)))


def is_contradictory(formula: Formula, symbol_table: dict = None) -> bool:
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


def propagate_minuses(formula, init=False):
    if isinstance(formula, Value) or isinstance(formula, Variable):
        if init:
            return UniOp(MathOps.SUB, formula)
        else:
            return formula
    elif isinstance(formula, MathExpr):
        return MathExpr(propagate_minuses(formula.formula, init))
    elif isinstance(formula, UniOp):
        if formula.op == "-":
            return propagate_minuses(formula.right, not init)
        else:
            return UniOp(formula.op, propagate_minuses(formula.right, init))
    elif isinstance(formula, BiOp):
        return BiOp(
            propagate_minuses(formula.left, init),
            formula.op,
            propagate_minuses(formula.right, init),
        )
    else:
        return formula


def propagate_nexts(formula, init=False):
    if isinstance(formula, Value) or isinstance(formula, Variable):
        if init:
            return X(formula)
    if isinstance(formula, UniOp):
        if formula.op == "X":
            return propagate_nexts(formula.right, True)
        else:
            return UniOp(formula.op, propagate_nexts(formula.right, init))
    elif isinstance(formula, BiOp):
        return BiOp(
            propagate_nexts(formula.left, init),
            formula.op,
            propagate_nexts(formula.right, init),
        )
    else:
        return formula


def propagate_nexts_and_atomize(formula, init=False):
    if isinstance(formula, Value):
        return formula
    elif isinstance(formula, Variable):
        if init:
            return Variable(str(formula) + "_next")
    if isinstance(formula, UniOp):
        if formula.op == "X":
            return propagate_nexts_and_atomize(formula.right, True)
        else:
            return UniOp(formula.op, propagate_nexts_and_atomize(formula.right, init))
    elif isinstance(formula, BiOp):
        return BiOp(
            propagate_nexts_and_atomize(formula.left, init),
            formula.op,
            propagate_nexts_and_atomize(formula.right, init),
        )
    else:
        return formula


def only_dis_or_con_junctions(f: Formula):
    if isinstance(f, Atom):
        return f
    elif isinstance(f, UniOp):
        return UniOp(f.op, only_dis_or_con_junctions(f.right))
    elif isinstance(f, BiOp):
        if f.op in ["&", "&&", "|"]:
            return BiOp(
                only_dis_or_con_junctions(f.left),
                f.op,
                only_dis_or_con_junctions(f.right),
            )
        elif f.op in ["->", "=>"]:
            return BiOp(
                UniOp("!", only_dis_or_con_junctions(f.left)),
                "|",
                only_dis_or_con_junctions(f.right),
            )
        elif f.op in ["<->", "<=>"]:
            return BiOp(
                only_dis_or_con_junctions(BiOp(f.left, "->", f.right)),
                "&",
                only_dis_or_con_junctions(BiOp(f.right, "->", f.left)),
            )
        elif f.op in LTLBiOps:
            return BiOp(
                only_dis_or_con_junctions(f.left),
                f.op,
                only_dis_or_con_junctions(f.right),
            )
        else:
            # check if math expr? math expr should be abstracted out before manipulating formulas also for dnf
            # logging.info("only_dis_or_con_junctions: I do not know how to handle " + str(f) + ", treating it as math expression.")
            return MathExpr(f)
    else:
        return f


dnf_cache = {}


def fnode_to_formula(fnode: FNode) -> Formula:
    return string_to_prop(serialize(fnode))


def fnode_to_formula_direct(fnode: FNode) -> Formula:
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
            return implies(
                fnode_to_formula(fnode.arg(0)), fnode_to_formula(fnode.arg(1))
            )
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


def simplify_formula_with_math_wo_type_constraints(formula, symbol_table):
    with Environment() as environ:
        simplified = environ.simplifier.simplify(formula.to_smt(symbol_table)[0])
        try:
            to_formula = fnode_to_formula(simplified)
        except Exception as e:
            to_formula = fnode_to_formula(simplified)
            logging.info(str(e))
        return to_formula


def simplify_sum(formula, symbol_table):
    with Environment() as environ:
        simplified = environ.simplifier.simplify(formula.to_smt(symbol_table)[0])
        str_simpl = serialize(simplified)
        if str_simpl[0] == "-":
            return UniOp(MathOps.SUB, Value(str_simpl[1:]))
        else:
            return Value(str_simpl)


def simplify_formula_without_math(formula, symbol_table=None):
    with Environment() as environ:
        if not symbol_table:
            symbol_table = {str(v): BOOLEAN for v in formula.variablesin()}

        simplified = environ.simplifier.simplify(And(*formula.to_smt(symbol_table)))
        to_formula = fnode_to_formula(simplified)
        return to_formula


def formula_with_next_to_without(formula):
    X_propagated_to_atoms = propagate_nexts_and_atomize(formula.to_strix())

    return X_propagated_to_atoms


def simplify_formula_with_next(formula, symbol_table=None):
    with Environment() as environ:
        if not symbol_table:
            symbol_table = {str(v): BOOLEAN for v in formula.variablesin()}

        formula_with_no_nexts = formula_with_next_to_without(formula)

        replacings = {
            Variable("next_" + v.name): X(Variable(v.name))
            for v in formula.variablesin()
        }
        replacings[Variable("next_true")] = X(true())
        replacings[Variable("next_false")] = X(false())

        symbol_table |= {str(r.left): BOOLEAN for r in replacings}

        simplified = environ.simplifier.simplify(
            And(*formula_with_no_nexts.to_smt(symbol_table))
        )
        to_formula = fnode_to_formula(simplified)
        to_formula = to_formula.replace(replacings)
        return to_formula


def bdd_simplify_ltl_formula(formula, symbol_table=None):
    ltl_to_prop = propagate_nexts_and_atomize(formula)

    keys = list(symbol_table.keys())
    for v in keys:
        symbol_table[str(v) + "_next"] = BOOLEAN

    simplified_ltl = bdd_simplify(ltl_to_prop.to_smt(symbol_table)[0])
    if simplified_ltl is not None:
        simplified = string_to_prop(serialize(simplified_ltl))

        simplified_ltl = simplified.replace(
            {
                Variable(str(v)): X(Variable(str(v).split("_next")[0]))
                for v in simplified.variablesin()
                if str(v).endswith("_next")
            }
        )
        return simplified_ltl
    else:
        return formula


def simplify_ltl_formula(formula, symbol_table=None):
    ltl_to_prop = ltl_to_propositional(formula)

    simplified = string_to_prop(
        serialize(simplify(And(*ltl_to_prop.to_smt(symbol_table))))
    )

    simplified_ltl = simplified.replace(
        {
            Variable(str(v)): X(Variable(str(v).split("_next")[0]))
            for v in simplified.variablesin()
            if str(v).endswith("_next")
        }
    )
    return simplified_ltl


def ltl_to_propositional(formula):
    if isinstance(formula, Value) or isinstance(formula, Variable):
        return formula
    elif isinstance(formula, BiOp):
        if formula.op in ["U", "W", "R", "M"]:
            raise Exception(
                "ltl_to_propositional: I can only handle propositional formulas with next "
                + str(formula)
            )
        return BiOp(
            ltl_to_propositional(formula.left),
            formula.op,
            ltl_to_propositional(formula.right),
        )
    elif isinstance(formula, UniOp):
        if formula.op == "X":
            vars = formula.right.variablesin()
            to_next = {v: Variable(str(v) + "_next") for v in vars}
            return ltl_to_propositional(formula.right.replace(to_next))
        else:
            return UniOp(formula.op, ltl_to_propositional(formula.right))
    else:
        raise Exception(
            "ltl_to_propositional: I do not know how to handle " + str(formula)
        )


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

    if len(f.ops_used()) <= 1:
        return f

    if not symbol_table:
        symbol_table = {str(v): BOOLEAN for v in f.variablesin()}
    try:
        simple_f = only_dis_or_con_junctions(f)
        simple_f = propagate_negations(simple_f)
        simple_f_without_math, dic = simple_f.replace_math_exprs(symbol_table)
        if simplify:
            simple_f_without_math = simplify_formula_without_math(simple_f_without_math)

        if (
            isinstance(simple_f_without_math, BiOp)
            and simple_f_without_math.op == BoolBiOps.DISJ
        ):
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
            new_disjunct = new_disjunct.replace(
                {Variable(key): value for key, value in dic.items()}
            )

            new_disjuncts.append(new_disjunct)

        in_dnf_math_back = disjunct_formula_set(new_disjuncts)

        return in_dnf_math_back
    except Exception as e:
        raise Exception(
            "dnf: I do not know how to handle "
            + str(f)
            + ", cannot turn it into dnf. "
            + str(e)
        )


def dnf_with_timeout(f: Formula, symbol_table: dict = None, simplify=True, timeout=0.3):
    if isinstance(f, Value) or isinstance(f, MathExpr):
        return f

    if not symbol_table:
        symbol_table = {str(v): BOOLEAN for v in f.variablesin()}

    success, ret = run_with_timeout(dnf, [f, symbol_table, simplify], timeout=timeout)

    if success:
        dnf_cache[f] = ret
        return ret
    else:
        return f


def cnf_with_timeout(f: Formula, symbol_table: dict = None, simplify=True, timeout=0.3):
    if isinstance(f, Value) or isinstance(f, MathExpr):
        return f

    if not symbol_table:
        symbol_table = {str(v): BOOLEAN for v in f.variablesin()}

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
        return cnf(f, symbol_table)
    else:
        return cnf_with_timeout(f, symbol_table, simplify, timeout)


cnf_cache = {}


def cnf(f: Formula, symbol_table: dict = None):
    if not symbol_table:
        symbol_table = {str(v): BOOLEAN for v in f.variablesin()}
    try:
        simple_f = only_dis_or_con_junctions(f)
        simple_f = propagate_negations(simple_f).simplify()
        simple_f_without_math, dic = simple_f.replace_math_exprs(symbol_table)
        simple_f_without_math = simplify_formula_without_math(simple_f_without_math)
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
        if not dic:
            in_cnf_math_back = in_cnf_formula
        else:
            in_cnf_math_back = in_cnf_formula.replace(
                {Variable(key): value for key, value in dic.items()}
            )

        cnf_cache[f] = in_cnf_math_back

        return in_cnf_math_back
    except Exception as e:
        raise Exception(
            "cnf: I do not know how to handle "
            + str(f)
            + ", cannot turn it into cnf."
            + str(e)
        )


def append_to_variable_name(formula, vars_names, suffix):
    return formula.replace(
        lambda v: Variable(v.name + suffix) if v in vars_names else v
    )


def mutually_exclusive_rules(states):
    return [
        str(s)
        + " -> "
        + str(
            conjunct_formula_set([neg(Variable(str(ss))) for ss in states if ss != s])
        )
        for s in states
    ]


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
    return conjunct_formula_set(
        set({type_constraint(v, symbol_table) for v in formula.variablesin()})
    )


def type_constraints_acts(transition, symbol_table):
    acts = transition.action
    constraints = []
    for act in acts:
        if act.right != act.left:
            constraint = type_constraint(act.left, symbol_table).replace(
                {act.left: act.right}
            )
            if sat(conjunct(transition.condition, neg(constraint)), symbol_table):
                constraints.append(constraint)
    return conjunct_formula_set(constraints)


def action_constraints(transition, symbol_table):
    acts = transition.action
    constraints = []
    for act in acts:
        if act.right != act.left:
            constraint = type_constraint(act.left, symbol_table).replace(
                {act.left: act.right}
            )
            if sat(conjunct(transition.condition, neg(constraint)), symbol_table):
                constraints.append(constraint)
    return conjunct_formula_set(constraints)


def type_constraint(variable, symbol_table):
    if str(variable) not in symbol_table.keys():
        raise Exception(f"{str(variable)} not in symbol table.")
    type = symbol_table[str(variable)]

    if isinstance(variable, Variable):
        if type == INTEGER:
            return Value(BoolAtoms.TRUE)
        elif type == BOOLEAN:
            return Value(BoolAtoms.TRUE)
        elif type == NATURAL:
            return MathExpr(BiOp(variable, ">=", Value("0")))
        elif type.interval:
            return BiOp(
                MathExpr(
                    BiOp(
                        variable,
                        (">=" if type.interval.lower_inclusive else ">"),
                        Value(type.interval.lower),
                    )
                ),
                "&&",
                MathExpr(
                    BiOp(
                        variable,
                        ("<=" if type.interval.lower_inclusive else "<"),
                        Value(type.interval.upper),
                    )
                ),
            )
        else:
            raise NotImplementedError(f"Type {type} unsupported.")
    else:
        raise Exception(f"{str(variable)} not a variable.")


def propagate_negations(formula: Formula):
    if isinstance(formula, UniOp):
        if formula.op == "!":
            return negate(propagate_negations(formula.right))
        else:
            return UniOp(formula.op, propagate_negations(formula.right))
    elif isinstance(formula, BiOp):
        return BiOp(
            propagate_negations(formula.left),
            formula.op,
            propagate_negations(formula.right),
        )
    else:
        return formula


def negate(formula):
    if isinstance(formula, UniOp):
        if formula.op == "!":
            return formula.right
        else:
            return UniOp(formula.op, negate(formula.right))
    elif isinstance(formula, BiOp):
        if formula.op == "&":
            return BiOp(negate(formula.left), "|", negate(formula.right))
        elif formula.op == "|":
            return BiOp(negate(formula.left), "&", negate(formula.right))
        elif formula.op == "->":
            return BiOp(formula.left, "&", negate(formula.right))
        elif formula.op == "<->":
            return BiOp(
                BiOp(formula.left, "&", negate(formula.right)),
                "|",
                BiOp(negate(formula.left), "&", formula.right),
            )
        elif formula.op == ">":
            return BiOp(formula.left, "<=", formula.right)
        elif formula.op == "<":
            return BiOp(formula.left, ">=", formula.right)
        elif formula.op == ">":
            return BiOp(formula.left, "<=", formula.right)
        elif formula.op == ">=":
            return BiOp(formula.left, "<", formula.right)
        elif formula.op == "<=":
            return BiOp(formula.left, ">", formula.right)
        elif formula.op == "=" or formula.op == "==":
            return BiOp(
                BiOp(formula.left, ">", formula.right),
                "|",
                BiOp(formula.left, "<", formula.right),
            )
        else:
            return UniOp("!", formula)
    else:
        return UniOp("!", formula).simplify()


def resolve_implications(formula):
    if isinstance(formula, UniOp):
        if formula.op == "!":
            return UniOp("!", resolve_implications(formula.right))
        else:
            return UniOp(formula.op, resolve_implications(formula.right))
    elif isinstance(formula, BiOp):
        if formula.op == "->" or formula.op == "=>":
            return BiOp(
                neg(resolve_implications(formula.left)),
                "|",
                resolve_implications(formula.right),
            )
        elif formula.op == "<->" or formula.op == "<=>":
            return BiOp(
                BiOp(
                    neg(resolve_implications(formula.left)),
                    "|",
                    resolve_implications(formula.right),
                ),
                "&",
                BiOp(
                    (resolve_implications(formula.left)),
                    "|",
                    neg(resolve_implications(formula.right)),
                ),
            )
        else:
            return BiOp(
                resolve_implications(formula.left),
                formula.op,
                resolve_implications(formula.right),
            )
    elif isinstance(formula, MathExpr):
        return MathExpr((formula.formula))
    else:
        return formula


def keep_only_vars(formula, vars_to_keep, make_program_choices_explicit=False):
    to_project_out = [v for v in formula.variablesin() if v not in vars_to_keep]
    return project_out_vars_int(
        propagate_negations(formula),
        to_project_out,
        True,
        make_program_choices_explicit,
    )


def keep_only_vars_inverse(formula, vars_to_keep):
    to_project_out = [v for v in formula.variablesin() if v not in vars_to_keep]
    return project_out_vars_int(propagate_negations(formula), to_project_out, False)


def project_out_vars_inverse(formula, vars_to_project_out):
    return project_out_vars_int(
        propagate_negations(formula), vars_to_project_out, False
    )


def project_out_vars(formula, vars_to_project_out, make_program_choices_explicit=False):
    return project_out_vars_int(
        propagate_negations(formula),
        vars_to_project_out,
        True,
        make_program_choices_explicit,
    )


def project_out_vars_int(
    formula,
    vars_to_project_out,
    make_true,
    make_program_choices_explicit=False,
):
    program_choice = (
        Variable("program_choice")
        if make_program_choices_explicit
        else Value(BoolAtoms.FALSE)
    )
    if isinstance(formula, Value):
        return formula
    elif isinstance(formula, Variable):
        if formula in vars_to_project_out:
            return Value(BoolAtoms.TRUE) if make_true else program_choice
        else:
            return formula
    elif isinstance(formula, UniOp):
        if not isinstance(formula.right, Value) and not isinstance(
            formula.right, Variable
        ):
            raise Exception("propagate negations before calling project_out_vars")
        if formula.right in vars_to_project_out:
            return Value(BoolAtoms.TRUE) if make_true else program_choice
        else:
            return formula
    elif isinstance(formula, BiOp):
        vars_in_formula = formula.variablesin()
        if not any(v not in vars_to_project_out for v in vars_in_formula):
            return Value(BoolAtoms.TRUE) if make_true else program_choice
        elif not any(v in vars_to_project_out for v in vars_in_formula):
            return formula
        else:
            make_true = (
                formula.op == BoolBiOps.CONJ
            )  # if make_true else formula.op == "|"
            return BiOp(
                project_out_vars_int(formula.left, vars_to_project_out, make_true),
                formula.op,
                project_out_vars_int(formula.right, vars_to_project_out, make_true),
            )
    else:
        raise Exception("not implemented")


def partially_evaluate(
    formula, true_vars: [Variable], false_vars: [Variable], symbol_table
):
    new_formula = formula
    for v in true_vars:
        if not isinstance(v, Variable):
            raise Exception(
                "partially_evaluate: element "
                + str(v)
                + " of true_vars is not a variable"
            )
        new_formula = new_formula.replace({v: true()})
    for v in false_vars:
        if not isinstance(v, Variable):
            raise Exception(
                "partially_evaluate: element "
                + str(v)
                + " of false_vars is not a variable"
            )
        new_formula = new_formula.replace({v, false()})

    new_formula_simplified = new_formula.simplify()
    new_formula_simplified_more = simplify_formula_with_math(
        new_formula_simplified, symbol_table
    )

    return new_formula_simplified_more


def is_atomic(f):
    return (
        isinstance(f, Variable)
        or isinstance(f, Value)
        or isinstance(f, MathExpr)
        or (isinstance(f, UniOp) and is_atomic(f.right))
        or should_be_math_expr(f)
    )


def is_conjunction_of_atoms(formula):
    if isinstance(formula, BiOp) and formula.op == BoolBiOps.CONJ:
        for f in formula.sub_formulas_up_to_associativity():
            if is_atomic(f):
                continue
            if isinstance(f, BiOp) and f.op == BoolBiOps.CONJ:
                if any(
                    not is_atomic(ff) for ff in f.sub_formulas_up_to_associativity()
                ):
                    return False
            else:
                return False
        return True
    elif is_atomic(formula):
        return True
    else:
        return False


def is_conjunction_of_atoms_modulo_vars(formula, synt_props):
    if isinstance(formula, BiOp) and formula.op == BoolBiOps.CONJ:
        for f in formula.sub_formulas_up_to_associativity():
            if is_atomic(f):
                continue
            if not any(v for v in f.variablesin() if v not in synt_props):
                continue
            if isinstance(f, BiOp) and f.op == BoolBiOps.CONJ:
                if any(
                    not is_atomic(ff) for ff in f.sub_formulas_up_to_associativity()
                ):
                    return False
            else:
                return False
        return True
    elif is_atomic(formula):
        return True
    else:
        return False


def is_disjunction_of_atoms(formula):
    if isinstance(formula, BiOp) and formula.op == "|":
        for f in formula.sub_formulas_up_to_associativity():
            if is_atomic(f):
                continue
            if isinstance(f, BiOp) and f.op == "|":
                if any(
                    not is_atomic(ff) for ff in f.sub_formulas_up_to_associativity()
                ):
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
        if formula.op == "|":
            for f in formula.sub_formulas_up_to_associativity():
                return is_conjunction_of_atoms(f)
        elif formula.op == "&":
            return is_conjunction_of_atoms(formula)
        else:
            return is_atomic(formula)
    elif isinstance(formula, UniOp):
        if formula.op == "!":
            return is_atomic(formula.right)
        else:
            return False
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
        right_form, new_dict = abstract_out_conjunctions_of_atoms(
            formula.right, new_dict
        )
        return BiOp(left_form, formula.op, right_form), new_dict
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
        right_form, new_dict = abstract_out_disjunctions_of_atoms(
            formula.right, new_dict
        )
        return BiOp(left_form, formula.op, right_form), new_dict
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


def should_be_math_expr(formula):
    if isinstance(formula, BiOp):
        if formula.op in ["<", ">", "<=", ">=", MathRels.EQ, "!="]:
            return True
    return False


def atomic_predicates(formula) -> set[Formula]:
    if isinstance(formula, Value):
        return set()
    elif isinstance(formula, Update):
        return set()
    elif (
        isinstance(formula, Variable)
        or isinstance(formula, MathExpr)
        or should_be_math_expr(formula)
    ):
        return {formula}
    else:
        if isinstance(formula, UniOp):
            return atomic_predicates(formula.right)
        elif isinstance(formula, BiOp):
            return atomic_predicates(formula.left) | atomic_predicates(formula.right)
        elif isinstance(formula, Update):
            return atomic_predicates(formula.formula)
        else:
            raise Exception("atomic_predicates: not implemented for " + str(formula))


def run_with_timeout_and_memory_limit(f, args, timeout, max_memory_gb):
    import time
    import resource
    from multiprocessing import Process, Manager

    if timeout == -1:
        return True, f(*args)

    with Manager() as manager:
        result_dict = manager.dict()

        def target(func, func_args, shared_dict, memory_limit_gb):
            try:
                memory_bytes = int(memory_limit_gb * 1024 * 1024 * 1024)
                resource.setrlimit(resource.RLIMIT_AS, (memory_bytes, memory_bytes))
                result = func(*func_args)
                shared_dict["status"] = "success"
                shared_dict["result"] = result
            except MemoryError:
                shared_dict["status"] = "oom"
            except BrokenPipeError:
                pass
            except Exception as e:
                shared_dict["status"] = "error"
                shared_dict["result"] = str(e)

        process = Process(target=target, args=(f, args, result_dict, max_memory_gb))
        process.start()

        start_time = time.time()
        while time.time() - start_time < timeout:
            if not process.is_alive():
                break
            time.sleep(0.01)

        process.terminate()
        process.join(1.0)

        status = result_dict.get("status", None)
        result = result_dict.get("result", None)

        if status == "success":
            return True, result
        elif status == "oom":
            return False, "Memory limit exceeded"
        elif status == "error":
            return False, result
        else:
            return False, "Timeout"


def run_with_timeout(f, args, timeout):
    import time
    import multiprocessing
    from multiprocessing import Process, Manager

    if timeout == -1:
        return True, f(*args)

    # Use Manager for shared objects
    with Manager() as manager:
        result_dict = manager.dict()
        result_dict["status"] = "running"

        def target(func, func_args, shared_dict):
            try:
                result = func(*func_args)
                shared_dict["status"] = "success"
                shared_dict["result"] = result
            except Exception as e:
                shared_dict["status"] = "error"
                shared_dict["error"] = str(e)

        process = Process(target=target, args=(f, args, result_dict))
        process.start()

        # Polling approach
        start_time = time.time()
        poll_interval = 0.01

        while time.time() - start_time < timeout:
            if not process.is_alive():
                # Process finished
                process.join()

                if result_dict["status"] == "success":
                    return True, result_dict.get("result", None)
                else:
                    return False, None

            time.sleep(poll_interval)

        # Timeout occurred
        if process.is_alive():
            process.terminate()
            time.sleep(0.01)
            if process.is_alive():
                process.kill()
            process.join(timeout=0.1)

        return False, None


def run_with_timeout_pickled(f, args, timeout):
    import time
    import tempfile
    import pickle
    import os
    from multiprocessing import Process

    if timeout == -1:
        return True, f(*args)

    # Create a temporary file for result communication
    with tempfile.NamedTemporaryFile(delete=False) as temp_file:
        result_file = temp_file.name

    def target(func, func_args, result_path):
        try:
            result = func(*func_args)
            with open(result_path, "wb") as f:
                pickle.dump(("success", result), f)
        except Exception as e:
            with open(result_path, "wb") as f:
                pickle.dump(("error", e), f)

    process = Process(target=target, args=(f, args, result_file))
    process.start()

    # Polling with file-based communication
    start_time = time.time()
    poll_interval = 0.1

    while time.time() - start_time < timeout:
        if not process.is_alive():
            # Process finished, check for result file
            if os.path.exists(result_file) and os.path.getsize(result_file) > 0:
                try:
                    with open(result_file, "rb") as f:
                        status, result = pickle.load(f)
                    process.join()
                    os.unlink(result_file)  # Clean up temp file
                    return (status == "success"), result
                except (pickle.PickleError, EOFError):
                    # File corrupted or incomplete
                    pass

            # Process finished but no valid result
            process.join()
            try:
                os.unlink(result_file)
            except:
                pass
            return False, None

        time.sleep(poll_interval)

    # Timeout occurred
    success = False
    result = None

    # Try to get any result before cleanup
    if os.path.exists(result_file) and os.path.getsize(result_file) > 0:
        try:
            with open(result_file, "rb") as f:
                status, result = pickle.load(f)
            success = status == "success"
        except:
            pass

    # Force cleanup
    if process.is_alive():
        process.terminate()
        time.sleep(0.5)
        if process.is_alive():
            process.kill()
        process.join(timeout=2)

    # Clean up temp file
    try:
        os.unlink(result_file)
    except:
        pass

    return success, result


def flatten_effects(
    effects: [(frozenset[Formula], frozenset[frozenset[Formula]])],
    preds,
    rename_pred,
):
    nows = [set(now) for now, _ in effects]
    common_nows = set.intersection(*nows)

    reduced_effects = [(now.difference(common_nows), nexts) for now, nexts in effects]
    common_now_preds = list(
        {p for p in preds for now, _ in reduced_effects if p in now or neg(p) in now}
    )
    common_now_preds.sort(
        key=lambda p: abs(
            len([p for now, _ in reduced_effects if p in now])
            - len([p for now, _ in reduced_effects if neg(p) in now])
        ),
    )

    nexts = [set(next) for _, nexts in reduced_effects for next in nexts]
    common_nexts = set.intersection(*nexts)
    reduced_effects = [
        (now, {next.difference(common_nexts)})
        for now, nexts in reduced_effects
        for next in nexts
    ]

    precondition = conjunct_formula_set([rename_pred(p) for p in common_nows])
    postcondition = conjunct_formula_set([rename_pred(p) for p in common_nexts])
    formula = take_out_predicate(reduced_effects, common_now_preds, rename_pred)
    formula = conjunct(conjunct(precondition, postcondition), formula)
    # TODO remove X TRUE
    return formula


def take_out_predicate(
    effects: [(frozenset[Formula], frozenset[frozenset[Formula]])],
    preds: list,
    rename_pred,
):
    if len(preds) == 0:
        formula = disjunct_formula_set(
            [
                conjunct(
                    conjunct_formula_set([rename_pred(n) for n in now]),
                    disjunct_formula_set(
                        [
                            X(conjunct_formula_set([rename_pred(n) for n in next]))
                            for next in nexts
                        ]
                    ),
                )
                for now, nexts in effects
            ]
        )
    else:
        p = preds[0]
        p_true = [(now.difference({p}), nexts) for now, nexts in effects if p in now]
        p_false = [
            (now.difference({neg(p)}), nexts) for now, nexts in effects if neg(p) in now
        ]
        true_formula = take_out_predicate(p_true, preds[1:], rename_pred)
        false_formula = take_out_predicate(p_false, preds[1:], rename_pred)

        true_formula = simplify_formula_with_next(true_formula)
        false_formula = simplify_formula_with_next(false_formula)
        true_formula = true_formula.replace_formulas(
            lambda x: (
                Value("true")
                if isinstance(x, UniOp)
                and x.op == "X"
                and isinstance(x.right, Value)
                and x.right.is_true()
                else None
            )
        )
        false_formula = false_formula.replace_formulas(
            lambda x: (
                Value("true")
                if isinstance(x, UniOp)
                and x.op == "X"
                and isinstance(x.right, Value)
                and x.right.is_true()
                else None
            )
        )

        if true_formula == false_formula:
            formula = true_formula
        else:
            formula = disjunct(
                conjunct(rename_pred(p), true_formula),
                conjunct(neg(rename_pred(p)), false_formula),
            )

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
        return disjunct_formula_set(
            [
                conjunct(
                    conjunct_formula_set(preds),
                    disjunct_formula_set([conjunct_formula_set(r) for r in rest]),
                )
                for preds, rest in associated_formula.items()
            ]
        )

    associated_formula = {frozenset(): disjuncts_of_conjuncts}

    if len(preds) == 0:
        return associated_formula_dict_to_formula(associated_formula)

    common_preds = set(
        v
        for D in disjuncts_of_conjuncts
        for d in D
        for v in d.variablesin()
        if v in preds
    )
    preds = common_preds
    # sort according to most common
    preds = sorted(
        preds,
        key=lambda p: sum(1 for D in disjuncts_of_conjuncts if p in D),
        reverse=True,
    )

    logging.info("Trying to take out preds from dnf formula")
    prev_formula = associated_formula_dict_to_formula(associated_formula)
    cnt = 0
    for pred in preds:
        new_associated_formula = {}

        for prev_preds, set_of_disjuncts in associated_formula.items():
            (
                pred_true_disjuncts,
                pred_false_disjuncts,
                others_at,
            ) = take_out_pred(set_of_disjuncts, pred)
            if len(pred_true_disjuncts) > 0:
                if frozenset(prev_preds | {pred}) not in new_associated_formula.keys():
                    new_associated_formula[frozenset(prev_preds | {pred})] = set()
                new_associated_formula[frozenset(prev_preds | {pred})].update(
                    pred_true_disjuncts
                )

            if len(pred_false_disjuncts) > 0:

                if (
                    frozenset(prev_preds | {neg(pred)})
                    not in new_associated_formula.keys()
                ):
                    new_associated_formula[frozenset(prev_preds | {neg(pred)})] = set()
                new_associated_formula[frozenset(prev_preds | {neg(pred)})].update(
                    pred_false_disjuncts
                )

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


def take_out_pred_sat(disjuncts: list[Formula], pred: Variable, symbol_table):
    true_at = set()
    false_at = set()
    others_at = set()
    for disjunct in disjuncts:
        if not sat(conjunct(disjunct, neg(pred)), symbol_table):
            true_at.add(disjunct.replace({pred, true()}))
        elif not sat(conjunct(disjunct, pred), symbol_table):
            false_at.add(disjunct.replace({pred: false()}))
        else:
            others_at.add(disjunct)

    return true_at, false_at, others_at


def take_out_preds_sat(disjuncts: [Formula], preds: [Formula], symbol_table):
    def associated_formula_dict_to_formula(associated_formula):
        return disjunct_formula_set(
            [
                conjunct(conjunct_formula_set(preds), disjunct_formula_set(rest))
                for preds, rest in associated_formula.items()
            ]
        )

    associated_formula = {frozenset(): disjuncts}

    if len(preds) == 0:
        return associated_formula_dict_to_formula(associated_formula)

    logging.info("Trying to take out preds from disjunction of formulas")
    prev_formula = associated_formula_dict_to_formula(associated_formula)
    cnt = 0
    for pred in preds:
        new_associated_formula = {}

        for prev_preds, set_of_disjuncts in associated_formula.items():
            (
                pred_true_disjuncts,
                pred_false_disjuncts,
                others_at,
            ) = take_out_pred_sat(set_of_disjuncts, pred, symbol_table)
            if len(pred_true_disjuncts) > 0:
                if frozenset(prev_preds | {pred}) not in new_associated_formula.keys():
                    new_associated_formula[frozenset(prev_preds | {pred})] = set()
                new_associated_formula[frozenset(prev_preds | {pred})].update(
                    pred_true_disjuncts
                )

            if len(pred_false_disjuncts) > 0:

                if (
                    frozenset(prev_preds | {neg(pred)})
                    not in new_associated_formula.keys()
                ):
                    new_associated_formula[frozenset(prev_preds | {neg(pred)})] = set()
                new_associated_formula[frozenset(prev_preds | {neg(pred)})].update(
                    pred_false_disjuncts
                )

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


def normalize_ltl(formula: Formula):
    if isinstance(formula, BiOp):
        n_left = normalize_ltl(formula.left)
        n_right = normalize_ltl(formula.right)
        if formula.op == "W":
            return disjunct(G(n_left), U(n_left, n_right))
        elif formula.op == "R":
            return neg(U(neg(n_left), neg(n_right)))
        elif formula.op == "M":
            return U(n_right, conjunct(n_left, n_right))
        else:
            return BiOp(n_left, formula.op, n_right)
    elif isinstance(formula, UniOp):
        return UniOp(formula.op, normalize_ltl(formula.right))
    else:
        return formula


predicate_to_var_cache = {}
var_to_predicate_cache = {}


def is_predicate_var(p):
    if isinstance(p, str):
        p = Variable(p)
    if str(p) in var_to_predicate_cache.keys():
        return True
    else:
        return False


def var_to_predicate(p):
    if str(p) in var_to_predicate_cache.keys():
        return var_to_predicate_cache[str(p)]
    elif (
        isinstance(p, UniOp)
        and p.op == "!"
        and str(p.right) in var_to_predicate_cache.keys()
    ):
        return neg(var_to_predicate_cache[str(p.right)])
    elif str(neg(p)) in var_to_predicate_cache.keys():
        return neg(var_to_predicate_cache[str(neg(p))].right)
    else:
        raise Exception("Could not find predicate for variable: " + str(p))


def label_pred(p, preds):
    if not isinstance(p, Formula):
        raise Exception(f"{p} is not a formula")
    if p in predicate_to_var_cache.keys():
        return predicate_to_var_cache[p]

    if p not in preds:
        representation = stringify_pred_take_out_neg(p)
    else:
        representation = stringify_pred(p)

    predicate_to_var_cache[strip_outer_mathexpr(p)] = representation
    var_to_predicate_cache[str(representation)] = p
    return representation


def stringify_pred(p):
    if strip_outer_mathexpr(p) in predicate_to_var_cache.keys():
        return predicate_to_var_cache[strip_outer_mathexpr(p)]

    representation = Variable(
        "pred_"
        + str(p)
        .replace(" ", "")
        .replace("_", "")
        .replace("(", "_")
        .replace(")", "_")
        .replace("<=>", "_IFF_")
        .replace("<->", "_IFF_")
        .replace("<=", "_LTEQ_")
        .replace(">=", "_GTEQ_")
        .replace("=>", "_IMPLIES_")
        .replace("->", "_IMPLIES_")
        .replace("=", "_EQ_")
        .replace(":=", "_ASSIGN_")
        .replace(">", "_GT_")
        .replace("<", "_LT_")
        .replace("+ -", "_SUB_")
        .replace("-", "_MINUS_")
        .replace("+", "_ADD_")
        .replace("/", "_DIV_")
        .replace("*", "_MULT_")
        .replace("%", "_MOD_")
        .replace("!", "_NEG_")
        .replace("&&", "_AND_")
        .replace("&", "_AND_")
        .replace("|", "_OR_")
        .replace("||", "_OR_")
    )
    predicate_to_var_cache[strip_outer_mathexpr(p)] = representation
    var_to_predicate_cache[str(representation)] = p
    return representation


def stringify_term(p):
    representation = (
        str(p)
        .replace(" + -", "_sub_")
        .replace(" + ", "_add_")
        .replace("-", "_min_")
        .replace("(", "")
        .replace(")", "")
    )

    return representation


def stringify_pred_take_out_neg(p):
    res = None
    if isinstance(p, UniOp) and p.op == "!":
        res = neg(stringify_pred(p.right))
    else:
        res = stringify_pred(p)
    if res == None:
        raise Exception("Could not stringify predicate: " + str(p))
    else:
        return res


def label_preds(ps, preds):
    return {label_pred(p, preds) for p in ps}


def stringify_formula(f, env_con_props):
    if isinstance(f, MathExpr) or should_be_math_expr(f):
        return stringify_pred(f), [f]
    elif isinstance(f, BiOp):
        new_left, left_preds = stringify_formula(f.left, env_con_props)
        new_right, right_preds = stringify_formula(f.right, env_con_props)
        return BiOp(new_left, f.op, new_right), left_preds + right_preds
    elif isinstance(f, UniOp):
        new_right, right_preds = stringify_formula(f.right, env_con_props)
        return UniOp(f.op, new_right), right_preds
    elif isinstance(f, Variable) and f not in env_con_props:
        return stringify_pred(f), [f]
    else:
        return f, []


def finite_state_preds(variable: Variable, type: Type) -> list[Formula]:
    if not is_finite(type):
        raise ValueError(f"Variable '{variable}' is not finite-state")
    if type == BOOLEAN:
        return [variable]
    elif isinstance(type, Number) and (
        type.number_type == BaseNumberTypes.natural
        or type.number_type == BaseNumberTypes.integer
    ):
        lo, hi = interval_range(type)
        return [MathExpr(BiOp(variable, "=", Value(str(x)))) for x in range(lo, hi + 1)]
    else:
        raise ValueError(f"Variable '{variable} has unknown type {type}'")


def ltl_back_to_vars(formula):
    if isinstance(formula, Value):
        return formula
    elif isinstance(formula, Variable):
        if str(formula) in var_to_predicate_cache.keys():
            return var_to_predicate_cache[str(formula)]
        else:
            return formula
    elif isinstance(formula, MathExpr):
        return MathExpr(ltl_back_to_vars(formula))
    elif isinstance(formula, UniOp):
        return UniOp(formula.op, ltl_back_to_vars(formula.right))
    elif isinstance(formula, BiOp):
        return BiOp(
            ltl_back_to_vars(formula.left),
            formula.op,
            ltl_back_to_vars(formula.right),
        )
    else:
        raise Exception("not implemented")


def normalise_mathexpr(mathexpr):
    f = None
    if isinstance(mathexpr, MathExpr):
        f = mathexpr.formula
    elif should_be_math_expr(mathexpr):
        f = mathexpr
    else:
        return None

    rewrite_lte = lambda x, y: MathExpr(BiOp(x, "<=", y))

    if isinstance(f, BiOp):
        if f.op == "<=":
            return rewrite_lte(f.left, f.right)
        elif f.op == ">=":
            return rewrite_lte(f.right, f.left)
        elif f.op == "<":
            f_le_than = rewrite_lte(f.left, f.right)
            f_not_gte_than = neg(rewrite_lte(f.right, f.left))
            return conjunct(f_le_than, f_not_gte_than)
        elif f.op == ">":
            f_le_than = rewrite_lte(f.right, f.left)
            f_not_gte_than = neg(rewrite_lte(f.left, f.right))
            return conjunct(f_le_than, f_not_gte_than)
        elif f.op == "=":
            new_f1 = rewrite_lte(f.left, f.right)
            new_f2 = rewrite_lte(f.right, f.left)
            return conjunct(new_f1, new_f2)
        elif f.op == "!=":
            new_f1 = neg(rewrite_lte(f.left, f.right))
            new_f2 = neg(rewrite_lte(f.right, f.left))
            return disjunct(new_f1, new_f2)

    return None


def ranking_from_predicate(predicate):
    if isinstance(predicate, MathExpr) or should_be_math_expr(predicate):
        p = strip_outer_mathexpr(predicate)
        if p.op == "<=":
            if len(p.left.variablesin()) == 0:
                return p.right, predicate.formula
            else:
                if len(p.right.variablesin()) == 0:
                    return BiOp(Value("0"), "-", p.left), p
            return BiOp(p.right, "-", p.left), predicate.formula
        if p.op == "<":
            if len(p.left.variablesin()) == 0:
                return p.right, predicate.formula
            else:
                if len(p.right.variablesin()) == 0:
                    return BiOp(Value("0"), "-", p.left), p

            return BiOp(p.right, "-", p.left), predicate.formula
    return None


def normalise_formula(f, signatures, symbol_table, ignore_these=None):
    if ignore_these is None:
        ignore_these = []
    preds = atomic_predicates(f)
    if len(preds) == 0:
        return f, set()
    preds = [p for p in preds if p not in ignore_these]
    old_to_new = {}
    new_preds = set()
    for pp in preds:
        if len(pp.variablesin()) == 0:
            if is_tautology(pp, {}):
                old_to_new[pp] = true()
            else:
                old_to_new[pp] = false()
        else:
            result = normalise_pred_multiple_vars(pp, signatures, symbol_table)
            if isinstance(result, Variable) or len(result) == 1:
                old_to_new[pp] = result
                new_preds.add(result)
            else:
                sig, new_pred, preds = result
                old_to_new[pp] = new_pred
                signatures.add(sig)
                new_preds.update(result[2])

    return f.replace_formulas(old_to_new), new_preds


# preds here may be use in structural refinements, careful
def normalise_predicate_old(pred, signatures, symbol_table) -> (Formula, [Formula]):
    pred = strip_outer_mathexpr(pred)
    if isinstance(pred, BiOp) and (pred.op == "==" or pred.op == "="):
        pred1 = BiOp(pred.left, "<=", pred.right)
        pred2 = BiOp(pred.right, "<=", pred.left)

        signature1, rep1, preds1 = normalise_pred_multiple_vars(
            pred1, signatures, symbol_table
        )
        signature2, rep2, preds2 = normalise_pred_multiple_vars(
            pred2, signatures, symbol_table
        )

        return conjunct(rep1, rep2), [
            (signature1, preds1),
            (signature2, preds2),
        ]
    elif isinstance(pred, BiOp) and pred.op == "!=":
        pred1 = BiOp(pred.left, "<", pred.right)
        pred2 = BiOp(pred.right, "<", pred.left)

        signature1, rep1, preds1 = normalise_pred_multiple_vars(
            pred1, signatures, symbol_table
        )
        signature2, rep2, preds2 = normalise_pred_multiple_vars(
            pred2, signatures, symbol_table
        )

        return disjunct(rep1, rep2), [
            (signature1, preds1),
            (signature2, preds2),
        ]
    else:
        signature, p, preds = normalise_pred_multiple_vars(
            pred, signatures, symbol_table
        )
        return p, [(signature, preds)]


def normalise_pred_with_var_on_one_side(pred, v):
    try:
        sympy_pred = sympy.solve(pred.to_sympy(), v.to_sympy())
    except Exception as e:
        raise Exception(e)
    preds = str(sympy_pred).split(" & ")
    if len(preds) > 1:
        preds = [
            string_to_prop(p)
            for p in preds
            if "oo <" not in p
            and "oo >" not in p
            and "> oo" not in p
            and "< oo" not in p
            and "> -oo" not in p
            and "< -oo" not in p
        ]
    if len(preds) > 1:
        raise Exception(
            "Predicate " + ", ".join(map(str, preds)) + " has more than one conjunct"
        )
    elif len(preds) == 0:
        raise Exception("Sympy predicate " + str(sympy_pred) + " is not well-formed")

    pred_with_var_on_one_side = strip_outer_mathexpr(string_to_prop(str(preds[0])))

    if isinstance(pred_with_var_on_one_side, BiOp):
        if pred_with_var_on_one_side.op == "<":
            # x < c is good already
            if pred_with_var_on_one_side.left == v:
                return pred_with_var_on_one_side, [pred_with_var_on_one_side]
            else:
                # of form c < x -> x > c -> ! x <= c
                new_pred = BiOp(
                    pred_with_var_on_one_side.right,
                    "<=",
                    pred_with_var_on_one_side.left,
                )
                return neg(new_pred), [new_pred]
        elif pred_with_var_on_one_side.op == "<=":
            # x < c is good already
            if pred_with_var_on_one_side.left == v:
                return pred_with_var_on_one_side, [pred_with_var_on_one_side]
            else:
                # c <= x -> x >= c -> ! x < c
                new_pred = BiOp(
                    pred_with_var_on_one_side.right,
                    "<",
                    pred_with_var_on_one_side.left,
                )
                return neg(new_pred), [new_pred]
        elif pred_with_var_on_one_side.op == ">":
            # x > c -> !(x <= c)
            if pred_with_var_on_one_side.left == v:
                new_pred = BiOp(
                    pred_with_var_on_one_side.left,
                    "<=",
                    pred_with_var_on_one_side.right,
                )
                return neg(new_pred), [new_pred]
            else:
                # of form c > x, then can represent as x < c
                new_pred = BiOp(
                    pred_with_var_on_one_side.right,
                    "<",
                    pred_with_var_on_one_side.left,
                )
                return new_pred, [new_pred]
        elif pred_with_var_on_one_side.op == ">=":
            if pred_with_var_on_one_side.left == v:
                # x >= c -> ! x < c
                new_pred = BiOp(
                    pred_with_var_on_one_side.left,
                    "<",
                    pred_with_var_on_one_side.right,
                )
                return neg(new_pred), [new_pred]
            else:
                # c >= x -> x <= c
                new_pred = BiOp(
                    pred_with_var_on_one_side.right,
                    "<=",
                    pred_with_var_on_one_side.left,
                )
                return new_pred, [new_pred]
        elif pred_with_var_on_one_side.op == "=":
            if pred_with_var_on_one_side.right == v:
                # c == x -> c <= x and c >= x
                new_pred1 = BiOp(
                    pred_with_var_on_one_side.right,
                    "<=",
                    pred_with_var_on_one_side.left,
                )
                new_pred2 = BiOp(
                    pred_with_var_on_one_side.right,
                    "<",
                    pred_with_var_on_one_side.left,
                )
                return conjunct(new_pred1, neg(new_pred2)), [
                    new_pred1,
                    new_pred2,
                ]
            else:
                new_pred1 = BiOp(
                    pred_with_var_on_one_side.left,
                    "<=",
                    pred_with_var_on_one_side.right,
                )
                new_pred2 = BiOp(
                    pred_with_var_on_one_side.left,
                    "<",
                    pred_with_var_on_one_side.right,
                )
                return conjunct(new_pred1, neg(new_pred2)), [
                    new_pred1,
                    new_pred2,
                ]
        elif pred_with_var_on_one_side.op == "!=":
            if pred_with_var_on_one_side.right == v:
                # c == x -> c <= x and c >= x
                new_pred1 = BiOp(
                    pred_with_var_on_one_side.right,
                    "<=",
                    pred_with_var_on_one_side.left,
                )
                new_pred2 = BiOp(
                    pred_with_var_on_one_side.right,
                    "<",
                    pred_with_var_on_one_side.left,
                )
                return conjunct(new_pred1, neg(new_pred2)), [
                    new_pred1,
                    new_pred2,
                ]
            else:
                new_pred1 = BiOp(
                    pred_with_var_on_one_side.left,
                    "<=",
                    pred_with_var_on_one_side.right,
                )
                new_pred2 = BiOp(
                    pred_with_var_on_one_side.left,
                    "<",
                    pred_with_var_on_one_side.right,
                )
                return conjunct(new_pred1, neg(new_pred2)), [
                    new_pred1,
                    new_pred2,
                ]
        else:
            raise Exception(
                "Predicate "
                + str(pred_with_var_on_one_side)
                + " has an unexpected relational operator"
            )
    else:
        raise Exception(
            "Predicate " + str(pred_with_var_on_one_side) + " is not a BiOp"
        )


def normalise_pred_multiple_vars(pred, signatures, symbol_table):
    if isinstance(pred, Variable):
        return pred
    signature, pred_with_var_on_one_side = put_vars_on_left_side(strip_mathexpr(pred))
    op = pred_with_var_on_one_side.op
    vars_on_left = True
    if signature not in signatures:
        for sig in signatures:
            if is_tautology(BiOp(sig, "=", signature), symbol_table):
                signature = sig
                pred_with_var_on_one_side = BiOp(
                    sig, op, pred_with_var_on_one_side.right
                )
                break
            elif is_tautology(
                BiOp(sig, "=", UniOp(MathOps.SUB, signature)), symbol_table
            ):
                signature = sig
                new_right = propagate_minuses(
                    UniOp(MathOps.SUB, pred_with_var_on_one_side.right)
                )
                new_right = simplify_sum(new_right, {})
                pred_with_var_on_one_side = BiOp(new_right, op, sig)
                vars_on_left = False
                break

    left = pred_with_var_on_one_side.left
    right = pred_with_var_on_one_side.right

    if isinstance(pred_with_var_on_one_side, BiOp):
        if op == "<":
            # turn x < c is good already
            if vars_on_left:
                return (
                    signature,
                    pred_with_var_on_one_side,
                    [pred_with_var_on_one_side],
                )
            else:
                # of form c < x -> x > c -> ! x <= c
                new_pred = BiOp(right, "<=", left)
                return signature, neg(new_pred), [new_pred]
        elif op == "<=":
            # x <= c is good already
            if vars_on_left:
                return (
                    signature,
                    pred_with_var_on_one_side,
                    [pred_with_var_on_one_side],
                )
            else:
                # c <= x -> x >= c -> ! x < c
                new_pred = BiOp(right, "<", left)
                return signature, neg(new_pred), [new_pred]
        elif op == ">":
            # x > c -> !(x <= c)
            if vars_on_left:
                new_pred = BiOp(left, "<=", right)
                return signature, neg(new_pred), [new_pred]
            else:
                # of form c > x, then can represent as x < c
                new_pred = BiOp(right, "<", left)
                return signature, new_pred, [new_pred]
        elif op == ">=":
            if vars_on_left:
                # x >= c -> ! x < c
                new_pred = BiOp(left, "<", right)
                return signature, neg(new_pred), [new_pred]
            else:
                # c >= x -> x <= c
                new_pred = BiOp(right, "<=", left)
                return signature, new_pred, [new_pred]
        elif op == "=":
            if vars_on_left:
                # x == c -> x <= c and ! x < c
                new_pred1 = BiOp(left, "<=", right)
                new_pred2 = BiOp(left, "<", right)
                return (
                    signature,
                    conjunct(neg(new_pred2), new_pred1),
                    [new_pred1, new_pred2],
                )
            else:
                # c == x -> x <= c and ! x < c
                new_pred1 = BiOp(right, "<=", left)
                new_pred2 = BiOp(right, "<", left)
                return (
                    signature,
                    conjunct(neg(new_pred2), new_pred1),
                    [new_pred1, new_pred2],
                )
        elif op == "!=":
            if vars_on_left:
                # x != c -> !(x <= c) or x < c
                new_pred1 = BiOp(left, "<=", right)
                new_pred2 = BiOp(left, "<", right)
                return (
                    signature,
                    disjunct(neg(new_pred1), new_pred2),
                    [new_pred1, new_pred2],
                )
            else:
                new_pred1 = BiOp(right, "<=", left)
                new_pred2 = BiOp(right, "<", left)
                return (
                    signature,
                    disjunct(neg(new_pred1), new_pred2),
                    [new_pred1, new_pred2],
                )
        else:
            raise Exception(
                "Predicate "
                + str(pred_with_var_on_one_side)
                + " has an unexpected relational operator"
            )
    else:
        raise Exception(
            "Predicate " + str(pred_with_var_on_one_side) + " is not a BiOp"
        )


def put_vars_on_left_side(pred):
    # put all the variables of a Linear Integer Arithmetic inequality on one side
    # assuming op is of form <=, <, >=, >

    if isinstance(pred, BiOp):
        left_vars, left_constants = get_vars_and_constants_in_term(pred.left)
        right_vars, right_constants = get_vars_and_constants_in_term(pred.right)

        new_left_vars = left_vars + [
            propagate_minuses(UniOp(MathOps.SUB, t)) for t in right_vars
        ]
        new_left = sum(new_left_vars)

        new_right_constants = right_constants + [
            propagate_minuses(UniOp(MathOps.SUB, c)) for c in left_constants
        ]
        if len(new_right_constants) == 0:
            new_right = Value("0")
        else:
            new_right = sum(new_right_constants)

        new_left_vars.sort(key=lambda x: str(x))
        new_right = simplify_sum(new_right, {})  # this should evaluate the sum
        return new_left, BiOp(new_left, pred.op, new_right)
    else:
        raise Exception("Predicate " + str(pred) + " is not a BiOp")


def get_vars_and_constants_in_term(term):
    vars = []
    constants = []
    left_to_do = term.sub_formulas_up_to_associativity()
    while True:
        new_left_to_do = []
        if len(left_to_do) == 0:
            break
        for t in left_to_do:
            for p in t.sub_formulas_up_to_associativity():
                if isinstance(p, BiOp):
                    new_left_to_do.append(p)
                    if p in left_to_do:
                        raise Exception(
                            "Cycle detected in get_vars_and_constants_in_term"
                        )
                elif (
                    isinstance(p, UniOp) and p.op == "-" and isinstance(p.right, Value)
                ):
                    constants.append(p)
                elif isinstance(p, Value):
                    constants.append(p)
                else:
                    vars.append(p)
        left_to_do = new_left_to_do
    vars.sort(key=lambda x: str(x))
    return vars, constants


def sum(terms):
    if len(terms) == 0:
        raise Exception("No terms to sum")
    elif len(terms) == 1:
        return terms[0]
    else:
        term = terms[0]
        for i in range(1, len(terms)):
            term = BiOp(term, "+", terms[i])
        return term


def strip_outer_mathexpr(f):
    if isinstance(f, MathExpr):
        return strip_outer_mathexpr(f.formula)
    else:
        return f


def strip_mathexpr(f):
    if isinstance(f, Value) or isinstance(f, Variable):
        return f
    elif isinstance(f, MathExpr):
        return strip_mathexpr(f.formula)
    elif isinstance(f, UniOp):
        return UniOp(f.op, strip_mathexpr(f.right))
    elif isinstance(f, BiOp):
        return BiOp(strip_mathexpr(f.left), f.op, strip_mathexpr(f.right))
    else:
        return f


def math_exprs_in_formula(f):
    if isinstance(f, MathExpr) or should_be_math_expr(f):
        return {f}
    elif isinstance(f, BiOp):
        return math_exprs_in_formula(f.left) | math_exprs_in_formula(f.right)
    elif isinstance(f, UniOp):
        return math_exprs_in_formula(f.right)
    else:
        return set()


def massage_ltl_for_dual(formula: Formula, next_events, preds_too=False):
    if isinstance(formula, Value):
        return formula
    elif isinstance(formula, Variable):
        if formula in next_events:
            return X(formula)
        else:
            return formula
    elif isinstance(formula, MathExpr) or should_be_math_expr(formula):
        return formula
    elif isinstance(formula, UniOp):
        return UniOp(
            formula.op, massage_ltl_for_dual(formula.right, next_events, preds_too)
        )
    elif isinstance(formula, BiOp):
        return BiOp(
            massage_ltl_for_dual(formula.left, next_events, preds_too),
            formula.op,
            massage_ltl_for_dual(formula.right, next_events, preds_too),
        )
    else:
        return formula


def all_sat_models(preds, symbol_table):
    if len(preds) == 0:
        raise Exception("all_sat_models called with zero-sized preds")
    models = [c for c in preds[0].chain]
    for chain_pred in preds[1:]:
        new_models = []
        for m in models:
            for c in chain_pred.chain:
                new_m = conjunct(c, m)
                if sat(new_m, symbol_table):
                    new_models.append(new_m)
        models = new_models
    return models


def reset_caches(names=None):
    dnf_cache.clear()
    cnf_cache.clear()
    var_to_predicate_cache.clear()
    predicate_to_var_cache.clear()

    import sys, functools, inspect

    """Clear @lru_cache decorated functions in specified modules"""
    if names is None:
        # Clear caches in prop_lang modules by default
        names = [
            "prop_lang.biop",
            "prop_lang.formula",
            "prop_lang.uniop",
            "prop_lang.value",
        ]

    cleared_count = 0

    for module_name in names:
        if module_name in sys.modules:
            module = sys.modules[module_name]

            # Iterate through all attributes in the module
            for attr_name in dir(module):
                attr = getattr(module, attr_name)

                # Check if it's an lru_cache decorated function
                if isinstance(attr, functools._lru_cache_wrapper):
                    try:
                        attr.cache_clear()
                        cleared_count += 1
                        print(f"Cleared cache for {module_name}.{attr_name}")
                    except Exception as e:
                        print(
                            f"Failed to clear cache for {module_name}.{attr_name}: {e}"
                        )

                # Check for class methods with lru_cache
                elif inspect.isclass(attr):
                    for method_name in dir(attr):
                        method = getattr(attr, method_name)
                        if isinstance(method, functools._lru_cache_wrapper):
                            try:
                                method.cache_clear()
                                cleared_count += 1
                                print(
                                    f"Cleared cache for {module_name}.{attr_name}.{method_name}"
                                )
                            except Exception as e:
                                print(
                                    f"Failed to clear cache for {module_name}.{attr_name}.{method_name}: {e}"
                                )

    return cleared_count
