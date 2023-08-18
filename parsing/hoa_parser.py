import re

from parsing.string_to_prop_logic import string_to_prop
from prop_lang.biop import BiOp
from prop_lang.variable import Variable


def hoa_to_transitions(hoa):
    preamble_body = hoa.split("--BODY--")

    hoa_preamble = preamble_body[0]
    lines = hoa_preamble.splitlines()

    hoa_dict = {n: v.strip() for n, v in [line.split(":") for line in lines[1:]]}
    aps = [a.replace('"', "") for a in hoa_dict["AP"].split(" ")[1:]]

    hoa_body = preamble_body[1].strip()
    raw_trans = hoa_body.split("State:")[1:]

    to_replace = []
    for i, name in reversed(list(enumerate(aps))):
        to_replace.append(BiOp(Variable(str(i)), ":=", Variable(name)))

    transitions = {}
    for raw_tran in raw_trans:
        result = re.search(
            r"(\n| )*(?P<src>[0-9]+) +\"[^\"]*\"( |\n)*(?P<trans>(\[[^\[\]]+\] (?P<tgt>[0-9]+)(\n| )+)+)", raw_tran)
        if result == None:
            raise Exception("Could not parse HOA:\n" + hoa)
        else:
            src = result.group("src")
            trans = result.group("trans")
            for line in trans.splitlines():
                if line.strip() != "":
                    search = re.search(r" *\[(?P<cond>[^\[\]]+)\] (?P<tgt>[0-9]+)", line)
                    tgt = search.group("tgt")
                    raw_cond = search.group("cond")
                    raw_cond = raw_cond.replace("t", "true")
                    raw_cond = raw_cond.replace("f", "false")  # probably we don't need this
                    cond = string_to_prop(raw_cond, True)
                    cond = cond.replace(to_replace)
                    # cond = cond.replace(lambda var : Variable(re.split("_loop", var.name)[0]))
                    assert isinstance(cond, BiOp)
                    key = (src, cond.left, tgt)
                    if key not in transitions.keys():
                        transitions[key] = [cond.right]
                    else:
                        transitions[key] += [cond.right]
    return hoa_dict["Start"], transitions
