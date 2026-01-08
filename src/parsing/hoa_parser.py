import re
import config

from multiprocessing import Pool

from config import strix, semml
from parsing.string_to_ltl import string_to_prop
from prop_lang.variable import Variable


def hoa_to_transitions(hoa, realisable, parallelise=True):
    preamble_body = hoa.strip().split("--BODY--")

    hoa_preamble = preamble_body[0]
    lines = hoa_preamble.splitlines()

    hoa_dict = {n: v.strip() for n, v in [line.split(":") for line in lines[1:]]}
    aps = [a.replace('"', "") for a in hoa_dict["AP"].split(" ")[1:]]

    hoa_body = preamble_body[1].strip()
    raw_trans = hoa_body.split("State: ")[1:]
    raw_trans_with_sts = []
    cond_to_src_tgt = {}
    for sttrans in raw_trans:
        lines = sttrans.strip().split("\n")
        src = lines[0].split(" ")[0]
        if lines[-1] == "--END--":
            lines = lines[:-1]

        for l in lines[1:]:
            split = l.split("] ")
            tgt = split[-1]
            cond = split[0][1:]
            raw_trans_with_sts.append((src, cond, tgt))
            if cond in cond_to_src_tgt.keys():
                cond_to_src_tgt[cond].append((src, tgt))
            else:
                cond_to_src_tgt[cond] = [(src, tgt)]

    to_replace = {}
    for i, name in reversed(list(enumerate(aps))):
        to_replace[Variable(str(i))] = Variable(name)

    transitions = {}
    if parallelise:
        arg1 = []
        arg2 = []
        arg3 = []
        arg4 = []
        for cond in cond_to_src_tgt.keys():
            if "END--" in cond:
                break
            arg1.append(to_replace)
            arg2.append(cond)
            arg3.append(realisable)
            arg4.append(config.Config.getConfig().backend)
        with Pool(config.Config.getConfig().workers) as pool:
            results = pool.map(parse_raw_cond, zip(arg1, arg2, arg3, arg4))

        for cond, env, con in results:
            for src, tgt in cond_to_src_tgt[cond]:
                key = (src, env, tgt)
                if key in transitions.keys():
                    transitions[key].append(con)
                else:
                    transitions[key] = [con]
    else:
        for cond, src_tgts in cond_to_src_tgt.items():
            _, env, con = parse_raw_cond(
                (to_replace, cond, realisable, config.Config.getConfig().backend)
            )
            for src, tgt in src_tgts:
                key = (src, env, tgt)
                if key in transitions.keys():
                    transitions[key].append(con)
                else:
                    transitions[key] = [con]

    return hoa_dict["Start"], transitions


def parse_state_trans(to_replace, raw_tran):
    result = re.search(
        r"([\n ])*(?P<src>[0-9]+) +\"[^\"]*\"([ \n])*(?P<trans>(\[[^\[\]]+] (?P<tgt>[0-9]+)([\n ])+)+)",
        raw_tran,
    )
    # if result == None:
    #     raise Exception("Could not parse HOA:\n" + hoa)
    # else:
    src = result.group("src")
    trans = result.group("trans")
    new_trans = {}
    for line in trans.splitlines():
        if line.strip("") != "":
            search = re.search(r" *\[(?P<cond>[^\[\]]+)] (?P<tgt>[0-9]+)", line)
            tgt = search.group("tgt")
            raw_cond = search.group("cond")
            raw_cond = raw_cond.replace("t", "true")
            raw_cond = raw_cond.replace("f", "false")  # probably we don't need this
            cond = string_to_prop(raw_cond, True)
            cond = cond.replace_vars(to_replace)
            env_cond = cond.left
            con_cond = cond.right
            key = (src, env_cond, tgt)
            if key not in new_trans.keys():
                new_trans[key] = []
            new_trans[key].append(con_cond)
    return new_trans


def parse_raw_cond(arg):
    to_replace, orig_cond, realisable, backend = arg
    raw_cond = orig_cond.replace("t", "true")
    raw_cond = raw_cond.replace("f", "false")  # probably we don't need this
    cond = string_to_prop(raw_cond, True)
    cond = cond.replace_vars(to_replace)
    if backend == strix or realisable:
        env_cond = cond.left
        con_cond = cond.right
    elif backend == semml and not realisable:
        env_cond = cond.right
        con_cond = cond.left
    else:
        raise Exception("Unknown backend while parse_raw_cond: " + str(backend))
    return orig_cond, env_cond, con_cond
