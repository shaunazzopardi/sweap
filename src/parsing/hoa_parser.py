import re
import config

from multiprocessing import Pool

from config import strix, semml
from prop_lang.biop import BiOp
from prop_lang.util import false, neg, true
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
            cond = hoa_trans_cond_parser(raw_cond)
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
    cond = hoa_trans_cond_parser(orig_cond)
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


def hoa_trans_cond_parser(cond):
    raw_cond = cond.replace("t", "true").replace("f", "false")

    def tokenize(s):
        tokens = []
        i = 0
        while i < len(s):
            ch = s[i]
            if ch.isspace():
                i += 1
                continue
            if ch in ("(", ")", "!", "&", "|"):
                if ch in ("&", "|") and i + 1 < len(s) and s[i + 1] == ch:
                    tokens.append(ch)
                    i += 2
                else:
                    tokens.append(ch)
                    i += 1
                continue
            if ch.isalnum() or ch == "_":
                start = i
                while i < len(s) and (s[i].isalnum() or s[i] == "_"):
                    i += 1
                tokens.append(s[start:i])
                continue
            raise Exception("Malformed HOA transition condition: " + cond)
        return tokens

    class Parser:
        def __init__(self, tokens):
            self.tokens = tokens
            self.pos = 0

        def peek(self):
            return self.tokens[self.pos] if self.pos < len(self.tokens) else None

        def consume(self, expected=None):
            tok = self.peek()
            if tok is None:
                return None
            if expected is not None and tok != expected:
                raise Exception("Malformed HOA transition condition: " + cond)
            self.pos += 1
            return tok

        def parse(self):
            expr = self.parse_or()
            if self.peek() is not None:
                raise Exception("Malformed HOA transition condition: " + cond)
            return expr

        def parse_or(self):
            left = self.parse_and()
            while self.peek() == "|":
                self.consume("|")
                right = self.parse_and()
                left = BiOp(left, "|", right)
            return left

        def parse_and(self):
            left = self.parse_not()
            while self.peek() == "&":
                self.consume("&")
                right = self.parse_not()
                left = BiOp(left, "&", right)
            return left

        def parse_not(self):
            if self.peek() == "!":
                self.consume("!")
                return neg(self.parse_not())
            return self.parse_atom()

        def parse_atom(self):
            tok = self.peek()
            if tok == "(":
                self.consume("(")
                expr = self.parse_or()
                self.consume(")")
                return expr
            if tok is None:
                raise Exception("Malformed HOA transition condition: " + cond)
            self.consume()
            if tok == "true":
                return true()
            if tok == "false":
                return false()
            return Variable(tok)

    parser = Parser(tokenize(raw_cond))
    res = parser.parse()
    # print(str(cond) + " ---> " + str(res.left) + " , " + str(res.right))
    return res
