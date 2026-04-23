#!/usr/bin/env python3
import csv
import re
from subprocess import CalledProcessError, check_output
import sys
from dataclasses import dataclass
from pathlib import Path
from textwrap import dedent
from typing import Optional
from collections import defaultdict, Counter

OUT_DIR = "results"
OUT_CSV = "results.csv"
OUT_LATEX = "table-results.tex"
LTL_LATEX = "table-ltl.tex"
REF_LATEX = "table-refinements.tex"
SUMM_LATEX = "table-summ.tex"
MACROS_LATEX = "macros-experiments.tex"
bullet = r"$\bullet$"

TIMEOUT = 600_000  # 1_200_000
popl24 = r"\cite{10.1145/3632899}"
cav24 = r"\cite{DBLP:conf/cav/SchmuckHDN24}"
popl25 = r"\cite{DBLP:journals/pacmpl/HeimD25}"
isola24 = r"\cite{DBLP:conf/isola/MaderbacherWB24}"

@dataclass
class ToolInfo:
    name: str
    # latex_name: str
    real: re.Pattern
    unreal: re.Pattern
    directory: Optional[str] = None
    err: Optional[re.Pattern] = None


rpg_real_re = re.compile(r"Game realizable => True", re.MULTILINE)
rpg_unreal_re = re.compile(r"Game realizable => False", re.MULTILINE)
sweap_real_re = re.compile(r"^Realisable$", re.MULTILINE)
sweap_unreal_re = re.compile(r"^Unrealisable$", re.MULTILINE)
strix_real_re = re.compile(r"^REALIZABLE", re.MULTILINE)
strix_unreal_re = re.compile(r"^UNREALIZABLE", re.MULTILINE)
err_re = re.compile(r"^Result:\s*$", re.MULTILINE)
stela_real_re = re.compile(r"^Realizable: True", re.MULTILINE)
stela_unreal_re = re.compile(r"^Realizable: False", re.MULTILINE)

oom_re = re.compile(r"memory allocation of [0-9]+ bytes failed")


class CheckMissing:
    def __init__(self, s) -> None:
        self.s = s
    def search(self, string):
        return self.s not in string

tools = {
    **{
        f"sweap{conf}": ToolInfo(name=f"sweap{conf}", real=sweap_real_re, unreal=sweap_unreal_re)
        for conf in ("-strix", "-dual", "-rpg", "-rpg-dual", "-tsl", "-tsl-dual", "-issy", "-issy-dual", "-semml", "-strix-dual")
    },
    **{
        f"issy{conf}": ToolInfo(name=f"issy{conf}", real=rpg_real_re, unreal=rpg_unreal_re)
        for conf in ("3", "3-rpg", "3-tsl")
    }
}

# These dictionaries map each benchmark
# to its expected realisability (True<->realisable)
safety_benchs_popl24 = {
    name: (True, "safety") for name in (
        "box",
        "box-limited",
        "diagonal",
        "evasion",
        "follow",
        "solitary",
        "square")
}

safety_benchs_popl25 = {
    "g-real": (True, "safety"),
    "g-unreal-1": (False, "safety"),
    "g-unreal-2": (False, "safety"),
    "g-unreal-3": (False, "safety"),
}

reach_benchs_popl24 = {
    "heim-normal": (True, "reach"),
    "heim-double-x": (True, "reach"),
    "robot-cat-real-1d": (True, "reach"),
    "robot-cat-unreal-1d": (False, "reach"),
    "robot-cat-real-2d": (True, "reach"),
    "robot-cat-unreal-2d": (False, "reach"),
    "robot-grid-reach-1d": (True, "reach"),
    "robot-grid-reach-2d": (True, "reach"),
}

reach_benchs_novel = {
    "robot-tasks": (True, "reach"),
}

buechi_benchs_popl24 = {
    "heim-buechi": (True, "buechi"),
    "heim-fig7": (False, "buechi"),
    "robot-commute-1d": (True, "buechi"),
    "robot-commute-2d": (True, "buechi"),
    "robot-resource-1d": (False, "buechi"),
    "robot-resource-2d": (False, "buechi"),
    "robot-resource-2d-real": (True, "buechi")
}

buechi_benchs_cav24 = {
    **{f"chain-{i}": (True, "buechi") for i in (4, 5, 6, 7)},
    **{f"chain-simple-{i}": (True, "buechi") for i in (5, 10, 20, 30, 40, 50, 60, 70)},
    "items_processing": (True, "buechi"),
    "robot_analyze": (True, "buechi"),
    **{f"robot_collect_v{i}": (True, "buechi") for i in (1, 2, 3)},
    **{f"robot_deliver_v{i}": (True, "buechi") for i in (1, 2, 3, 4, 5)},
    "robot_repair": (False, "buechi"),
    "robot_running": (True, "buechi"),
    "scheduler": (True, "buechi"),
}

tacas26_benchs = {
    "tacas26-buchi-hard-loops-200": (False, "buechi"),
    "tacas26-buchi-hard-loops-400": (False, "buechi"),
    "tacas26-buchi-hard-loops-800": (False, "buechi"),
    "tacas26-buchi": (True, "buechi"),
    "tacas26-buchi-loops-200": (True, "buechi"),
    "tacas26-buchi-loops-400": (True, "buechi"),
    "tacas26-buchi-loops-800": (True, "buechi"),
    "tacas26-buchi-loops-chaining-200": (True, "buechi"),
    "tacas26-buchi-loops-chaining-400": (True, "buechi"),
    "tacas26-buchi-loops-chaining-800": (True, "buechi"),
    "tacas26-buchi-loops-swap-200": (True, "buechi"),
    "tacas26-buchi-loops-swap-400": (True, "buechi"),
    "tacas26-buchi-loops-swap-800": (True, "buechi"),
    "tacas26-buchi-simple": (True, "buechi"),
    "tacas26-choice-3-actions": (True, "buechi"),
    "tacas26-choice-4-actions": (True, "buechi"),
    "tacas26-choice-actions-i":  (True, "buechi"),
    "tacas26-double": (True, "reach"),
    "tacas26-equality-assumption": (True, "buechi"),
    "tacas26-equal-mod2-real": (True, "buechi"),
    "tacas26-equal-mod2-unreal": (False, "buechi"),
    "tacas26-fault-tolerance": (True, "reach"),
    "tacas26-inequality-assumption": (True, "buechi"),
    "tacas26-lemma-chaining-control": (True, "reach"),
    "tacas26-lemma-chaining": (True, "buechi"),
    "tacas26-nested-x-y-z": (True, "reach"),
    "tacas26-nested-x-y-z-u": (True, "reach"),
    "tacas26-nested-x-y-z-u-v": (True, "reach"),
    "tacas26-nondet-exit-swap-input": (True, "reach"),
    "tacas26-nondet-exit-swap": (True, "reach"),
    "tacas26-prioritized-tasks-real-100": (True, "reach"),
    "tacas26-prioritized-tasks-real-200": (True, "reach"),
    "tacas26-prioritized-tasks-unreal-100": (False, "reach"),
    "tacas26-ranking-choice-2": (True, "buechi"),
    "tacas26-ranking-choice-3": (True, "buechi"),
    "tacas26-ranking-choice-4": (True, "buechi"),
    "tacas26-reach-either-or": (True, "reach"),
    "tacas26-service-10": (True, "buechi"),
    "tacas26-service-2": (True, "buechi"),
    "tacas26-service-4": (True, "buechi"),
    "tacas26-service-8": (True, "buechi"),
    "tacas26-service-bounds-10": (True, "buechi"),
    "tacas26-service-bounds-20": (True, "buechi"),
    "tacas26-ex-2-05": (True, "buechi"),
    "tacas26-ex-4-06": (True, "buechi"),
    "tacas26-ex-4-11": (True, "buechi"),
    "tacas26-ex-4-12": (False, "buechi"),
    "tacas26-ex-4-13": (True, "buechi"),
    "tacas26-ex-4-15": (True, "buechi"),
    "tacas26-ex-4-18": (True, "buechi"),
    "tacas26-ex-4-21": (True, "buechi"),
    "tacas26-ex-5-01": (True, "buechi"),
}

ltl_benchs = {
    "arbiter": (True, "ltl"),
    "arbiter-failure": (True, "ltl"),
    "arbiter-with-failure-variant": (False, "ltl"),
    "elevator": (True, "ltl"),
    "infinite-race": (True, "ltl"),
    "infinite-race-u": (False, "ltl"),
    "infinite-race-unequal-1": (True, "ltl"),
    "infinite-race-unequal-1-variant": (False, "ltl"),
    "infinite-race-unequal-2": (True, "ltl"),
    "reversible-lane-r": (True, "ltl"),
    "reversible-lane-r-variant": (False, "ltl"),
    "reversible-lane-u": (False, "ltl"),
    "rep-reach-obst-1d": (True, "ltl"),
    "rep-reach-obst-2d": (True, "ltl"),
    "rep-reach-obst-6d": (True, "ltl"),
    "robot_collect_v4": (True, "ltl"),
    "taxi-service": (True, "ltl"),
    "taxi-service-u": (False, "ltl"),
}

reach_benchs_popl25 = {
    "F-G-contradiction-1": (False, "reach"),
    "F-G-contradiction-2": (False, "reach"),
    "f-real": (True, "reach"),
    "f-unreal": (False, "reach"),
    "ordered-visits": (True, "reach"),
    "ordered-visits-choice": (True, "reach"),
    "precise-reachability": (True, "reach"),
    "robot-to-target": (True, "reach"),
    "robot-to-target-unreal": (False, "reach"),
    "robot-to-target-charging": (True, "reach"),
    "robot-to-target-charging-unreal": (False, "reach"),
    "thermostat-F": (True, "reach"),
    "thermostat-F-unreal": (False, "reach"),
    "unordered-visits-charging": (True, "reach"),
    "unordered-visits": (True, "reach"),
}

buechi_benchs_popl25 = {
    "buffer-storage": (True, "buechi"),
    "gf-real": (True, "buechi"),
    "gf-unreal": (False, "buechi"),
    "GF-G-contradiction": (False, "buechi"),
    "helipad": (True, "buechi"),
    "helipad-contradict": (False, "buechi"),
    "package-delivery": (True, "buechi"),
    "patrolling": (True, "buechi"),
    "patrolling-alarm": (True, "buechi"),
    "storage-GF-64": (True, "buechi"),
    "tasks": (True, "buechi"),
    "tasks-unreal": (False, "buechi"),
    "thermostat-GF": (True, "buechi"),
    "thermostat-GF-unreal": (False, "buechi"),
}

reach_benchs_isola24 = {
    "sort4": (True, "reach"),
    "sort5": (True, "reach"),
}

nondet_input_benchs = {
    "nd-robot-resource-2d": (False, "buechi"),
    "nd-gf-real": (True, "buechi"),
    "nd-robot-to-target": (True, "reach"),
    "nd-infinite-race-u": (False, "ltl"),
    "nd-heim-fig7": (False, "buechi"),
    "nd-arbiter-nodet": (False, "ltl"),
    "nd-arbiter-det": (True, "ltl"),
    "nd-helipad": (True, "buechi"),
    "nd-chain-4": (True, "buechi"),
    "nd-chain-5": (True, "buechi"),
    "nd-arbiter": (True, "ltl"),
}

issy_benchs = {
    "balancer-bool-simplified-1": (True, "ltl"),
    "balancer-bool-simplified-2": (True, "ltl"),
    "balancer-bool-simplified-3": (True, "ltl"),
    "balancer": (True, "ltl"),
    "fig7-gt1": (False, "buechi"),
    "two-loc-inp-real": (True, "buechi"),
    "two-loc-inp-unreal-0": (False, "buechi"),
    "two-loc-inp-unreal-1": (False, "buechi"),
    "two-loc-real-1": (True, "buechi"),
    "two-loc-real-2": (True, "buechi"),
    "two-vars-real": (True, "buechi"),
    "two-vars-unreal": (False, "buechi"),
    "counter-10-10-formula": (True, "reach"),
    "counter-10-10-game": (True, "reach"),
    "counter-2-10-2-formula": (True, "reach"),
    "counter-2-10-2-game": (True, "reach"),
    "counter-2-10-formula": (True, "reach"),
    "counter-2-10-game": (True, "reach"),
    "counter-3-10-formula": (True, "reach"),
    "counter-3-10-game": (True, "reach"),
    "counter-3-7-formula": (True, "reach"),
    "counter-3-7-game": (True, "reach"),
    # "v1": (True, "buechi"),
    # "v2-unreal": (False, "buechi"),
    "parity-two-vars-real": (True, "ltl"),
    "parity-two-vars-unreal-0": (False, "ltl"),
    "parity-two-vars-unreal-1": (False, "ltl"),
    "parity-two-vars-unreal-2": (False, "ltl"),
    "balance-add-rem-2-2-8": (False, "safety"),
    "balance-add-rem-8-1-16": (True, "safety"),
    "balance-add-rem-8-1-7": (False, "safety"),
    "balance-add-rem-8-2-16": (False, "safety"),
    "empty-add-rem-2-1-unreal": (False, "buechi"),
    "empty-add-rem-2-1": (True, "buechi"),
    "empty-balance-add-rem-2-1-2": (True, "buechi"),
    "test-01": (False, "buechi"),
    "test-02": (True, "buechi"),
    "test-03": (True, "buechi"),
    "test-04": (True, "safety"),
    "test-05": (True, "safety"),
    "test-06": (False, "safety"),
    "test-07": (True, "buechi"),
    "test-08": (True, "buechi"),
    "test-09": (True, "safety"),
    "test-10": (False, "buechi"),
    "test-11": (True, "buechi"),
    "test-12": (True, "buechi"),
    "test-13": (True, "buechi"),
    "test-14": (True, "safety"),
    "test-extract-input": (True, "safety"),
    "test-extract-lemma": (True, "reach")
}

other_benchs = {
    "repeated-robot-resource-1d": (True, "ltl"),
    "arbiter-unreal": ( False, "ltl")
}

infinite_benchs = {
    **safety_benchs_popl24,
    **safety_benchs_popl25,
    **reach_benchs_popl24,
    **reach_benchs_popl25,
    **reach_benchs_isola24,
    **reach_benchs_novel,
    **buechi_benchs_cav24,
    **buechi_benchs_popl24,
    **buechi_benchs_popl25,
    **ltl_benchs,
    **issy_benchs,
    **tacas26_benchs
}


finite_benchs = {
    **{f"bloem-elevator-simple-{i}": True for i in (3, 5, 10, 50)},
    **{f"bloem-elevator-signal-{i}": True for i in (3, 5, 10, 50)},
    **{f"arbiter-{i}": True for i in (5, 10, 50)},
    **{f"arbiter-unreal-{i}": False for i in (5, 10, 50)},
    **{f"robot-grid-reach-1d-{i}": True for i in (5, 10, 50)},
    **{f"robot-grid-reach-2d-{i}": True for i in (5, 10, 50)},
    **{f"elevator-{i}": True for i in (5, 10, 50)},
    **{f"reversible-lane-r-{i}": True for i in (5, 10, 50)},
    **{f"reversible-lane-u-{i}": False for i in (5, 10, 50)}
}

# Alternative names for some of the benchmarks
aliases = {
    "arbiter": ("arbiter-paper", "batch-arbiter"),
    "arbiter-failure": ("arbiter-with-failure", ),
    "arbiter-unreal": ("arbiter-paper-unreal", ),
    "box-limited": ("neider-box-limited", ),
    "box": ("neider-box", ),
    "diagonal": ("neider-diagonal", ),
    "elevator": ("elevator-paper", ),
    "evasion": ("neider-evasion", ),
    "follow": ("neider-follow", ),
    "heim-fig7": ("heim-buechi-u", "heim-buchi-u", "fig7"),
    "rep-reach-obst-1d": ("robot-grid-reach-repeated-with-obstacles-1d", ),
    "rep-reach-obst-2d": ("robot-grid-reach-repeated-with-obstacles-2d", ),
    "rep-reach-obst-6d": ("robot-grid-reach-repeated-with-obstacles-6d", ),
    "reversible-lane-r": ("road", ),
    "robot_analyze": ("robot_analyze_samples", "robot_analyze_samples_v1", ),
    "robot-commute-1d": ("robot-grid-comute-1d", "robot-grid-commute-1d", ),
    "robot-commute-2d": ("robot-grid-comute-2d", "robot-grid-commute-2d", ),
    "solitary": ("neider-solitary", ),
    "square": ("neider-square5x5", "neider-square-5x5", "square5x5"),
    **{f"chain-{i}": (f"chain_{i}", ) for i in (4, 5, 6, 7)},
    **{f"chain-simple-{i}": (f"chain_simple_{i}", ) for i in (5, 10, 20, 30, 40, 50, 60, 70)},
    **{f"robot_collect_v{i}": (f"robot_collect_samples_v{i}", ) for i in (1, 2, 3, 4)},
    **{f"robot_deliver_v{i}": (f"robot_deliver_products_{i}", ) for i in (1, 2, 3, 4, 5)},
    ## Finite-state bechmarks
    **{f"arbiter-{i}": (f"arbiter-paper-{i}", ) for i in (5, 10, 50)},
    **{f"arbiter-unreal-{i}": (f"arbiter-paper-unreal-{i}", ) for i in (5, 10, 50)},
    **{f"elevator-{i}": (f"elevator-paper-{i}", ) for i in (5, 10, 50)},
}


runtime_re = re.compile(r"Runtime: ([0-9]+)ms")

base_dir = "." if len(sys.argv) == 1 else sys.argv[1]
out_dir = Path(base_dir) / OUT_DIR
try:
    out_dir.mkdir()
except FileExistsError:
    pass

STATS = defaultdict(lambda: defaultdict(int))
GET_TR_PREDS = (
    """tr '" ()!' '\n' | tr "'" '\n' | """
    "grep prev | grep pred | sort | uniq | wc -l")
def get_refinements(fname):
    def shell(cmd):
        return check_output(cmd, shell=True, encoding="utf-8")
    def handle_predicates_line(line):
        preds = (
            line.
            strip().
            replace("adding ", "").
            replace(" to predicate abstraction", "").
            split(", "))
        preds = [p for p in preds if p]
        tr = sum("_prev" in p for p in preds)
        st = len(preds) - tr
        return st, tr

    init_preds = shell(
        f"""grep -A1 "Starting abstract synthesis loop." {fname} | tail -n1""")
    init_st, _ = handle_predicates_line(init_preds)
    init_tr = shell(f"sed '/constructing LTL/q' {fname} | {GET_TR_PREDS}")
    init_tr = int(init_tr)

    try:
        all_pred_lines = shell(f"""grep "^adding" {fname}""").split("\n")
        all_pred_lines = [handle_predicates_line(x) for x in all_pred_lines if x]
    except CalledProcessError:
        all_pred_lines = []
    add_st, add_tr = 0, 0
    count_fair_ref, count_safe_ref = 0, 0
    if len(all_pred_lines):
        all_st, all_tr = zip(*all_pred_lines)
        add_st, add_tr = sum(all_st) - init_st, sum(all_tr) - init_tr

        count_fair_ref = shell(
            f"""grep "Structural Refinement" {fname} | wc -l""").strip()
        count_safe_ref = shell(
            f"""grep "safety refinement" {fname} | wc -l""").strip()

    all_tr = shell(f"cat {fname} | {GET_TR_PREDS}")
    add_tr = int(all_tr) - init_tr
    return init_st, init_tr, count_fair_ref, count_safe_ref, add_st, add_tr

all_logs = set(Path(base_dir).rglob("*.*.log"))

def get_result(tool, tool_info, bench, b_real):
    result = None
    for name in (bench, *aliases.get(bench, [])):
        log = [
            p for p in all_logs
            if p.name.replace("cav25-azzopardi-", "") == f"{name}.{tool}.log"]
        if log:
            break
    if not log:
        return 0, 0, "missing"
    try:
        with open(log[0], "r") as log_file:
            raw_result = log_file.read()
    except FileNotFoundError:
        return 0, 0, "missing"
    log_lines = raw_result.splitlines()
    find_timeout = log_lines[0].find("timeout ")
    timeout = 1_000 * int(log_lines[0][find_timeout+8:].split()[0]) if find_timeout != -1 else TIMEOUT
    try:
        runtime = int(log_lines[-1])
        return_code = int(log_lines[-2])
    except (ValueError):
        search_137 = [i for i in range(len(log_lines)) if log_lines[i] == "137"]
        if search_137:
            runtime=0
            return_code = 137
            for line in log_lines[search_137[0]+1:]:
                try:
                    runtime = int(line)
                    break
                except ValueError:
                    continue
        else:
            raise ValueError(f"Invalid or empty log file: {log[0]}")
    if runtime >= timeout:
        return runtime, timeout, "timeout"

    
    if return_code == 137:
        return runtime, timeout, "oom"

    verdict_real = tool_info.real.search(raw_result)
    verdict_unreal = tool_info.unreal.search(raw_result)
    if verdict_real and not verdict_unreal:
        return runtime, timeout, "realizable"
    elif verdict_unreal and not verdict_real:
        return runtime, timeout, "unrealizable"
    elif any((
        oom_re.search(raw_result),
        "java.lang.OutOfMemoryError" in raw_result,
        "You may be using a special nuXmv keyword" in raw_result,
        "Finite synthesis engine did not return any output." in raw_result,
        "Finite synthesis engine ran out of memory." in raw_result,
        "issy-bin: out of memory" in raw_result
    )):
        return runtime, timeout, "oom"
    elif any((
        "currently unsupported" in raw_result,
        "We do not handle ISSY files without game arenas yet." in raw_result,
        "We do not handle yet ISSY problems with no games." in raw_result,
        "We do not yet handle objectives" in raw_result
    )):
        return runtime, timeout, "unsupported"

    return runtime, timeout, "error"


results = defaultdict(dict)
refinements = defaultdict(dict)

def update_stats(verdict: str, tool: str, bench_real: bool):
    if verdict == "realizable":
        STATS[tool]["right" if bench_real else "wrong"] += 1
        if bench_real:
            STATS[tool]["right_real"] += 1
    elif verdict == "unrealizable":
        STATS[tool]["wrong" if bench_real else "right"] += 1
    elif verdict != "missing":
        STATS[tool][verdict] += 1

stdout_writer = csv.writer(sys.stdout, dialect="excel", lineterminator="\n")
stdout_writer.writerow(["benchmark", "goal", "real","tool","time(ms)","verdict"])

COUNT_REAL = Counter()
for b, (b_real, b_goal) in infinite_benchs.items():
    for tool, tool_info in tools.items():
        runtime, timeout_val, verdict = get_result(tool, tool_info, b, b_real)
        results[b][tool] = (runtime, timeout_val, verdict)
        update_stats(verdict, tool, b_real)
        if (b_real and verdict == "unrealizable") or (not b_real and verdict == "realizable"):
            verdict += "___wrong"
        row = (b, b_goal, b_real, tool, abs(runtime), verdict)
        if runtime > 0:
            stdout_writer.writerow(row)
            COUNT_REAL[tool] += 1 if b_real else 0
            sys.stdout.flush()

def get_portfolio_result(tool1, tool2, b, b_real):
    if b not in results or any(tool not in results[b] for tool in (tool1, tool2)):
        return 0, "missing"
    t1, to1, result1 = results[b][tool1]
    t2, to2, result2 = results[b][tool2]
    t1 = t1 if t1 > 0 else max(to1, to2)
    t2 = t2 if t2 > 0 else max(to1, to2)
    verdicts = set((result1, result2)) - {"missing"}
    time = min(t1, t2)
    if not verdicts:
        return 0, "missing"
    elif len(verdicts) == 1:  # Tools agree
        v = verdicts.pop()
        return 0 if v == "missing" else time, v
    elif "realizable" in verdicts and "unrealizable" in verdicts:  # Tools disagree
        return time, "unsupported"
    else:
        at_least_one_timeout = "timeout" in verdicts
        verdicts -= set(("timeout", "oom", "error"))
        if len(verdicts) == 1:
            return time, verdicts.pop()
        elif at_least_one_timeout:
            return time, "timeout"
        else:
            return time, "error" 


for b, (b_real, b_goal) in infinite_benchs.items():
    for (pf, tool1, tool2) in (
        ("sweap-pf", "sweap-semml", "sweap-dual"),
        ("sweap-rpg-pf", "sweap-rpg", "sweap-rpg-dual"),
        ("sweap-tsl-pf", "sweap-tsl", "sweap-tsl-dual"),
        ("sweap-issy-pf", "sweap-issy", "sweap-issy-dual"),
    ):
        better_time, verdict = get_portfolio_result(tool1, tool2, b, b_real)
        update_stats(verdict, pf, b_real)
        if (b_real and verdict == "unrealizable") or (not b_real and verdict == "realizable"):
            verdict += "___wrong"
        row = (b, b_goal, b_real, pf, abs(better_time), verdict)
        if better_time > 0:
            stdout_writer.writerow(row)
            sys.stdout.flush()


VERDICTS = (
    "right", "right_real", "wrong", "timeout", "oom", "unsupported", "error")

stderr_writer = csv.writer(sys.stderr, dialect="excel", lineterminator="\n")
stderr_writer.writerow(["tool", *VERDICTS, "total", "total_real"])
for k in (sorted(STATS.keys())):
    v = STATS[k]
    values = [v.get(x, 0) for x in VERDICTS]
    total = sum(values) - v.get("right_real", 0)
    stderr_writer.writerow([k, *values, total, COUNT_REAL.get(k, 0)])
    sys.stderr.flush()



sys.exit(0)

# Results (latex) #############################################################
latex_order = (
    # "rpgsolve", "tslmt2rpg", "rpg-stela",
    # "rpgsolve-syn", "tslmt2rpg-syn",
    "sweap", 
    # "sweap-noacc"
    )
fmt_names = " & ".join(tools[x].latex_name for x in latex_order)


latex_header = rf"""
\begin{{tabular}}{{|c|lr|c||c|c|c||c|c|c|c||c|c|}}\hline
\multirow{{2}}{{*}}{{G.}}
& \multirow{{2}}{{*}}{{Name, source}} &
& \multirow{{2}}{{*}}{{U}}
& \multicolumn{{3}}{{c||}}{{Realisability (s)}}
& \multicolumn{{6}}{{c|}}{{Synthesis (s)}}\\\cline{{5-13}}
& & & & {fmt_names}\\\hline\hline
"""

def fmt_result(x: int, real: bool=False):
    if x == 0:
        return ""
    if x == 1:
        return r"\ERROR"
    if x < 0:
        return r"\textsf{x}"
    if x >= timeout:
        return r"\TIMEOUT"
    return f"{x/1000:.2f}{'$_r$' if real else ''}"


syn_tools = ("rpgsolve-syn", "tslmt2rpg-syn", "sweap", "sweap-noacc")
r11y_tools = ("rpgsolve", "rpg-stela", "tslmt2rpg", "sweap", "sweap-noacc")

def do_latex_body(benchs, source):
    for b, is_realizable in benchs.items():

        # Sort & Format results for this benchmark b
        r = {x: fmt_result(results[b].get(x, 0), False) for x in latex_order}

        # Highlight best (synthesis) time
        positive_results = {
            tool: results[b][tool]
            for tool in latex_order
            if tool in syn_tools and results[b].get(tool, 0) > 2}
        if positive_results:
            best = min(positive_results, key=positive_results.get)
            r[best] = f"\\textbf{{{r[best]}}}" if results[b][best] < timeout else r[best]
        fmt_r = " & ".join(r.values())
        yield rf"&  \textsf{{{b.replace('_', '-')}}} & {source} & {'' if is_realizable else bullet} & {fmt_r} \\"
        yield '\n'


with open(out_dir / OUT_LATEX, "w") as latex:
    latex.write(latex_header)
    how_many_safety = len(safety_benchs_popl24) + len(safety_benchs_popl25)
    latex.write(rf"\multirow{{{how_many_safety}}}{{*}}{{\rotatebox[origin=c]{{90}}{{Safety}}}}" "\n") 
    latex.writelines(do_latex_body(safety_benchs_popl24, popl24))
    latex.writelines(do_latex_body(safety_benchs_popl25, popl25))
    latex.write("\\hline\\hline\n")
    how_many_reach = len(reach_benchs_popl24) + len(reach_benchs_popl25) + len(reach_benchs_isola24) + len(reach_benchs_novel)
    latex.write(rf"\multirow{{{how_many_reach}}}{{*}}{{\rotatebox[origin=c]{{90}}{{Reachability}}}}" "\n") 
    latex.writelines(do_latex_body(reach_benchs_popl24, popl24))
    latex.writelines(do_latex_body(reach_benchs_isola24, isola24))
    latex.writelines(do_latex_body(reach_benchs_popl25, popl25))
    latex.writelines(do_latex_body(reach_benchs_novel, ""))
    latex.write("\\hline\\hline\n")
    how_many_buechi = len(buechi_benchs_cav24) + len(buechi_benchs_popl24) + len(buechi_benchs_popl25)
    latex.write(rf"\multirow{{{how_many_buechi}}}{{*}}{{\rotatebox[origin=c]{{90}}{{Deterministic B\"uchi}}}}" "\n") 
    latex.writelines(do_latex_body(buechi_benchs_popl24, popl24))
    latex.writelines(do_latex_body(buechi_benchs_cav24, cav24))
    latex.writelines(do_latex_body(buechi_benchs_popl25, popl25))
    latex.write("\\hline\n")
    latex.write(r"\end{tabular}")
    latex.write("\n")

with open(out_dir / LTL_LATEX, "w") as latex:
    latex.write(dedent(rf"""
        \begin{{tabular}}{{|c|c||c|c|}}
        \hline
        \multirow{{2}}{{*}}{{Name}} & \multirow{{2}}{{*}}{{U}} & \multicolumn{{2}}{{c|}}{{Time (s)}}\\\cline{{3-4}}
        & & S$_{{\textit{{acc}}}}$ & S\\\hline\hline
        """[1:]))
    for b in ltl_benchs:
        latex.write(dedent(rf"""
            \textsf{{{b.replace("_", "-")}}} & {{{"" if ltl_benchs[b] else bullet}}}"""[1:]))
        best = None 
        # best = min(("sweap", "sweap-noacc"), key=results[b].get)
        # if not 1 < results[b].get(best, 0) < timeout:
        #     best = None
        for tool in ("sweap",):
            latex.write(" & ")
            latex.write(fr"\textbf{{{fmt_result(results[b][tool])}}}" if best == tool else fmt_result(results[b][tool]))
        latex.write(r"\\\hline" "\n")

    latex.write("\n" r"\end{tabular}")



# Refinements #################################################################
with open(out_dir / REF_LATEX, "w") as latex:
    begin_tabular = dedent(r"""
        \begin{tabular}[t]{|l||c||c|c|c|c|c|c||}
        \hline
        && \multicolumn{2}{c|}{init}
        & \multicolumn{2}{c|}{ref}
        & \multicolumn{2}{c||}{add}\\\hline
        \multicolumn{1}{|c||}{Name} & acc & s & t &sf. &sl. & sp & tp\\\hline\hline""")
    all_keys = [k for k in sorted(refinements.keys(), key=lambda x: x.lower())]
    keys_1, keys_2 = all_keys[:len(all_keys)//2], all_keys[len(all_keys)//2:]
    for keys in (keys_1, keys_2):
        latex.write(begin_tabular[1:])
        for k in keys:
            latex.write(rf"\multirow{{2}}{{*}}[0em]{{{k.replace('_', '-')}}}")
            latex.write("\n")
            for tool in ("sweap", "sweap-noacc"):
                init_st, init_tr, count_fair_ref, count_safe_ref, add_st, add_tr = refinements[k].get(tool, ["--"] * 6)
                latex.write(dedent(rf"""
                    & {bullet if tool == 'sweap' else ''}
                    & {init_st} & {init_tr} & {count_safe_ref} & {count_fair_ref} & {add_st} & {add_tr}"""))
                latex.write(r"\\\cline{2-8}" if tool == "sweap" else r"\\\hline")
        latex.write("\n")
        latex.write(r"\end{tabular}")

# Aggregates ##################################################################
syn_best, syn_uniq, r11y_best, r11y_uniq = (Counter() for _ in range(4))

for best, uniq, which_tools in ((syn_best, syn_uniq, syn_tools), (r11y_best, r11y_uniq, r11y_tools)):
    for b in infinite_benchs:
        # Exclude LTL benchmarks
        if b in ltl_benchs:
            continue
        good_times = {
            tool: t
            for tool, t in results[b].items()
            if tool in which_tools and 2 < t < timeout}
        if (good_times):
            best_tool = min(good_times, key=good_times.get)
            best[best_tool] += 1
        if len(good_times) == 1:
            uniq_tool, *_ = good_times.keys()
            uniq[uniq_tool] += 1
