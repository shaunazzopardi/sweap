#!/usr/bin/env python3
import csv
import re
from subprocess import CalledProcessError, check_output
import sys
from dataclasses import dataclass
from pathlib import Path
from textwrap import dedent
from typing import Optional, Sequence
from collections import defaultdict, Counter
from itertools import product

OUT_CSV = "results.csv"
OUT_LATEX = "table-results.tex"
LTL_LATEX = "table-ltl.tex"
REF_LATEX = "table-refinements.tex"
SUMM_LATEX = "table-summ.tex"
bullet = r"$\bullet$"

timeout = 1200000

@dataclass
class ToolInfo:
    name: str
    latex_name: str
    real: re.Pattern
    unreal: re.Pattern
    directory: Optional[str] = None
    err: Optional[re.Pattern] = None


raboniel_real_re = re.compile(r"^Result: realizable", re.MULTILINE)
raboniel_unreal_re = re.compile(r"^Result: [Uu]nrealizable", re.MULTILINE)
rpg_real_re = re.compile(r"^[Rr]ealizable", re.MULTILINE)
rpg_unreal_re = re.compile(r"^[Uu]nrealizable", re.MULTILINE)
sweap_real_re = re.compile(r"^Realizable\.", re.MULTILINE)
sweap_unreal_re = re.compile(r"^Unrealizable\.", re.MULTILINE)
strix_real_re = re.compile(r"^REALIZABLE", re.MULTILINE)
strix_unreal_re = re.compile(r"^UNREALIZABLE", re.MULTILINE)
err_re = re.compile(r"^Result:\s*$", re.MULTILINE)
stela_real_re = re.compile(r"^Realizable: True", re.MULTILINE)
stela_unreal_re = re.compile(r"^Realizable: False", re.MULTILINE)

class CheckMissing:
    def __init__(self, s) -> None:
        self.s = s
    def search(self, string):
        return self.s not in string

tools = {
    "raboniel": ToolInfo(name="raboniel", latex_name="Rab", real=raboniel_real_re, unreal=raboniel_unreal_re, err=CheckMissing("Result")),
    "temos": ToolInfo(name="temos", latex_name="Tem", real=strix_real_re, unreal=strix_unreal_re),
    "rpgsolve": ToolInfo(name="rpgsolve", latex_name="RPG", real=rpg_real_re, unreal=rpg_unreal_re, err=err_re),
    "rpgsolve-syn": ToolInfo(name="rpgsolve-syn", latex_name="RPG", real=rpg_real_re, unreal=rpg_unreal_re, directory="rpgsolve", err=err_re),
    "sweap": ToolInfo(name="sweap", latex_name=r"S$_{\textit{acc}}$", real=sweap_real_re, unreal=sweap_unreal_re),
    "sweap-noacc": ToolInfo(name="sweap-noacc", latex_name=r"S", real=sweap_real_re, directory="sweap", unreal=sweap_unreal_re),
    "rpg-stela": ToolInfo(name="rpg-stela", latex_name="RSt", real=stela_real_re, unreal=stela_unreal_re, directory="rpgsolve", err=err_re),
    "tslmt2rpg": ToolInfo(name="tslmt2rpg", latex_name="T2R", real=rpg_real_re, unreal=rpg_unreal_re, directory="tslmt2rpg", err=err_re),
    "tslmt2rpg-syn": ToolInfo(name="tslmt2rpg-syn", latex_name="T2R", real=rpg_real_re, unreal=rpg_unreal_re, directory="tslmt2rpg", err=err_re)
}
# These dictionaries map each benchmark
# to its expected realisability (True<->realisable)
safety_benchs_popl24 = {
    "box": True,
    "box-limited": True,
    "diagonal": True,
    "evasion": True,
    "follow": True,
    "solitary": True,
    "square": True,
}

reach_benchs_popl24 = {
    "robot-cat-real-1d": True,
    "robot-cat-unreal-1d": False,
    "robot-cat-real-2d": True,
    "robot-cat-unreal-2d": False,
    "robot-grid-reach-1d": True,
    "robot-grid-reach-2d": True,
    "heim-double-x": True,
    "robot-tasks": True,
}

buechi_benchs_popl24 = {
    "robot-commute-1d": True,
    "robot-commute-2d": True,
    "robot-resource-1d": False,
    "robot-resource-2d": False,
    "heim-buechi": True,
    "heim-fig7": False,
}

buechi_benchs_cav24 = {
    **{f"chain-{i}": True for i in (4, 5, 6, 7)},
    **{f"chain-simple-{i}": True for i in (5, 10, 20, 30, 40, 50, 60, 70)},
    "items_processing": True,
    "robot_analyze": True,
    **{f"robot_collect_v{i}": True for i in (1, 2, 3)},
    **{f"robot_deliver_v{i}": True for i in (1, 2, 3, 4, 5)},
    "robot_repair": True,
    "robot_running": True,
    "scheduler": True,
}

ltl_benchs = {
    "arbiter": True,
    "arbiter-failure": True,
    "arbiter-unreal": False,
    "elevator": True,
    "reversible-lane-r": True,
    "reversible-lane-u": False,
    "rep-reach-obst-1d": True,
    "rep-reach-obst-2d": True,
    "robot_collect_v4": True,
    "taxi-service": True,
}

buechi_benchs_popl25 = {
    "buffer-storage": True,
    "ordered-visits": True,
    "sort4": True,
    "sort5": True,
    "tasks": True,
    "precise-reachability": True,
    "gf-real": True,
    "f-real": True,
}

infinite_benchs = {
    **safety_benchs_popl24,
    **reach_benchs_popl24,
    **buechi_benchs_cav24,
    **buechi_benchs_popl24,
    **buechi_benchs_popl25,
    **ltl_benchs
}

other_benchs = {
    "repeated-robot-resource-1d": True,
    "heim-normal": True,
    "infinite-race": True,
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
    "heim-fig7": ("heim-buechi-u", "heim-buchi-u" ),
    "rep-reach-obst-1d": ("robot-grid-reach-repeated-with-obstacles-1d", ),
    "rep-reach-obst-2d": ("robot-grid-reach-repeated-with-obstacles-2d", ),
    "robot_analyze": ("robot_analyze_samples", "robot_analyze_samples_v1", ),
    "robot-commute-1d": ("robot-grid-comute-1d", ),
    "robot-commute-2d": ("robot-grid-comute-2d", ),
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

STATS = {t: defaultdict(int) for t in tools}

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
        tr = sum(1 for p in preds if "_prev" in p)
        st = len(preds) - tr
        return st, tr

    init_preds = shell(
        f"""grep -A1 "Starting abstract synthesis loop." {fname} | tail -n1""")
    init_st, init_tr = handle_predicates_line(init_preds)

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
    return init_st, init_tr, count_fair_ref, count_safe_ref, add_st, add_tr


def get_result(tool, tool_info, bench, bench_info):
    result = None
    for name in (bench, *aliases.get(bench, [])):
        log = list(Path(base_dir).rglob(f"{name}.{tool}.log"))
        if log:
            break
    if not log:
        if tool == "tslmt2rpg":
            # Some benchmarks are not available in tslmt format.
            # So we use the time obtained by rpgsolve (or rpgsolve-syn below)
            # and assume the "translation" time from tslmt to be zero
            return get_result("rpgsolve", tools["rpgsolve"], bench, bench_info)
        if tool == "tslmt2rpg-syn":
            return get_result("rpgsolve-syn", tools["rpgsolve-syn"], bench, bench_info)
        # 0 means no log found
        return 0
    if tool in ("sweap", "sweap-noacc"):
        refinements[b][tool] = get_refinements(log[0])

    with open(log[0], "r") as log_file:
        raw_result = log_file.read()
    runtime = int(raw_result.splitlines()[-1])
    # Scan file for realizability/unrealizability verdict
    # and compare it to the expected one
    if runtime < timeout:
        right_match, wrong_match = (
            (tool_info.real, tool_info.unreal)
            if bench_info.real
            else (tool_info.unreal, tool_info.real))
        # Time is positive/negative if verdict was correct/incorrect
        if right_match.search(raw_result):
            if tool == "temos" and not bench_info.real:
                # Temos' unrealizability verdicts cannot be trusted
                return 1
            result = max(runtime, 2)
        elif wrong_match.search(raw_result):
            result = -runtime
        else:
            # No outcome found = we assume an error and ignore runtime
            result = 1
    else:
        result = runtime
    if result is None:
        # Should never happen
        raise ValueError(f"{bench=}, {tool=}")
    return result


results = defaultdict(dict)
refinements = defaultdict(dict)

def update_stats(result: int, tool: str, bench: str):
    if 1 < result < timeout:
        if tool == "temos" and not infinite_benchs[b]:
            # Temos' unrealizability verdicts cannot be trusted
            STATS[tool]["err"] += 1
        else:
            STATS[tool]["right"] += 1
    elif result == 1:
        STATS[tool]["err"] += 1
    elif result >= timeout:
        STATS[tool]["to"] += 1
    elif result < 0:
        STATS[tool]["wrong"] += 1

with open(OUT_CSV, 'w', newline='') as csv_file:
    writer = csv.writer(csv_file, dialect="excel", lineterminator="\n")
    writer.writerow(["row-id", "benchmark", *tools])
    for i, b in enumerate(infinite_benchs, start=2):
        print(i-1, b, "...", file=sys.stderr)
        row = [i, b]
        bench_info = infinite_benchs[b]
        for tool, tool_info in tools.items():
            result = get_result(tool, tool_info, b, bench_info)
            results[b][tool] = result
            update_stats(result, tool, b)
            row.append(result)
        writer.writerow(row)

print(STATS, file=sys.stderr)

# Results (latex) #############################################################
latex_order = (
    "rpgsolve", "tslmt2rpg", "rpg-stela",
    "rpgsolve-syn", "tslmt2rpg-syn",
    "raboniel", "temos",
    "sweap", "sweap-noacc")
fmt_names = " & ".join(tools[x].latex_name for x in latex_order)


latex_header = rf"""
\begin{{tabular}}{{|c|c|c||c|c|c||c|c|c|c||c|c|}}\hline
\multirow{{2}}{{*}}{{G.}}
& \multirow{{2}}{{*}}{{Name}}
& \multirow{{2}}{{*}}{{U}}
& \multicolumn{{3}}{{c||}}{{Realisability}}
& \multicolumn{{6}}{{c|}}{{Synthesis}}\\\cline{{4-12}}
& & & {fmt_names}\\\hline\hline
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


syn_tools = ("raboniel", "temos", "rpgsolve-syn", "tslmt2rpg-syn", "sweap", "sweap-noacc")
r11y_tools = ("rpgsolve", "rpg-stela", "tslmt2rpg", "sweap", "sweap_noacc")

def do_latex_body(benchs, title, double_hline_at_end=True):
    yield rf"\multirow{{{len(benchs)}}}{{*}}{{\rotatebox[origin=c]{{90}}{{{title}}}}}"
    yield '\n'
    for b, is_realizable in benchs.items():

        # Sort & Format results for this benchmark b
        r = {x: fmt_result(results[b][x], False) for x in latex_order}

        # Temos' unrealizability verdicts cannot be trusted
        if not is_realizable and 1 < results[b].get("temos", 0) < timeout:
            r["temos"] = r"\ERR"

        # Highlight best (synthesis) time
        positive_results = {
            tool: results[b][tool]
            for tool in latex_order
            if tool in syn_tools and results[b][tool] > 2}
        if positive_results:
            best = min(positive_results, key=positive_results.get)
            r[best] = f"\\textbf{{{r[best]}}}"
        fmt_r = " & ".join(r.values())
        yield rf"& {b.replace('_', '-')} & {'' if is_realizable else bullet} & {fmt_r} \\"
        yield '\n'
    yield "\hline\hline\n" if double_hline_at_end else "\hline\n"


with open(OUT_LATEX, "w") as latex:
    latex.write(latex_header)
    for benchs, title, double_hline in (
        (safety_benchs_popl24,  "Safety",                       True),
        (reach_benchs_popl24,   "Reachability",                 True),
        (buechi_benchs_popl24,  r"""Det. B\"uchi""",            True),
        (buechi_benchs_cav24,   r"""Det. B\"uchi, CAV'24""",    True),
        (buechi_benchs_popl25,  "POPL'25",                      True),
        (ltl_benchs,            "Full LTL",                     False)
    ):
        latex.writelines(do_latex_body(benchs, title, double_hline))
    latex.write("\n")
    latex.write(r"\end{tabular}")
    latex.write("\n")

with open(LTL_LATEX, "w") as latex:
    latex.write(dedent(rf"""
        \begin{{tabular}}{{|c|c|c||c|c|c|c|c|c||c|}}
        \hline
        \multirow{{2}}{{*}}{{Name}} 
        & \multirow{{2}}{{*}}{{U}}
        & \multirow{{2}}{{*}}{{acc}} 
        & \multicolumn{{2}}{{c|}}{{init}}
        & \multicolumn{{2}}{{c|}}{{ref}}
        & \multicolumn{{2}}{{c||}}{{add}}
        & \multirow{{2}}{{*}}{{time}}\\\cline{{4-9}}
        & & & s & t &sf. &sl. & sp & tp & \\\hline
        """[1:]))
    for b in ltl_benchs:
        latex.write(dedent(rf"""
            \hline
            \multirow{{2}}{{*}}{{{b.replace("_", "-")}}} & \multirow{{2}}{{*}}{{{"" if ltl_benchs[b] else bullet}}} &
            """[1:]))
        best = min(("sweap", "sweap-noacc"), key=results[b].get)
        
        for tool in ("sweap", "sweap-noacc"):
            init_st, init_tr, count_fair_ref, count_safe_ref, add_st, add_tr = refinements[b][tool]
            latex.write(dedent(rf"""
                {bullet if tool == 'sweap' else '&&'}
                & {init_st} & {init_tr} & {count_fair_ref} & {count_safe_ref} & {add_st} & {add_tr} & """[1:]))
            latex.write(fr"\textbf{{{fmt_result(results[b][tool])}}}" if best == tool else fmt_result(results[b][tool]))
            latex.write(r"\\\cline{3-10}" if tool == "sweap" else r"\\\hline")
            latex.write("\n")

    latex.write("\n")
    latex.write(r"\end{tabular}")
    latex.write("\n")



# Refinements #################################################################
with open(REF_LATEX, "w") as latex:
    begin_tabular = dedent(r"""
        \begin{tabular}[t]{|l||c||c|c|c|c|c|c||}
        \hline
        && \multicolumn{2}{c|}{init}
        & \multicolumn{2}{c|}{ref}
        & \multicolumn{2}{c||}{add}\\\hline
        \multicolumn{1}{|c||}{Name} & acc & s & t &sf. &sl. & sp & tp\\\hline\hline""")
    all_keys = sorted(refinements.keys())
    keys_1, keys_2 = all_keys[:len(all_keys)//2], all_keys[len(all_keys)//2:]
    for keys in (keys_1, keys_2):
        latex.write(begin_tabular)
        for k in keys:
            latex.write(rf"\multirow{{2}}{{*}}[0em]{{{k.replace('_', '-')}}}")
            latex.write("\n")
            for tool in ("sweap", "sweap-noacc"):
                init_st, init_tr, count_fair_ref, count_safe_ref, add_st, add_tr = refinements[k][tool]
                latex.write(dedent(rf"""
                    & {bullet if tool == 'sweap' else ''}
                    & {init_st} & {init_tr} & {count_fair_ref} & {count_safe_ref} & {add_st} & {add_tr}"""))
                latex.write(r"\\\cline{2-8}" if tool == "sweap" else r"\\\hline")
        latex.write("\n")
        latex.write(r"\end{tabular}")

# Agregates ###################################################################
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

def fmt_summ_data(summ_dict: dict, tools: Sequence[str], real: bool=False):
    max_tool = max(summ_dict, key=summ_dict.get)
    if real:
        tools = [t.replace("-syn", "") for t in tools]
    fmt_summ_dict = " & ".join(
        rf"\textbf{{{summ_dict.get(k, 0)}}}"
        if k == max_tool else str(summ_dict.get(k, 0))
        for k in tools)
    return fmt_summ_dict

with open(SUMM_LATEX, "w") as latex:
    summ_tools = ("raboniel", "rpgsolve-syn", "temos", "tslmt2rpg-syn", "sweap", "sweap-noacc")
    header = " & ".join(tools[x].latex_name for x in summ_tools)

    all_solved = {
        t: sum(
            int(1 < results[b][t] < timeout)
            for b in results if b not in ltl_benchs)
            for t in tools}

    syn_solved = {t: d for t, d in all_solved.items() if t in summ_tools}

    fmt_syn_solved = fmt_summ_data(syn_solved, summ_tools)
    fmt_syn_best = fmt_summ_data(syn_best, summ_tools)
    fmt_syn_uniq = fmt_summ_data(syn_uniq, summ_tools)

    fmt_r11y_solved = fmt_summ_data(all_solved, summ_tools, real=True)
    fmt_r11y_best = fmt_summ_data(r11y_best, summ_tools, real=True)
    fmt_r11y_uniq = fmt_summ_data(r11y_uniq, summ_tools, real=True)

    not_our_tools=[t for t in summ_tools if "sweap" not in t]

    latex.write(dedent(rf"""
    \begin{{tabular}}{{|p{{5em}}||{"|".join("c" for _ in not_our_tools)}||c|c|}}\hline
    Synthesis & {header} \\\hline
        solved & {fmt_syn_solved}\\
        best & {fmt_syn_best}\\
        unique & {fmt_syn_uniq}\\\hline
    \end{{tabular}}\\
    \begin{{tabular}}{{|p{{6.2em}}||{"|".join("c" for _ in not_our_tools)}||c|c|}}\hline
    Realisability & {header} \\\hline
        solved & {fmt_r11y_solved}\\
        best & {fmt_r11y_best}\\
        unique & {fmt_r11y_uniq}\\\hline
    \end{{tabular}}
    """))
