#!/usr/bin/env python3
import csv
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Optional
from collections import defaultdict, Counter

OUT_CSV = "results.csv"
OUT_LATEX = "results.tex"
timeout = 1200000

@dataclass
class ToolInfo:
    name: str
    ext: str
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
    "raboniel": ToolInfo(name="raboniel", ext="tslmt", latex_name="R", real=raboniel_real_re, unreal=raboniel_unreal_re, err=CheckMissing("Result")),
    "temos": ToolInfo(name="temos", ext="tslt", latex_name="T", real=strix_real_re, unreal=strix_unreal_re),
    "rpgsolve": ToolInfo(name="rpgsolve", ext="rpg", latex_name="RPG$_r$", real=rpg_real_re, unreal=rpg_unreal_re, err=err_re),
    "rpgsolve-syn": ToolInfo(name="rpgsolve-syn", ext="rpg", latex_name="RPG", real=rpg_real_re, unreal=rpg_unreal_re, directory="rpgsolve", err=err_re),
    "sweap": ToolInfo(name="sweap", ext="prog", latex_name=r"O$_{\textit{acc}}$", real=sweap_real_re, unreal=sweap_unreal_re),
    "sweap-noacc": ToolInfo(name="sweap-noacc", ext="prog", latex_name=r"O", real=sweap_real_re, directory="sweap", unreal=sweap_unreal_re),
    "rpg-stela": ToolInfo(name="rpg-stela", ext="rpg", latex_name="RSt$_r$", real=stela_real_re, unreal=stela_unreal_re, directory="rpgsolve", err=err_re),
    "tslmt2rpg": ToolInfo(name="tslmt2rpg", ext="rpg", latex_name="T2R$_r$", real=rpg_real_re, unreal=rpg_unreal_re, directory="tslmt2rpg", err=err_re),
    "tslmt2rpg-syn": ToolInfo(name="tslmt2rpg-syn", ext="rpg", latex_name="T2R", real=rpg_real_re, unreal=rpg_unreal_re, directory="tslmt2rpg", err=err_re)
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
    "infinite-race": True,
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
    "robot-commute-1d": ("robot-grid-comute-1d"),
    "robot-commute-2d": ("robot-grid-comute-2d"),
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
            return get_result("rpgsolve", tools["rpgsolve-syn"], bench, bench_info)
        # 0 means no log found
        return 0
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

writer = csv.writer(sys.stdout, dialect="excel", lineterminator="\n")
latex = """
    \begin{tabular}{lfff}
"""

results = defaultdict(dict)

def update_stats(result: int, tool: str):
    if 1 < result < timeout:
        STATS[tool]["right"] += 1
    elif result == 1:
        STATS[tool]["err"] += 1
    elif result >= timeout:
        STATS[tool]["to"] += 1
    elif result < 0:
        STATS[tool]["wrong"] += 1

for benchs in (infinite_benchs,):
    writer.writerow(["row-id", "benchmark", *tools])
    for i, b in enumerate(benchs, start=2):
        row = [i, b]
        bench_info = benchs[b]
        for tool, tool_info in tools.items():
            result = get_result(tool, tool_info, b, bench_info)
            results[b][tool] = result
            update_stats(result, tool)
            row.append(result)
        writer.writerow(row)
    print()
    print(STATS, file=sys.stderr)

latex_order = (
    "rpgsolve", "tslmt2rpg", "rpg-stela",
    "rpgsolve-syn", "tslmt2rpg-syn",
    "raboniel", "temos", 
    "sweap", "sweap-noacc")
fmt_names = " & ".join(tools[x].latex_name for x in latex_order)

latex_header = rf"""
\begin{{tabular}}{{|c|c|c||c|c|c||c|c|c|c||c|c|}}\hline
G. & Name & U & {fmt_names}\\\hline
"""


def fmt_result(x: int, real: bool=False):
    if x == 0:
        return ""
    if x == 1:
        return "ERR"
    if x < 0:
        return r"\textsf{x}"
    if x >= timeout:
        return "--"
    return f"{x/1000:.2f}{'$_r$' if real else ''}"


syn_tools = ("raboniel", "temos", "rpgsolve-syn", "tslmt2rpg-syn", "sweap", "sweap-noacc")
r11y_tools = ("rpgsolve", "rpg-stela", "tslmt2rpg", "sweap", "sweap_noacc")

def do_latex_body(benchs, title):
    yield rf"\multirow{{{len(benchs)}}}{{*}}{{\rotatebox[origin=c]{{90}}{{{title}}}}}"
    yield '\n'
    for b, is_realizable in benchs.items():

        # Sort & Format results for this benchmark b
        r = {x: fmt_result(results[b][x], x in r11y_tools) for x in latex_order}

        # Temos' unrealizability verdicts cannot be trusted
        if not is_realizable and 1 < results[b].get("temos", 0) < timeout:
            r["temos"] = "unk"

        # Highlight best (synthesis) time
        positive_results = {
            tool: results[b][tool]
            for tool in latex_order if results[b][tool] > 2}
        if positive_results:
            best = min(positive_results, key=positive_results.get)
            r[best] = f"\\textbf{{{r[best]}}}"

        # Replace with realizability time if synthesis failed
        # if not (2 < results[b]["rpgsolve-syn"] < timeout):
        #     r["rpgsolve-syn"] = fmt_result(results[b]["rpgsolve"], True)
        # if not (2 < results[b]["tslmt2rpg-syn"] < timeout):
        #     r["tslmt2rpg-syn"] = fmt_result(results[b]["tslmt2rpg"], True)
        # Yield formatted value
        fmt_r = " & ".join(r.values())
        bullet = "" if is_realizable else r"$\bullet$"
        yield rf"& {b.replace('_', '-')} & {bullet} & {fmt_r} \\"
        yield '\n'
    yield "\hline\hline\n"


# latex = sys.stdout
with open("table.tex", "w") as latex:
    latex.write(latex_header)
    latex.writelines(do_latex_body(safety_benchs_popl24, "Safety"))
    latex.writelines(do_latex_body(reach_benchs_popl24, "Reachability"))
    latex.writelines(do_latex_body(buechi_benchs_popl24, r"""Det. B\"uchi"""))
    latex.writelines(do_latex_body(buechi_benchs_cav24, r"""Det. B\"uchi, CAV'24"""))
    latex.writelines(do_latex_body(buechi_benchs_popl25, "POPL'25"))
    latex.writelines(do_latex_body(ltl_benchs, "Full LTL"))
    latex.write("\n")
    latex.write(r"\end{tabular}")
    latex.write("\n")


# Compute best/unique times
syn_best, syn_uniq, r11y_best, r11y_uniq = (Counter() for _ in range(4))

for best, uniq, which_tools in ((syn_best, syn_uniq, syn_tools), (r11y_best, r11y_uniq, r11y_tools)):
    for b in infinite_benchs:
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

print(f"{syn_best=}")
print(f"{r11y_best=}")
print(f"{syn_uniq=}")
print(f"{r11y_uniq=}")

