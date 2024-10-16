#!/usr/bin/env python3
import csv
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from subprocess import CalledProcessError, check_output
from typing import Optional

@dataclass
class ToolInfo:
    name: str
    ext: str
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
    "raboniel": ToolInfo(name="raboniel", ext="tslmt", real=raboniel_real_re, unreal=raboniel_unreal_re, err=CheckMissing("Result")),
    "temos": ToolInfo(name="temos", ext="tslt", real=strix_real_re, unreal=strix_unreal_re),
    "rpgsolve": ToolInfo(name="rpgsolve", ext="rpg", real=rpg_real_re, unreal=rpg_unreal_re, err=err_re),
    "rpgsolve-syn": ToolInfo(name="rpgsolve-syn", ext="rpg", real=rpg_real_re, unreal=rpg_unreal_re, directory="rpgsolve", err=err_re),
    "sweap": ToolInfo(name="sweap", ext="prog", real=sweap_real_re, unreal=sweap_unreal_re),
    "sweap-noacc": ToolInfo(name="sweap-noacc", ext="prog", real=sweap_real_re, directory="sweap", unreal=sweap_unreal_re),
    "rpg-stela": ToolInfo(name="rpg-stela", ext="rpg", real=stela_real_re, unreal=stela_unreal_re, directory="rpgsolve", err=err_re)
}

# map bench name to its realisability (True<->realisable)
infinite_benchs = {
    "box-limited": True,
    "box": True,
    "diagonal": True,
    "evasion": True,
    "follow": True,
    "solitary": True,
    "robot-cat-real-1d": True,
    "robot-cat-unreal-1d": False,
    "robot-cat-real-2d": True,
    "robot-cat-unreal-2d": False,
    "robot-grid-reach-1d": True,
    "robot-grid-reach-2d": True,
    "repeated-robot-resource-1d": True,
    "heim-double-x": True,
    "heim-buechi": True,
    "arbiter": True,
    "arbiter-unreal": False,
    "reversible-lane-r": True,
    "xyloop": True,
    "arbiter-with-failure": True,
    "neider-square-5x5": True,
    "robot-resource-1d": False,
    "robot-resource-2d": False,
    "heim-normal": True,
    "elevator": True,
    "reversible-lane-u": False,
    "heim-buechi-u": False,
    "infinite-race": True,
    "robot-grid-reach-repeated-with-obstacles-1d": True,
    "robot-grid-reach-repeated-with-obstacles-2d": True,
    "taxi-service": True,
    "robot-grid-comute-1d": True,
    "robot-grid-comute-2d": True,
    **{f"chain-{i}": True for i in (4, 5, 6, 7)},
    **{f"chain-simple-{i}": True for i in (5, 10, 20, 30, 40, 50, 60, 70)},
    "items_processing": True,
    "robot_analyze_samples": True,
    **{f"robot_collect_samples_v{i}": True for i in (1, 2, 3)},
    **{f"robot_deliver_products_{i}": True for i in (1, 2, 3, 4, 5)},
    "robot_running": True,
    "robot_repair": True,
    "scheduler": True,
    "robot_collect_samples_v4": True,
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

aliases = {
    "box-limited": ("neider-box-limited", ),
    "box": ("neider-box", ),
    "diagonal": ("neider-diagonal", ),
    "evasion": ("neider-evasion", ),
    "follow": ("neider-follow", ),
    "solitary": ("neider-solitary", ),
    "arbiter": ("arbiter-paper", ),
    "arbiter-unreal": ("arbiter-paper-unreal", ),
    "square": ("neider-square5x5", "square5x5"),
    "robot_analyze_samples": ("robot_analyze_samples_v1", ),
    "elevator": ("elevator-paper", ),
    "heim-buechi-u": ("heim-buchi-u", ),
    **{f"chain-{i}": (f"chain_{i}", ) for i in (4, 5, 6, 7)},
    **{f"chain-simple-{i}": (f"chain_simple_{i}", ) for i in (5, 10, 20, 30, 40, 50, 60, 70)},
    ## Finite-state bechmarks
    **{f"arbiter-{i}": (f"arbiter-paper-{i}", ) for i in (5, 10, 50)},
    **{f"arbiter-unreal-{i}": (f"arbiter-paper-unreal-{i}", ) for i in (5, 10, 50)},
    **{f"elevator-{i}": (f"elevator-paper-{i}", ) for i in (5, 10, 50)}

}


runtime_re = re.compile(r"Runtime: ([0-9]+)ms")
timeout = 1200000

base_dir = "." if len(sys.argv) == 1 else sys.argv[1]

out_files = {t: list(Path(base_dir).glob(f"out-{t}-[0-9]*")) for t in tools}

def get_result(tool, tool_info, bench, bench_info, files):
    result = None
    try:
        # bench = (
        #     bench_info.aliases.get(tool, bench)
        #     if bench_info.aliases
        #     else bench)
        for name in (bench, *aliases.get(bench, [])):
            log = list(Path(base_dir).rglob(f"{name}.{tool}.log"))
            if log:
                break
        if not log:
            return 1
        with open(log[0], "r") as log_file:
            raw_result = log_file.read()
        runtime = int(raw_result.splitlines()[-1])
        if runtime <= timeout:
            right_match, wrong_match = (
                (tool_info.real, tool_info.unreal)
                if bench_info.real
                else (tool_info.unreal, tool_info.real)
            )
            if right_match.search(raw_result):
                result = runtime
            elif wrong_match.search(raw_result):
                result = -runtime
            else:
                result = 2
        else:
            result = runtime
        # else:
        #     raise ValueError(f"{bench=}, {tool=} [no runtime]")
    except CalledProcessError:
        result = 1
    if result is None:
        raise ValueError(f"{bench=}, {tool=}")
    return result

writer = csv.writer(sys.stdout, dialect="excel", lineterminator="\n")
for benchs in (infinite_benchs,):
    writer.writerow(["row-id", "benchmark", *tools])
    for i, b in enumerate(benchs, start=2):
        row = [i, b]
        bench_info = benchs[b]
        for tool, tool_info in tools.items():
            result = None
            if  False: #not out_files.get(tool, []):
                result = 1
            else:
                result = get_result(tool, tool_info, b, bench_info, out_files[tool])
            row.append(result)
        writer.writerow(row)
    print()
