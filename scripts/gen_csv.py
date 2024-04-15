#!/usr/bin/env python3
import csv
import glob
import re
import sys
from dataclasses import dataclass
from subprocess import CalledProcessError, check_output
from typing import Optional

@dataclass
class ToolInfo:
    ext: str
    real: re.Pattern
    unreal: re.Pattern
    err: Optional[re.Pattern] = None

@dataclass
class BenchInfo:
    real: bool
    aliases: Optional[dict] = False

real_re = re.compile(r"^Result: [Rr]ealizable", re.MULTILINE)
unreal_re = re.compile(r"^Result: [Uu]nrealizable", re.MULTILINE)
sweap_real_re = re.compile(r"^Realizable\.", re.MULTILINE)
sweap_unreal_re = re.compile(r"^Unrealizable\.", re.MULTILINE)
strix_real_re = re.compile(r"^REALIZABLE", re.MULTILINE)
strix_unreal_re = re.compile(r"^UNREALIZABLE", re.MULTILINE)
err_re = re.compile(r"^Result:\s*$", re.MULTILINE)

class CheckMissing:
    def __init__(self, s) -> None:
        self.s = s
    def search(self, string):
        return self.s not in string

tools = {
    "raboniel": ToolInfo(ext="tslmt", real=real_re, unreal=unreal_re, err=CheckMissing("Result")),
    "temos": ToolInfo(ext="tslt", real=strix_real_re, unreal=strix_unreal_re),
    "rpgsolve": ToolInfo(ext="rpg", real=real_re, unreal=unreal_re, err=err_re),
    "rpgsolve-syn": ToolInfo(ext="rpg", real=real_re, unreal=unreal_re, err=err_re),
    "sweap": ToolInfo(ext="prog", real=sweap_real_re, unreal=sweap_unreal_re),
    "sweap-noacc": ToolInfo(ext="prog", real=sweap_real_re, unreal=sweap_unreal_re)
}

infinite_benchs = {
    "box-limited": BenchInfo(True),
    "box": BenchInfo(True),
    "diagonal": BenchInfo(True),
    "evasion": BenchInfo(True),
    "follow": BenchInfo(True),
    "solitary": BenchInfo(True),
    "robot-cat-real-1d": BenchInfo(True),
    "robot-cat-unreal-1d": BenchInfo(False),
    "robot-cat-real-2d": BenchInfo(True),
    "robot-cat-unreal-2d": BenchInfo(False),
    "robot-grid-reach-1d": BenchInfo(True),
    "robot-grid-reach-2d": BenchInfo(True),
    "repeated-robot-resource-1d": BenchInfo(True),
    "running-example-double-x": BenchInfo(True),
    "running-example-buechi": BenchInfo(True),
    "arbiter": BenchInfo(
        True, 
        {"sweap": "arbiter-paper", "sweap-noacc": "arbiter-paper"}),
    "arbiter-unreal": BenchInfo(
        False,
        {"sweap": "arbiter-paper-unreal",
         "sweap-noacc": "arbiter-paper-unreal"}),
    "reversible-lane-r": BenchInfo(True),
    "xyloop": BenchInfo(False),
    "arbiter-with-failure": BenchInfo(True),
    "neider-square-5x5": BenchInfo(
        True,
        {"raboniel": "neider-square5x5",
         "sweap": "square5x5",
         "sweap-noacc": "square5x5",
         "temos": "neider-square5x5",}),
    "robot-resource-1d": BenchInfo(False),
    "robot-resource-2d": BenchInfo(False),
    "running-example-normal": BenchInfo(True),
    "elevator": BenchInfo(
        True,
        {"sweap": "elevator-paper", "sweap-noacc": "elevator-paper"}),
    "reversible-lane-u": BenchInfo(False),
    "heim-buchi-unreal": BenchInfo(False),
    "infinite-race": BenchInfo(True),
    "robot-grid-reach-repeated-with-obstacles-1d": BenchInfo(True),
    "robot-grid-reach-repeated-with-obstacles-2d": BenchInfo(True),
    "taxi-service": BenchInfo(True)
}

finite_benchs = {
    "elevator-simple-3": BenchInfo(True),
    "elevator-simple-5": BenchInfo(True),
    "elevator-simple-10": BenchInfo(True),
    "elevator-simple-50": BenchInfo(True),
    "elevator-signal-3": BenchInfo(True),
    "elevator-signal-5": BenchInfo(True),
    "elevator-signal-10": BenchInfo(
        True,
        {"sweap": "arbiter-paper-10", "sweap-noacc": "arbiter-paper-10"}),
    "elevator-signal-50": BenchInfo(
        True,
        {"sweap": "arbiter-paper-50", "sweap-noacc": "arbiter-paper-50"}),
    "arbiter-5": BenchInfo(
        True,
        {"sweap": "arbiter-paper-5", "sweap-noacc": "arbiter-paper-5"}),
    "arbiter-10": BenchInfo(
        True,
        {"sweap": "arbiter-paper-10", "sweap-noacc": "arbiter-paper-10"}),
    "arbiter-50": BenchInfo(
        True,
        {"sweap": "arbiter-paper-50", "sweap-noacc": "arbiter-paper-50"}),
    "arbiter-unreal-5": BenchInfo(
        False,
        {"sweap": "arbiter-paper-unreal-5", 
         "sweap-noacc": "arbiter-paper-unreal-5"}),
    "arbiter-unreal-10": BenchInfo(False,
        {"sweap": "arbiter-paper-unreal-10", 
         "sweap-noacc": "arbiter-paper-unreal-10"}),
    "arbiter-unreal-50": BenchInfo(False,
        {"sweap": "arbiter-paper-unreal-50", 
         "sweap-noacc": "arbiter-paper-unreal-50"}),
    "robot-grid-reach-1d-5": BenchInfo(True),
    "robot-grid-reach-1d-10": BenchInfo(True),
    "robot-grid-reach-1d-50": BenchInfo(True),
    "robot-grid-reach-2d-5": BenchInfo(True),
    "robot-grid-reach-2d-10": BenchInfo(True),
    "robot-grid-reach-2d-50": BenchInfo(True),
    "elevator-5": BenchInfo(
        True,
        {"sweap": "elevator-paper-5", "sweap-noacc": "elevator-paper-5"}),
    "elevator-10": BenchInfo(
        True,
        {"sweap": "elevator-paper-10", "sweap-noacc": "elevator-paper-10"}),
    "elevator-50": BenchInfo(
        True,
        {"sweap": "elevator-paper-50", "sweap-noacc": "elevator-paper-50"}),
    "reversible-lane-r-5": BenchInfo(True),
    "reversible-lane-r-10": BenchInfo(True),
    "reversible-lane-r-50": BenchInfo(True),
    "reversible-lane-u-5": BenchInfo(False),
    "reversible-lane-u-10": BenchInfo(False),
    "reversible-lane-u-50": BenchInfo(False),
}


runtime_re = re.compile(r"Runtime: ([0-9]+)ms")
timeout = 600000

out_files = {t: glob.glob(f"out-{t}-[0-9]*") for t in tools}

def get_result(tool, tool_info, bench, bench_info):
    result = None
    try:
        bench = (
            bench_info.aliases.get(tool, bench)
            if bench_info.aliases
            else bench)
        raw_result = check_output([
            "grep", "-A", "2", 
            f"Benchmark:.*{bench}\.{tool_info.ext}", fname],
            encoding="utf-8")
        if m := runtime_re.search(raw_result):
            runtime = int(m.group(1))
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
        else:
            raise ValueError(f"{bench=}, {tool=} [no runtime]")
    except CalledProcessError:
        result = 1
    finally:
        if result is None:
            raise ValueError(f"{bench=}, {tool=}")
    return result

writer = csv.writer(sys.stdout)
for benchs in (infinite_benchs, finite_benchs):
    writer.writerow(["row-id", "benchmark", *tools])
    for i, b in enumerate(benchs, start=2):
        row = [i, b]
        bench_info = benchs[b]
        for tool, tool_info in tools.items():
            result = None
            if not out_files.get(tool, []):
                result = 1
            else:
                fname = out_files[tool][0]
                result = get_result(tool, tool_info, b, bench_info)
            row.append(result)
        writer.writerow(row)
    print("-"*30)
