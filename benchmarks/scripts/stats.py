#!/usr/bin/env python3

import sys
from itertools import product
from pathlib import Path

import polars as pl


TIMEOUT = 600_000


pretty_tool_names = {
    "sweap-strix": "Sweap-strix",
    "sweap-pf": "Sweap (portfolio)",
    "sweap-dual": "Sweap (Dual)",
    "sweap-rpg": "Sweap (RPG)",
    "sweap-rpg-dual": "Sweap (RPG, Dual)",
    "sweap-tsl": "Sweap (TSL)",
    "sweap-tsl-dual": "Sweap (TSL, Dual)",
    "sweap-issy": "Sweap (Issy format)",
    "sweap-issy-dual": "Sweap (Issy format, Dual)",
    "sweap-semml": "Sweap (SemML)",
    "issy3": "Issy",
    "issy3-rpg": "Issy (RPG)",
    "issy3-tsl": "Issy (TSL)",
    "sweap-tsl-pf": "Sweap (TSL, portfolio)",
    "sweap-rpg-pf": "Sweap (RPG, portfolio)",
    "sweap-issy-pf": "Sweap (ISSY, portfolio)"
}


if len(sys.argv) < 2:
    print("Usage: ./stats.py <file.csv>")
    sys.exit(1)
FILENAME = sys.argv[1]
DIR = Path(FILENAME).parent
csv0 = pl.read_csv(FILENAME)


def compare(language, realisable, TOOLS):
    all_benchmarks = (
        csv0.filter(pl.col("tool").is_in(TOOLS))
        .filter(True if realisable is None else pl.col("real") if realisable else ~pl.col("real"))
        .select("benchmark")
        .unique()).height

    csv1 = (
        csv0
        .filter(pl.col("tool").is_in(TOOLS))
        .filter(True if realisable is None else pl.col("real") if realisable else ~pl.col("real"))
        .with_columns((pl.col("time(ms)")/1000).clip(0, TIMEOUT/1000).alias("time(s)"))
        .pivot(values=["time(s)", "verdict", "real", "goal"], index="benchmark", on="tool")
    ).select([
        pl.col("benchmark"),
        *[
            pl.col(f"{col}_{tool}").alias(f"{col}_{tool}")
            for tool, col in product(reversed(TOOLS), ["time(s)", "verdict", "real", "goal"])
        ]])

    solved_only_by_tool0 = csv1.filter(
        (pl.col(f"real_{TOOLS[0]}") & 
         pl.col(f"verdict_{TOOLS[0]}").is_in(["realizable"]) &
         ~(pl.col(f"verdict_{TOOLS[1]}").is_in(["realizable"])))
        |
        (~pl.col(f"real_{TOOLS[0]}") &
         pl.col(f"verdict_{TOOLS[0]}").is_in(["unrealizable"]) &
         ~(pl.col(f"verdict_{TOOLS[1]}").is_in(["unrealizable"]))))
    solved_only_by_tool1 = csv1.filter(
        (pl.col(f"real_{TOOLS[0]}") & 
         pl.col(f"verdict_{TOOLS[1]}").is_in(["realizable"]) &
         ~(pl.col(f"verdict_{TOOLS[0]}").is_in(["realizable"])))
        |
        (~pl.col(f"real_{TOOLS[0]}") &
         pl.col(f"verdict_{TOOLS[1]}").is_in(["unrealizable"]) &
         ~(pl.col(f"verdict_{TOOLS[0]}").is_in(["unrealizable"]))) 
        )
    solved_by_both = csv1.filter((
        pl.col(f"real_{TOOLS[0]}") &
        pl.col(f"verdict_{TOOLS[0]}").is_in(["realizable"]) &
        pl.col(f"verdict_{TOOLS[1]}").is_in(["realizable"])) | (
            ~pl.col(f"real_{TOOLS[0]}") &
            pl.col(f"verdict_{TOOLS[0]}").is_in(["unrealizable"]) &
            pl.col(f"verdict_{TOOLS[1]}").is_in(["unrealizable"])))

    not_oom = ["realizable", "unrealizable", "timeout"]
    csv = (
        csv1
        .with_columns((pl.col(f"goal_{TOOLS[0]}")+"_"+pl.col(f"real_{TOOLS[0]}")).alias("category"))
        .filter(pl.col(f"time(s)_{TOOLS[0]}").is_not_null())
        .filter(pl.col(f"time(s)_{TOOLS[1]}").is_not_null())
        .filter(pl.col(f"verdict_{TOOLS[0]}").is_in(not_oom))
        .filter(pl.col(f"verdict_{TOOLS[1]}").is_in(not_oom))
        .filter(
            (pl.col(f"verdict_{TOOLS[0]}") != "timeout") |
            (pl.col(f"verdict_{TOOLS[1]}") != "timeout")))

    fmt_real = (
        "realizable" if realisable else
        "unrealizable" if realisable is not None else "all")

    print(f"{language} ({fmt_real}),{all_benchmarks},{pretty_tool_names[TOOLS[0]]},{solved_by_both.height + solved_only_by_tool0.height},{(csv[f'time(s)_{TOOLS[0]}'] < csv[f'time(s)_{TOOLS[1]}']).sum()},{solved_only_by_tool0.height}")  # noqa: E501
    print(f"{language} ({fmt_real}),{all_benchmarks},{pretty_tool_names[TOOLS[1]]},{solved_by_both.height + solved_only_by_tool1.height},{(csv[f'time(s)_{TOOLS[1]}'] < csv[f'time(s)_{TOOLS[0]}']).sum()},{solved_only_by_tool1.height}")  # noqa: E501


print("format+realisability,benchmarks,tool,solved,fastest,unique")
compare("prog", None, ["sweap-strix", "sweap-pf"])
compare("prog", None, ["sweap-semml", "sweap-dual"])
compare("issy", True, ["issy3", "sweap-issy-pf"])
compare("issy", False, ["issy3", "sweap-issy-pf"])
compare("rpg", True, ["issy3-rpg", "sweap-rpg-pf"])
compare("rpg", False, ["issy3-rpg", "sweap-rpg-pf"])
compare("tsl", True, ["issy3-tsl", "sweap-tsl-pf"])
compare("tsl", False, ["issy3-tsl", "sweap-rpg-pf"])
