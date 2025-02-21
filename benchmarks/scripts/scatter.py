#!/usr/bin/env python3
import sys
from pathlib import Path

import polars as pl
import seaborn as sns
import matplotlib as mpl
from functools import reduce

mpl.rc("font", family="serif", size=11)

TIMEOUT = 1200000

if len(sys.argv) < 2:
    print(f"Usage: {sys.argv[0]} <file.csv>")
    sys.exit(1)
FILENAME = sys.argv[1]
DIR = Path(FILENAME).parent

exclude_full_ltl = True

tools = [
    name
    for name in pl.scan_csv(FILENAME).columns
    if name not in ("row-id", "benchmark", "temos", "sweap-nobin")]

legend = {
    "sweap": "Our tool (synthesis)",
    "sweap-noacc": "Our tool, lazy (synthesis)",
    "raboniel": "Raboniel (synthesis)",
    "rpgsolve-syn": "Rpgsolve (synthesis)",
    "rpg-stela": "Rpg-stela (realisability)",
    "rpgsolve": "Rpgsolve (realisability)",
    "tslmt2rpg": "tslmt2rpg (realisability)",
    "tslmt2rpg-syn": "tslmt2rpg (synthesis)"
}

full_ltl_benchs = {
    "arbiter",
    "arbiter-failure",
    "elevator",
    "infinite-race",
    "infinite-race-u",
    "infinite-race-unequal-1",
    "infinite-race-unequal-2",
    "reversible-lane-r",
    "reversible-lane-u",
    "rep-reach-obst-1d",
    "rep-reach-obst-2d",
    "rep-reach-obst-6d",
    "robot_collect_v4",
    "taxi-service",
    "taxi-service-u",
} if exclude_full_ltl else tuple()

realisable = {
    "F-G-contradiction-1": False,
    "F-G-contradiction-2": False,
    "f-real": True,
    "f-unreal": False,
    "ordered-visits": True,
    "ordered-visits-choice": True,
    "precise-reachability": True,
    "robot-to-target": True,
    "robot-to-target-unreal": False,
    "robot-to-target-charging": True,
    "robot-to-target-charging-unreal": False,
    "thermostat-F": True,
    "thermostat-F-unreal": False,
    "unordered-visits-charging": True,
    "unordered-visits": True,
    **{f"chain-{i}": True for i in (4, 5, 6, 7)},
    **{f"chain-simple-{i}": True for i in (5, 10, 20, 30, 40, 50, 60, 70)},
    "items_processing": True,
    "robot_analyze": True,
    **{f"robot_collect_v{i}": True for i in (1, 2, 3)},
    **{f"robot_deliver_v{i}": True for i in (1, 2, 3, 4, 5)},
    "robot_repair": True,
    "robot_running": True,
    "scheduler": True,
    "heim-buechi": True,
    "heim-fig7": False,
    "robot-commute-1d": True,
    "robot-commute-2d": True,
    "robot-resource-1d": False,
    "robot-resource-2d": False,
    "box": True,
    "box-limited": True,
    "diagonal": True,
    "evasion": True,
    "follow": True,
    "solitary": True,
    "square": True,
    "g-real": True,
    "g-unreal-1": False,
    "g-unreal-2": False,
    "g-unreal-3": False,
    "heim-double-x": True,
    "robot-cat-real-1d": True,
    "robot-cat-unreal-1d": False,
    "robot-cat-real-2d": True,
    "robot-cat-unreal-2d": False,
    "robot-grid-reach-1d": True,
    "robot-grid-reach-2d": True,
    "robot-tasks": True,
    "buffer-storage": True,
    "gf-real": True,
    "gf-unreal": False,
    "GF-G-contradiction": False,
    "helipad": True,
    "helipad-contradict": False,
    "package-delivery": True,
    "patrolling": True,
    "patrolling-alarm": True,
    "storage-GF-64": True,
    "tasks": True,
    "tasks-unreal": False,
    "thermostat-GF": True,
    "thermostat-GF-unreal": False,
    "sort4": True,
    "sort5": True,
}

csv = (
    pl.scan_csv(FILENAME).filter(pl.col("benchmark").is_not_null())
    .filter(pl.col("benchmark").is_in(full_ltl_benchs).not_())
    .filter(pl.col("sweap") > 1)
    .with_columns(
        pl.col("benchmark").map_elements(realisable.get, return_dtype=pl.Boolean).alias("realisable"),
        (pl.col("sweap")/1000).alias("sweap (s)")
        )
)

tool_times = [(
    csv
    .filter(pl.col(t) > 1)
    .select(
        "benchmark", "sweap (s)", "realisable", tool=pl.lit(t), 
        **{"other (s)": pl.col(t)/1000})
    ).collect()
    for t in tools if t != "sweap"]

tool_times = reduce(lambda x, y: x.vstack(y), tool_times)

scatter = sns.scatterplot(
    data=tool_times.to_pandas(),
    x="sweap (s)", y="other (s)", hue="tool", style="realisable",
    markers="Xo")
sns.move_legend(scatter, "upper left", bbox_to_anchor=(1, 1))
xmin=0.7E-1
xmax=TIMEOUT/1000
scatter.set_xlim(left=xmin, right=xmax)
scatter.set_ylim(bottom=xmin, top=xmax)
scatter.set_clip_on(False)
mpl.pyplot.setp(scatter.collections, clip_on=False)
mpl.pyplot.setp(scatter.artists, clip_on=False)

ln = sns.lineplot(x=[xmin,xmax], y=[xmin,xmax], ax=scatter)

scatter.set(yscale='log')
scatter.set(xscale='log')
scatter.figure.savefig("scatter.png", dpi=300)
