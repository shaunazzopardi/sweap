#!/usr/bin/env python3
import sys
from pathlib import Path

import polars as pl
import seaborn as sns
import matplotlib as mpl
from functools import reduce


mpl.rc("font", family="serif", size=11)

FORMAT = "pdf"
TIMEOUT = 600_000


if len(sys.argv) < 4:
    print("Usage: ./cactus.py <file.csv> <tool1> <tool2>")
    sys.exit(1)
FILENAME = sys.argv[1]
DIR = Path(FILENAME).parent
TOOLS = [sys.argv[2], sys.argv[3]]
csv1 = (
    pl.read_csv(FILENAME)
    .filter(pl.col("tool").is_in(TOOLS))
    # Filter out wrong verdicts
    .filter(~(pl.col("real") & (pl.col("verdict") == "unrealizable")))
    .filter(~(~pl.col("real") & (pl.col("verdict") == "realizable")))
    .with_columns((pl.col("time(ms)")/1000).clip(0, TIMEOUT/1000).alias("time(s)"))
    .pivot(values=["time(s)", "verdict", "real"], index="benchmark", columns="tool")
)

print(f"Number of data points (with oom and errors): {csv1.height}")
solved_only_by_tool0 = csv1.filter(
    (pl.col(f"verdict_{TOOLS[0]}").is_in(["realizable", "unrealizable"])) &
    ~(pl.col(f"verdict_{TOOLS[1]}").is_in(["realizable", "unrealizable"]))
).height
solved_only_by_tool1 = csv1.filter(
    (pl.col(f"verdict_{TOOLS[1]}").is_in(["realizable", "unrealizable"])) &
    ~(pl.col(f"verdict_{TOOLS[0]}").is_in(["realizable", "unrealizable"]))
).height
print(f"Solved only by {TOOLS[0]}: {solved_only_by_tool0}")
print(f"Solved only by {TOOLS[1]}: {solved_only_by_tool1}")
print(f"Solved by none: {csv1.filter(
    ~(pl.col(f"verdict_{TOOLS[0]}").is_in(["realizable", "unrealizable"])) &
    ~(pl.col(f"verdict_{TOOLS[1]}").is_in(["realizable", "unrealizable"]))
).height}")
print(f"Solved by both: {csv1.filter(
    (pl.col(f"verdict_{TOOLS[0]}").is_in(["realizable", "unrealizable"])) &
    (pl.col(f"verdict_{TOOLS[1]}").is_in(["realizable", "unrealizable"]))
).height}")

csv = (
    csv1
    .filter(pl.col(f"time(s)_{TOOLS[0]}").is_not_null())
    .filter(pl.col(f"time(s)_{TOOLS[1]}").is_not_null())
    .filter(pl.col(f"verdict_{TOOLS[0]}").is_in(["realizable", "unrealizable", "timeout"]))
    .filter(pl.col(f"verdict_{TOOLS[1]}").is_in(["realizable", "unrealizable", "timeout"]))
    .filter((pl.col(f"verdict_{TOOLS[0]}") != "timeout") | (pl.col(f"verdict_{TOOLS[1]}") != "timeout"))
)

# print(csv)
print(f"Number of data points (w/o oom or errors): {csv.height}")
print(f"{TOOLS[0]} wins: {(csv[f'time(s)_{TOOLS[0]}'] < csv[f'time(s)_{TOOLS[1]}']).sum()}")
print(f"{TOOLS[1]} wins: {(csv[f'time(s)_{TOOLS[1]}'] < csv[f'time(s)_{TOOLS[0]}']).sum()}")

print(f"{TOOLS[0]} wins and {TOOLS[1]} times out: {((csv[f'time(s)_{TOOLS[0]}'] < csv[f'time(s)_{TOOLS[1]}']) & (csv[f'time(s)_{TOOLS[1]}'] == TIMEOUT/1000)).sum()}")
print(f"{TOOLS[1]} wins and {TOOLS[0]} times out: {((csv[f'time(s)_{TOOLS[1]}'] < csv[f'time(s)_{TOOLS[0]}']) & (csv[f'time(s)_{TOOLS[0]}'] == TIMEOUT/1000)).sum()}")




min_time_tool0 = csv[f"time(s)_{TOOLS[0]}"].min()
min_time_tool1 = csv[f"time(s)_{TOOLS[1]}"].min()
min_time = min(min_time_tool0, min_time_tool1)

scatter = sns.scatterplot(
    data=csv.to_pandas(),
    x=f"time(s)_{TOOLS[0]}", y=f"time(s)_{TOOLS[1]}",
    style=f"real_{TOOLS[0]}", clip_on=False)
xmax=TIMEOUT/1000
ln = sns.lineplot(x=[min_time,xmax], y=[min_time,xmax], ax=scatter, color='red', clip_on=False)

handles, labels  =  scatter.get_legend_handles_labels()
scatter.legend(handles, ['False', 'True'], loc='upper left', title='Realisable')


scatter.set_xlim(min_time, xmax)
scatter.set_ylim(min_time, xmax)
# scatter.set_ybound(lower=0, upper=xmax)
scatter.set(yscale='log')
scatter.set(xscale='log')
fig = scatter.get_figure()
fig.set_size_inches(5,5)
# fig.tight_layout()
fig.savefig(DIR / f"scatter_{TOOLS[0]}_{TOOLS[1]}.png", dpi=300)