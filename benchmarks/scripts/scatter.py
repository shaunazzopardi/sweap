#!/usr/bin/env python3
import sys
from itertools import product
from pathlib import Path


import polars as pl
import seaborn as sns
import matplotlib as mpl
from functools import reduce


mpl.rc("font", family="serif", size=11)

FORMAT = "pdf"
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
    "issy2": "Issy",
    "issy2-rpg": "Issy (RPG)",
    "issy2-tsl": "Issy (TSL)",
    "sweap-tsl-pf": "Sweap (TSL, portfolio)",
    "sweap-rpg-pf": "Sweap (RPG, portfolio)",
    "sweap-issy-pf": "Sweap (ISSY, portfolio)",
}


if len(sys.argv) < 4:
    print("Usage: ./scatter.py <file.csv> <tool1> <tool2>")
    sys.exit(1)
FILENAME = sys.argv[1]
DIR = Path(FILENAME).parent
TOOLS = [sys.argv[2], sys.argv[3]]

csv0 = pl.read_csv(FILENAME)
min_time = csv0.filter(pl.col("verdict").is_in(["realizable", "unrealizable"]))["time(ms)"].min()
min_time /= 1000  # convert to seconds
print(f"[INFO] min_time: {min_time}", file=sys.stderr)



csv1 = (
    csv0.filter(pl.col("tool").is_in(TOOLS))
    .with_columns((pl.col("time(ms)")/1000).clip(0, TIMEOUT/1000).alias("time(s)"))
    .pivot(values=["time(s)", "verdict", "real", "goal"], index="benchmark", on="tool")
)

# print all rows of csv1
# pl.Config.set_tbl_rows(csv1.height)
# print(csv1)

def pprint(row, tool):
    def fmt(expected):
        return (
            str(round(row["time(s)_"+tool], 2))
            if row["verdict_"+tool] == expected else "X")

    if row["time(s)_"+tool] is None:
        return None
    if row["verdict_"+tool] == "oom":
        return "OOM" 
    if row["time(s)_"+tool] >= TIMEOUT/1000 or row["verdict_"+tool] == "timeout":
        return r"\phantom{O}"
    if row["verdict_"+tool] == "error":
        return "ERR"
    if "bullet" in row["R"]:
        return fmt("realizable")
    else:
        return fmt("unrealizable")

xx = csv1.select([
    pl.col("benchmark"),
    pl.col(f"real_{TOOLS[0]}").map_elements(lambda x: r"$\bullet$" if x else r"\phantom{X}").alias("R"),
    *[
        pl.col(f"{col}_{tool}").alias(f"{col}_{tool}")
        for tool, col in product(reversed(TOOLS), ["time(s)", "verdict"])
    ]]).with_columns(
        pl.struct("R", "time(s)_"+TOOLS[0], "verdict_"+TOOLS[0])
        .map_elements(lambda x: pprint(x, TOOLS[0]), return_dtype=pl.Utf8)
        .alias(pretty_tool_names[TOOLS[0]] + " (s)"),
        pl.struct("R", "time(s)_"+TOOLS[1], "verdict_"+TOOLS[1])
        .map_elements(lambda x: pprint(x, TOOLS[1]), return_dtype=pl.Utf8)
        .alias(pretty_tool_names[TOOLS[1]] + " (s)")
    ).select([
        pl.col("benchmark").alias("Name"),
        pl.col("R"),
        pl.col(pretty_tool_names[TOOLS[1]] + " (s)"),
        pl.col(pretty_tool_names[TOOLS[0]] + " (s)"),
    ])

ltx = (
    xx.to_pandas().to_latex(index=False)
    .replace("tacas26-", "")
    .replace(" (ISSY, portfolio)", "")
    .replace(" (RPG, portfolio)", "")
    .replace(" (TSL, portfolio)", "")
    .replace("_", "-")
    )
ltx_lines = ltx.splitlines()
n = len(ltx_lines)+2
if n > 80:
    ltx_lines = (
        [ltx_lines[0].replace("\\begin{tabular}", "\\begin{tabular}[t]")] +
        ltx_lines[1:n//2] +
        ["\\bottomrule", "\\end{tabular}"] +
        [ltx_lines[0].replace("\\begin{tabular}", "\\begin{tabular}[t]")] +
        ltx_lines[1:4] +
        ltx_lines[n//2:])
print("\n".join(ltx_lines))


solved_only_by_tool0 = csv1.filter(
    (pl.col(f"real_{TOOLS[0]}") & 
    pl.col(f"verdict_{TOOLS[0]}").is_in(["realizable"]) &
    ~(pl.col(f"verdict_{TOOLS[1]}").is_in(["realizable"])))
    |
    (~pl.col(f"real_{TOOLS[0]}") &
    pl.col(f"verdict_{TOOLS[0]}").is_in(["unrealizable"]) &
    ~(pl.col(f"verdict_{TOOLS[1]}").is_in(["unrealizable"])))
    )
solved_only_by_tool1 = csv1.filter(
    (pl.col(f"real_{TOOLS[0]}") & 
    pl.col(f"verdict_{TOOLS[1]}").is_in(["realizable"]) &
    ~(pl.col(f"verdict_{TOOLS[0]}").is_in(["realizable"])))
    |
    (~pl.col(f"real_{TOOLS[0]}") &
    pl.col(f"verdict_{TOOLS[1]}").is_in(["unrealizable"]) &
    ~(pl.col(f"verdict_{TOOLS[0]}").is_in(["unrealizable"]))) 
    )
solved_by_both = csv1.filter(
    (
        (pl.col(f"real_{TOOLS[0]}") & 
        pl.col(f"verdict_{TOOLS[0]}").is_in(["realizable"]) &
        pl.col(f"verdict_{TOOLS[1]}").is_in(["realizable"]))
        |
        (~pl.col(f"real_{TOOLS[0]}") &
        pl.col(f"verdict_{TOOLS[0]}").is_in(["unrealizable"]) &
        pl.col(f"verdict_{TOOLS[1]}").is_in(["unrealizable"]))
    )
)

solved_by_none = csv1.filter(
    (pl.col(f"real_{TOOLS[0]}") & 
    ~(pl.col(f"verdict_{TOOLS[0]}").is_in(["realizable"])) &
    ~(pl.col(f"verdict_{TOOLS[1]}").is_in(["realizable"])))
    |
    (~pl.col(f"real_{TOOLS[0]}") &
    ~(pl.col(f"verdict_{TOOLS[0]}").is_in(["unrealizable"])) &
    ~(pl.col(f"verdict_{TOOLS[1]}").is_in(["unrealizable"])))
)

print(f"[INFO] Number of data points: {csv1.height}", file=sys.stderr)
print(f"[INFO] solved by both: {solved_by_both.height}", file=sys.stderr)
print(f"[INFO] solved by none: {solved_by_none.height}", file=sys.stderr)
print(f"[INFO] solved only by {TOOLS[0]}: {solved_only_by_tool0.height}", file=sys.stderr)
print(f"[INFO] solved only by {TOOLS[1]}: {solved_only_by_tool1.height}", file=sys.stderr)

with pl.Config(tbl_rows=30):
    print(f"[INFO] solved only by {TOOLS[0]}: {solved_only_by_tool0["benchmark", f"real_{TOOLS[0]}"].unique()}", file=sys.stderr)
    print(f"[INFO] solved only by {TOOLS[1]}: {solved_only_by_tool1["benchmark", f"real_{TOOLS[1]}"].unique()}", file=sys.stderr)

csv = (
    csv1
    .with_columns((pl.col(f"goal_{TOOLS[0]}")+"_"+pl.col(f"real_{TOOLS[0]}")).alias("category"))
    # fill nulls with timeout in verdict
    .filter(pl.col(f"time(s)_{TOOLS[0]}").is_not_null())
    .filter(pl.col(f"time(s)_{TOOLS[1]}").is_not_null())
    .filter(pl.col(f"verdict_{TOOLS[0]}").is_in(["realizable", "unrealizable", "timeout"]))
    .filter(pl.col(f"verdict_{TOOLS[1]}").is_in(["realizable", "unrealizable", "timeout"]))
    .filter((pl.col(f"verdict_{TOOLS[0]}") != "timeout") | (pl.col(f"verdict_{TOOLS[1]}") != "timeout"))
)

print(csv, file=sys.stderr)
print(f"[INFO] Number of data points (w/o oom or errors): {csv.height}", file=sys.stderr)
print(f"[INFO] {TOOLS[0]} wins: {(csv[f'time(s)_{TOOLS[0]}'] < csv[f'time(s)_{TOOLS[1]}']).sum()}", file=sys.stderr)
print(f"[INFO] {TOOLS[1]} wins: {(csv[f'time(s)_{TOOLS[1]}'] < csv[f'time(s)_{TOOLS[0]}']).sum()}", file=sys.stderr)
print(f"[INFO] {TOOLS[0]} wins and {TOOLS[1]} times out: {((csv[f'time(s)_{TOOLS[0]}'] < csv[f'time(s)_{TOOLS[1]}']) & (csv[f'time(s)_{TOOLS[1]}'] == TIMEOUT/1000)).sum()}", file=sys.stderr)
print(f"[INFO] {TOOLS[1]} wins and {TOOLS[0]} times out: {((csv[f'time(s)_{TOOLS[1]}'] < csv[f'time(s)_{TOOLS[0]}']) & (csv[f'time(s)_{TOOLS[0]}'] == TIMEOUT/1000)).sum()}", file=sys.stderr)


with pl.Config(tbl_rows=30):
    print(f"{TOOLS[0]} wins:", file=sys.stderr)
    print(csv.filter(pl.col(f'time(s)_{TOOLS[0]}') < pl.col(f'time(s)_{TOOLS[1]}')).select("benchmark", f"real_{TOOLS[0]}"), file=sys.stderr)

# min_time_tool0 = csv[f"time(s)_{TOOLS[0]}"].min()
# min_time_tool1 = csv[f"time(s)_{TOOLS[1]}"].min()
# min_time = min(min_time_tool0, min_time_tool1)
real_color, unreal_color = "orange", "blue"
# markers = "sDov"

markers = {
    "safety_true": "s",
    "safety_false": "s",
    "reach_true": "D",
    "reach_false": "D",
    "buechi_true": "o",
    "buechi_false": "o",
    "ltl_true": "v",
    "ltl_false": "v",
    "issy_true": "P",
    "issy_false": "P",
}



scatter = sns.scatterplot(
    data=csv.filter(pl.col(f"real_{TOOLS[0]}")).to_pandas(),
    x=f"time(s)_{TOOLS[0]}", y=f"time(s)_{TOOLS[1]}",
    markers=markers, palette=[real_color],
    style=f"category", hue=f"real_{TOOLS[0]}",
    clip_on=False)
scatter2 = sns.scatterplot(
    data=csv.filter(~pl.col(f"real_{TOOLS[0]}")).to_pandas(), ax=scatter,
    x=f"time(s)_{TOOLS[0]}", y=f"time(s)_{TOOLS[1]}",
    markers=markers,
    facecolors="none",
    edgecolor=unreal_color,
    style=f"category",
    clip_on=False,
    s=(mpl.rcParams['lines.markersize'] ** 1.8)
    )


scatter.set_xlabel(f"{pretty_tool_names.get(TOOLS[0], TOOLS[0])} time (s)")
scatter.set_ylabel(f"{pretty_tool_names.get(TOOLS[1], TOOLS[1])} time (s)")

xmax=TIMEOUT/1000
ln = sns.lineplot(x=[min_time,xmax], y=[min_time,xmax], ax=scatter, color='red', linewidth=1, clip_on=False)

handles, labels = scatter.get_legend_handles_labels()
indices = [i for i, lbl in enumerate(labels) if any(x in lbl for x in ["true", "false"])]
for idx in indices:
    if "true" in labels[idx]:
        handles[idx].set_markerfacecolor(real_color)

hh = [handles[i] for i in indices]
ll = (labels[i].capitalize() for i in indices)

ll = (lbl.replace("_true", " (R)") for lbl in ll)
ll = (lbl.replace("uechi", "üchi") for lbl in ll)
ll = (lbl.replace("Ltl", "LTL") for lbl in ll)
ll = [lbl.replace("_false", " (U)") for lbl in ll]


scatter.legend(hh, ll,
    title="Category",
    loc='upper center',
    bbox_to_anchor=(0.5, -0.15),
    ncol=3)

# make plot square
scatter.set_aspect('equal', adjustable='box')

scatter.set_xlim(min_time, xmax)
scatter.set_ylim(min_time, xmax)
# scatter.set_ybound(lower=0, upper=xmax)
scatter.set(yscale='log')
scatter.set(xscale='log')


# add a tick at TIMEOUT on both axes
for (get_ticks, set_ticks, get_labels, set_labels) in [
    (scatter.get_xticks, scatter.set_xticks, scatter.get_xticklabels, scatter.set_xticklabels),
    (scatter.get_yticks, scatter.set_yticks, scatter.get_yticklabels, scatter.set_yticklabels),
]:
     current_ticks = get_ticks().tolist()
     current_ticks = [t for t in current_ticks if min_time <= t <= TIMEOUT/1000]
     if TIMEOUT/1000 not in current_ticks:
         current_ticks.append(TIMEOUT/1000)
         set_ticks(current_ticks)
         # add label to the tick    
         labels = [item.get_text() for item in get_labels()]
         labels[-1] = ("TO")
         set_labels(labels)

fig = scatter.get_figure()
scatter.get_legend().remove()
fig.subplots_adjust(left=-0.1)
for fmt in ("png", "pdf"):
    pass
    # fig.savefig(
    #     DIR / f"scatter_{TOOLS[0]}_{TOOLS[1]}.{fmt}",
    #     dpi=300, bbox_inches='tight', pad_inches=0.05)

# save legend separately
fig_legend = mpl.figure.Figure(figsize=(3, 1))
ax_legend = fig_legend.add_subplot(111)
# remove frame
ax_legend.axis('off')
fig_legend.legend(
    hh, ll,
    title="Category",
    loc='center',
    ncol=4)
if len(hh) >= 8:
    fig_legend.savefig(
        DIR / f"scatter_legend.pdf",
        dpi=300, bbox_inches='tight', pad_inches=0.1)
