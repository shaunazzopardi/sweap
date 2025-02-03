#!/usr/bin/env python3
import sys

import polars as pl
import seaborn as sns
import matplotlib as mpl
import matplotlib.pyplot as plt
from functools import reduce

mpl.rc("font", family="serif", size=11)

FORMAT = "pdf"
TIMEOUT = 1200000


if len(sys.argv) < 2:
    print("Usage: ./cactus.py <file.csv>")
    sys.exit(1)
FILENAME = sys.argv[1]

exclude_full_ltl = True
lineplot_config = dict(markers="osdPso^XX", markersize=5)


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

linestyles = {
    legend["sweap"]: "-",
    legend["sweap-noacc"]: "--",
    legend["raboniel"]: "-.",
    # legend["temos"]: "--",
    legend["rpgsolve-syn"]: "-",
    legend["rpgsolve"]: ":",
    legend["rpg-stela"]: ":",
    legend["tslmt2rpg"]: ":",
    legend["tslmt2rpg-syn"]: "--"
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


def cum_sum(tool_name: str):
    col_name = legend.get(tool_name, tool_name)
    q = (
        pl.scan_csv(FILENAME)
        .filter(pl.col(tool_name) > 1)
        .filter(pl.col(tool_name) < TIMEOUT)
        .filter(pl.col("benchmark").is_in(full_ltl_benchs).not_())
        .sort(by=tool_name)
        .with_row_index("instances", 1)
        .select(instances=pl.col("instances"), **{"time": pl.cum_sum(tool_name)/1000}, tool=pl.lit(col_name))
    )
    df = q.collect()
    return df

dataframes = [cum_sum(x) for x in tools]
for x in dataframes:
    print(x)

stacked = reduce(lambda x, y: x.vstack(y), dataframes)
print(stacked)

## Easiest 20 instances
dataframes_easy = [x.limit(20) for x in dataframes]
stacked_easy = reduce(lambda x, y: x.vstack(y), dataframes_easy)
plot_easy = sns.lineplot(
    data=stacked_easy.sort(pl.col("tool")).to_pandas(), x="instances", y="time",
    hue="tool", style="tool",
    **lineplot_config)


plot_easy.set_ylim(bottom=0.5E-2)

# Some black magic to sort & add headers to our legend
dummy = mpl.lines.Line2D([], [], color="none")
handles, labels = plot_easy.get_legend_handles_labels()

# Force linestyles
for i, tool in enumerate(labels):
    for ln in (plot_easy.lines[i], handles[i]):
        ln.set_linestyle(linestyles.get(tool, '-'))
        ln.set_linewidth(1.2)

zipped = list(zip(handles, labels))

# Save styles for later
styles = {lbl: line2d for line2d, lbl in zipped}
def sort(handle_label):
    _, label = handle_label
    return ("realisability" in label, label)

zipped = sorted(zipped, key=sort)
handles, labels = (list(x) for x in zip(*zipped))
labels = [x.replace(" (realisability)", "").replace(" (synthesis)", "") for x in labels]
handles.insert(0, dummy)
labels.insert(0, "$\\bf{Synthesis}$")

handles.insert(4, dummy)
labels.insert(4, "$\\bf{Synthesis}$")

handles.insert(7, dummy)
labels.insert(7, "$\\bf{Realisability}$")
handles.insert(7, dummy)
labels.insert(7, "")

plot_easy.legend(handles, labels, ncol=3)

newline = '\n'
plot_easy.set_title(f"Behaviour on first 20 solved instances{newline + ' (excl. novel LTL instances)' if exclude_full_ltl else ''}")
plot_easy.set(xlabel="Instances solved")
plot_easy.set(ylabel="Cumulative time (s)")
plot_easy.set(yscale='log')
plot_easy.set(xticks=[1,5,10,15,20])


fig = plot_easy.get_figure()
fig.tight_layout()
fig.savefig(f"cactus-easy.{FORMAT}", dpi=300)
fig.clear()


# real_df = (
#     joined
#     .drop(*(
#         name for name in legend.values()
#         if name in joined.columns and 
#         "(realisability)" not in name and
#         "Our tool" not in name)))

stacked_real = (
    stacked
    .filter(
        pl.col("tool").str.contains("realisability") | 
        pl.col("tool").str.contains("Our tool")))

plot_real = sns.lineplot(
    data=stacked_real.to_pandas(),
    x="instances", y="time",
    hue="tool", style="tool",
    **lineplot_config)
# plot_real.set(yscale='log')

# ## Keep line styles consistent
handles, labels = plot_real.get_legend_handles_labels()

for i, tool in enumerate(labels):
    for ln in (plot_real.lines[i], handles[i]):
        ln.set_color(styles[tool].get_color())
        ln.set_linewidth(styles[tool].get_linewidth())
        ln.set_linestyle(linestyles.get(tool, '-'))
        ln.set_marker(styles[tool].get_marker())

## Sort legend alphabetically
zipped = sorted(zip(handles, labels), key=lambda x: x[1])
handles, labels = zip(*zipped)

plot_real.legend(handles, labels, ncols=1)

plot_real.set_title(f"Realisability{' (excl. novel LTL instances)' if exclude_full_ltl else ''}")
plot_real.set(xlabel="Instances solved")
plot_real.set(ylabel="Cumulative time (s)")


fig = plot_real.get_figure()
fig.tight_layout()
fig.savefig(f"cactus-real.{FORMAT}", dpi=300)

## Synthesis results
fig.clear()

stacked_syn = (
    stacked
    .filter(pl.col("tool").str.contains("synthesis")))

plot_syn = sns.lineplot(
    data=stacked_syn.to_pandas(), 
    x="instances", y="time",
    hue="tool", style="tool",
    **lineplot_config)

# plot_syn.set_ylim(top=5000)
plot_syn.figure.set_size_inches(4.6, 4.6)
# # plot_syn.set(yscale='log')

# # Keep line styles consistent
handles, labels = plot_syn.get_legend_handles_labels()
for i, tool in enumerate(labels):
    for ln in (plot_syn.lines[i], handles[i]):
        ln.set_color(styles[tool].get_color())
        ln.set_linewidth(styles[tool].get_linewidth())
        ln.set_linestyle(linestyles.get(tool, '-'))
        ln.set_marker(styles[tool].get_marker())
labels = [x.replace(" (realisability)", "").replace(" (synthesis)", "") for x in labels]
# # Sort legend alphabetically
zipped = sorted(zip(handles, labels), key=lambda x: x[1])
handles, labels = zip(*zipped)
plot_syn.legend(handles, labels, ncols=2)

plot_syn.set_title(f"Synthesis{' (excl. novel LTL instances)' if exclude_full_ltl else ''}")
plot_syn.set(xlabel="Instances solved")
plot_syn.set(ylabel="Cumulative time (s)")

fig = plot_syn.get_figure()
fig.tight_layout()
fig.savefig(f"cactus-syn.{FORMAT}", dpi=300)


# Speedup
withbin = (
    pl.scan_csv(FILENAME)
    .select("benchmark", "sweap-noacc", "sweap-nobin")
    .filter(pl.col("benchmark").is_not_null()))

speedups_lazy = (
    withbin
    .filter(pl.col("sweap-noacc") > 1).filter(pl.col("sweap-noacc") < TIMEOUT)
    .filter(pl.col("sweap-nobin") > 1).filter(pl.col("sweap-nobin") < TIMEOUT)
    .with_columns(
        (pl.col("sweap-noacc")/1000).alias("Lazy, with efficient encoding (s)"),
        (pl.col("sweap-nobin")/1000).alias("Lazy, baseline (s)"),
        (pl.col("sweap-nobin") / pl.col("sweap-noacc")).alias("speedup"))
    )

print(speedups_lazy.select("speedup").max().collect())
print(speedups_lazy.select("speedup").min().collect())
print(speedups_lazy.select("speedup").mean().collect())
fig.clear()
scatter = sns.scatterplot(
    data=speedups_lazy.collect().to_pandas(),\
    x="Lazy, with efficient encoding (s)", y="Lazy, baseline (s)")
xmax=150
ln = sns.lineplot(x=[1,xmax], y=[1,xmax], ax=scatter)
ln.lines[0].set_linewidth(1)
ln.lines[0].set_color('r')
scatter.set_xbound(lower=1, upper=xmax)
scatter.set_ybound(lower=1, upper=xmax)
scatter.set(yscale='log')
scatter.set(xscale='log')
scatter.figure.savefig("speedup.pdf", dpi=300)
