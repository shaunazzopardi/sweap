#!/usr/bin/env python3
import sys

import polars as pl
import seaborn as sns
import matplotlib as mpl
import matplotlib.pyplot as plt

mpl.rc("font", family="serif", size=11)

FORMAT = "pdf"
TIMEOUT = 1200000


# def export_legend(ax, ncols=10, filename="legend.pdf"):
#     # https://stackoverflow.com/a/62013436
#     fig2 = plt.figure()
#     ax2 = fig2.add_subplot()
#     ax2.axis('off')
#     legend = ax2.legend(
#         *ax.get_legend_handles_labels(), frameon=False, 
#         loc='lower center', ncol=10)
#     fig  = legend.figure
#     fig.canvas.draw()
#     bbox  = legend.get_window_extent().transformed(fig.dpi_scale_trans.inverted())
#     fig.savefig(filename, dpi="figure", bbox_inches=bbox)

if len(sys.argv) < 2:
    print("Usage: ./cactus.py <file.csv>")
    sys.exit(1)
FILENAME = sys.argv[1]

exclude_full_ltl = True
lineplot_config = dict(markers="osdPso^XX", markersize=5)


tools = [
    name
    for name in pl.scan_csv(FILENAME).columns
    if name not in ("row-id", "benchmark", "temos")]

legend = {
    "sweap": "Our tool (synthesis)",
    "sweap-noacc": "Our tool, lazy (synthesis)",
    "raboniel": "Raboniel (synthesis)",
    "rpgsolve-syn": "Rpgsolve (synthesis)",
    # "temos": "Temos (synthesis)",
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

full_ltl_benchs = (
    "arbiter",
    "arbiter-failure",
    "arbiter-unreal",
    "elevator",
    "reversible-lane-r",
    "reversible-lane-u",
    "rep-reach-obst-1d",
    "rep-reach-obst-2d",
    "robot_collect_v4",
    "taxi-service"
) if exclude_full_ltl else tuple()


def cum_sum(tool_name: str):
    # col_name = tool_name
    col_name = legend.get(tool_name, tool_name)
    q = (
        pl.scan_csv(FILENAME)
        .filter(pl.col(tool_name) > 1)
        .filter(pl.col(tool_name) < TIMEOUT)
        .filter(pl.col("benchmark").is_in(full_ltl_benchs).not_())
        .sort(by=tool_name)
        .with_row_index("instances", 1)
        .select(instances=pl.col("instances"), **{col_name: pl.cum_sum(tool_name)/1000})
    )
    df = q.collect()
    zero = (
        pl.DataFrame({"instances": [0], col_name: [None]})
        .cast({"instances": pl.UInt32, col_name: pl.Float64}))
    return pl.concat([zero, df])

dataframes = [cum_sum(x) for x in tools]
joined = dataframes[0]
for df in dataframes[1:]:
    df1, df2 = (
        (joined, df)
        if len(df["instances"]) <= len(joined["instances"])
        else (df, joined))
    joined = (
        df1
        .join(df2, on="instances", how="full").drop("instances_right"))

print(joined)

## Easiest 20 instances
easy_df = joined.limit(20)
plot_easy = sns.lineplot(
    data=easy_df.drop("instances").to_pandas(),
    **lineplot_config)

plot_easy.set_ylim(bottom=0.5E-2)

# Some black magic to sort & add headers to our legend
dummy = mpl.lines.Line2D([], [], color="none")
handles, labels = plot_easy.get_legend_handles_labels()

# Force linestyles
for i, tool in enumerate(easy_df.drop("instances").columns):
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
plot_easy.set(ylabel="Time (s)")
plot_easy.set(yscale='log')
plot_easy.set(xticks=[1,5,10,15,20])


fig = plot_easy.get_figure()
fig.tight_layout()
fig.savefig(f"cactus-easy.{FORMAT}", dpi=300)
fig.clear()


real_df = (
    joined
    .drop(*(
        name for name in legend.values()
        if name in joined.columns and 
        "(realisability)" not in name and
        "Our tool" not in name)))


plot_real = sns.lineplot(
    data=real_df.drop("instances").to_pandas(),
    **lineplot_config)
plot_real.set_ylim(top=11_000)

## Keep line styles consistent
handles, labels = plot_real.get_legend_handles_labels()

for i, tool in enumerate(real_df.drop("instances").columns):
    for ln in (plot_real.lines[i], handles[i]):
        ln.set_color(styles[tool].get_color())
        ln.set_linewidth(styles[tool].get_linewidth())
        ln.set_linestyle(linestyles.get(tool, '-'))
        ln.set_marker(styles[tool].get_marker())

## Sort legend alphabetically
zipped = sorted(zip(handles, labels), key=lambda x: x[1])
handles, labels = zip(*zipped)

plot_real.legend(handles, labels, ncols=2)

plot_real.set_title(f"Realisability{' (excl. novel LTL instances)' if exclude_full_ltl else ''}")
plot_real.set(xlabel="Instances solved")
plot_real.set(ylabel="Time (s)")


fig = plot_real.get_figure()
fig.tight_layout()
fig.savefig(f"cactus-real.{FORMAT}", dpi=300)

## Synthesis results
fig.clear()

syn_df = (
    joined.drop(*(name for name in legend.values() if "(synthesis)" not in name)))

plot_syn = sns.lineplot(data=syn_df.drop("instances").to_pandas(), **lineplot_config)



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
plot_syn.set(ylabel="Time (s)")

fig = plot_syn.get_figure()
fig.tight_layout()
fig.savefig(f"cactus-syn.{FORMAT}", dpi=300)
