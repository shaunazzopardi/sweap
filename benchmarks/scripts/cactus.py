#!/usr/bin/env python3
import polars as pl
import seaborn as sns
import matplotlib as mpl
from itertools import cycle

TIMEOUT = 1200000
FILENAME = "../../newnew.csv"
# FILENAME = "infinitestate-stela.csv"
# sns.set_theme("notebook")


tools = [
    name
    for name in pl.scan_csv(FILENAME).columns
    if name not in ("row-id", "benchmark")]

legend = {
    "sweap": "Our tool (synthesis)",
    "sweap-noacc": "Our tool, lazy (synthesis)",
    "raboniel": "Raboniel (synthesis)",
    "rpgsolve-syn": "Rpgsolve (synthesis)",
    "temos": "Temos (synthesis)",
    "rpg-stela": "Rpg-stela (realisability)",
    "rpgsolve": "Rpgsolve (realisability)",
    "tslmt2rpg": "tslmt2rpg (realisability)"
}

def cum_sum(tool_name: str):
    # col_name = tool_name
    col_name = legend.get(tool_name, tool_name)
    q = (
        pl.scan_csv(FILENAME)
        .filter(pl.col(tool_name) > 2)
        .filter(pl.col(tool_name) < TIMEOUT)
        .sort(by=tool_name)
        .with_row_index("instances", 1)
        .select(instances=pl.col("instances"), **{col_name: pl.cum_sum(tool_name)/1000})
    )
    df = q.collect()
    zero = (
        pl.DataFrame({"instances": [0], col_name: [None]})
        .cast({"instances": pl.UInt32, col_name: pl.Float64}))
    return pl.concat([zero, df])
    # return df

# def remove_right(df: pl.DataFrame):
#     return {
#         x: x[:-6]
#         for x in df.columns
#         if x[-6:] == "_right"}


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
    markers=True, markeredgecolor=None, markeredgewidth=1, markersize=5)

# for ln, style in zip(plot_easy.lines, [x["line"] for x in style.values()]):
#     ln.set_linestyle(style)
# plot_easy.legend()

# Some black magic to sort & add headers to our legend
dummy = mpl.lines.Line2D([], [], color="none")
handles, labels = plot_easy.get_legend_handles_labels()
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

handles.insert(6, dummy)
labels.insert(6, "")
handles.insert(6, dummy)
labels.insert(6, "$\\bf{Realisability}$")

plot_easy.legend(handles, labels, ncol=2)





plot_easy.set_title("Behaviour on first 20 solved instances")
plot_easy.set(xlabel="Instances solved")
plot_easy.set(ylabel="Time (s)")
plot_easy.set(yscale='log')
plot_easy.set(xticks=[1,5,10,15,20])


fig = plot_easy.get_figure()
fig.tight_layout()
fig.savefig("cactus-easy.png", dpi=300)

fig.clear()

real_df = (
    joined
    .drop(*(name for name in legend.values() if "(realisability)" not in name and "Our tool" not in name)))


plot_real = sns.lineplot(
    data=real_df.drop("instances").to_pandas(),
    markers=True, markeredgecolor=None, markeredgewidth=1, markersize=5)

# Keep line styles consistent
handles, labels = plot_real.get_legend_handles_labels()

linestyles = {
    legend["sweap"]: "-",
    legend["sweap-noacc"]: "--",
    legend["raboniel"]: ":",
    legend["temos"]: "-.",
    legend["rpgsolve"]: "--",
    legend["rpgsolve-syn"]: "-",
    legend["rpg-stela"]: "-.",
    legend["tslmt2rpg"]: "-."
}
for i, tool in enumerate(real_df.drop("instances").columns):
    for ln in (plot_real.lines[i], handles[i]):
        ln.set_color(styles[tool].get_color())
        ln.set_linestyle(linestyles[tool])
        ln.set_marker(styles[tool].get_marker())
# labels = [x.replace(" (realisability)", "") for x in labels]

# Sort legend alphabetically
zipped = sorted(zip(handles, labels), key=lambda x: x[1])
handles, labels = zip(*zipped)

plot_real.legend(handles, labels)



plot_real.set_title("Realisability")
plot_real.set(xlabel="Instances solved")
plot_real.set(ylabel="Time (s)")


fig = plot_real.get_figure()
fig.tight_layout()
fig.savefig("cactus-real.png", dpi=300)

## Synthesis results
fig.clear()

syn_df = (
    joined
    .drop(*(name for name in legend.values() if "(synthesis)" not in name)))

plot_syn = sns.lineplot(
    data=syn_df.drop("instances").to_pandas(),
    markers=True, markeredgecolor=None, markeredgewidth=1, markersize=5)
plot_syn.set_title("Synthesis")
plot_syn.set(xlabel="Instances solved")
plot_syn.set(ylabel="Time (s)")


# Keep line styles consistent
handles, labels = plot_syn.get_legend_handles_labels()
for i, tool in enumerate(syn_df.drop("instances").columns):
    for ln in (plot_syn.lines[i], handles[i]):
        ln.set_color(styles[tool].get_color())
        ln.set_linestyle(linestyles[tool])
        # ln.set_linestyle(styles[tool].get_linestyle())
        ln.set_marker(styles[tool].get_marker())
labels = [x.replace(" (realisability)", "").replace(" (synthesis)", "") for x in labels]
# Sort legend alphabetically
zipped = sorted(zip(handles, labels), key=lambda x: x[1])
handles, labels = zip(*zipped)
plot_syn.legend(handles, labels)

fig = plot_syn.get_figure()
fig.tight_layout()
fig.savefig("cactus-syn.png", dpi=300)





# fig = plot.get_figure()
# fig.tight_layout()
# fig.savefig("cactus-log.png", dpi=300)