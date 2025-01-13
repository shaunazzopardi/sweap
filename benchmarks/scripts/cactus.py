#!/usr/bin/env python3
import polars as pl
import seaborn as sns

TIMEOUT = 1200000
FILENAME = "infinitestate-stela.csv"
# sns.set_theme("notebook")


tools = [
    name
    for name in pl.scan_csv(FILENAME).columns
    if name not in ("row-id", "benchmark")]

legend = {
    "sweap": "Our tool (synthesis)",
    "sweap-noacc": "Our tool, lazy (synthesis)",
    "raboniel": "Raboniel (synthesis)",
    "temos": "Temos (synthesis)",
    "rpgsolve": "Rpgsolve (realizability)",
    "rpgsolve-syn": "Rpgsolve (synthesis)",
    "rpg-stela": "Rpg-stela (realizability)",
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


real_df = (
    joined
    .drop(*(legend[x] for x in ("raboniel", "temos", "rpgsolve-syn"))))
real_df = real_df.rename({
        x: x.replace(" (realizability)", "")
        for x in real_df.columns})


plot = sns.lineplot(
    data=real_df.drop("instances").to_pandas(),
    markers=True, markeredgecolor=None, markeredgewidth=1, markersize=5,
    )
plot.get_legend().set_title("Realizability")
plot.set(xlabel="Instances solved")
plot.set(ylabel="Time (s)")
fig = plot.get_figure()
fig.tight_layout()
fig.savefig("cactus-real.png", dpi=300)

## Synthesis results
fig.clear()

syn_df = (
    joined
    .drop(*(legend[x] for x in ("rpg-stela", "rpgsolve")))
    .rename({
        x: x.replace(" (synthesis)", "")
        for x in joined.columns}))

plot_syn = sns.lineplot(
    data=syn_df.drop("instances").to_pandas(),
    markers=True, markeredgecolor=None, markeredgewidth=1, markersize=5)
plot_syn.get_legend().set_title("Synthesis")
plot_syn.set(xlabel="Instances solved")
plot_syn.set(ylabel="Time (s)")
fig = plot_syn.get_figure()
fig.tight_layout()
fig.savefig("cactus-syn.png", dpi=300)


fig.clear()
easy_df = joined.limit(20)

plot_easy = sns.lineplot(
    data=easy_df.drop("instances").to_pandas(),
    markers=True, markeredgecolor=None, markeredgewidth=1, markersize=5)
plot_easy.set(xlabel="Instances solved")
plot_easy.set(ylabel="Time (s)")
plot_easy.set(yscale='log')
plot_easy.set(xticks=[1,5,10,15,20])
fig = plot_easy.get_figure()
fig.tight_layout()
fig.savefig("cactus-easy.png", dpi=300)



# fig = plot.get_figure()
# fig.tight_layout()
# fig.savefig("cactus-log.png", dpi=300)