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
    "raboniel": "Raboniel",
    "temos": "Temos",
    "rpgsolve": "Rpgsolve",
    "rpgsolve-syn": "Rpgsolve (synthesis)",
    "rpg-stela": "Rpg-stela",
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
    # zero = (
    #     pl.DataFrame({"instances": [0], col_name: [0]})
    #     .cast({"instances": pl.UInt32, col_name: pl.Int64}))
    # return pl.concat([zero, df])
    return df

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


real_df = joined.drop(*(legend[x] for x in ("raboniel", "temos", "rpgsolve-syn")))
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
fig_syn = plot_syn.get_figure()
fig_syn.tight_layout()
fig_syn.savefig("cactus-syn.png", dpi=300)



# plot.set(yscale='log')
# fig = plot.get_figure()
# fig.tight_layout()
# fig.savefig("cactus-log.png", dpi=300)