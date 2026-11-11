#!/usr/bin/env python3
import sys
from pathlib import Path


import polars as pl
import polars.selectors as cs
from great_tables import loc, style

csv = pl.read_csv(sys.argv[1]).with_columns(
    (pl.col("time(ms)") / 1000).alias("time(s)")
)

solved = csv.filter(
    pl.col("real") & (pl.col("verdict") == "realizable")
    |
    ~pl.col("real") & (pl.col("verdict") == "unrealizable")
)

print(solved, file=sys.stderr)

# Get all values in tools column
tools = solved["tool"].unique().to_list()
benchs = solved["benchmark"].unique().to_list()
print("Tools in the log:", tools, file=sys.stderr)


num_solved = {t: solved.filter(pl.col("tool") == t).height for t in tools}
print(num_solved, file=sys.stderr)


def best_and_unique(solved_df, tools_list, benchs_list):
    num_best = {t: 0 for t in tools_list}
    num_unique = {t: 0 for t in tools_list}

    # find best tool for each benchmark
    for b in benchs_list:
        best_time = float('inf')
        best_tool = None
        hits = 0
        for t in tools_list:
            entry = solved_df.filter((pl.col("tool") == t) & (pl.col("benchmark") == b))
            if entry.height == 1:
                hits += 1
                time = entry[0, "time(s)"]
                if time < best_time:
                    best_time = time
                    best_tool = t
        if best_tool is not None:
            num_best[best_tool] += 1
            if hits == 1:
                num_unique[best_tool] += 1
    return num_best, num_unique

tools_map = {
    "tsl": ["issy2-tsl", "sweap-tsl-pf"],
    "rpg": ["issy2-rpg", "sweap-rpg-pf"],
    "issy": ["issy2", "sweap-issy-pf"],
    "prog": ["sweap-strix", "sweap-pf"]
}

def name_fmt(tool):
    if "issy" in tool and "sweap" not in tool:
        return "Issy"
    elif "strix" in tool:
        return "\\SweapStrix"
    else:
        return "\\sweap"

def get_benchs(formats, tool1, tool2):
    data = {f: [] for f in formats}
    for fmt in formats:
        fmt_tools = tools_map[fmt]
        solved_fmt = solved.filter(pl.col("tool").is_in(fmt_tools))
        fmt_benchs = solved_fmt["benchmark"].unique().to_list()
        
        solved_r = solved_fmt.filter(pl.col("real") & (pl.col("verdict") == "realizable"))
        solved_u = solved_fmt.filter(~pl.col("real") & (pl.col("verdict") == "unrealizable"))

        num_solved_r = {t: solved_r.filter(pl.col("tool") == t).height for t in fmt_tools}
        num_solved_u = {t: solved_u.filter(pl.col("tool") == t).height for t in fmt_tools}

        best_fmt_r, unique_fmt_r = best_and_unique(solved_r, fmt_tools, fmt_benchs)
        best_fmt_u, unique_fmt_u = best_and_unique(solved_u, fmt_tools, fmt_benchs)
        
        data[fmt] = (fmt_tools, num_solved_r, num_solved_u, best_fmt_r, unique_fmt_r, best_fmt_u, unique_fmt_u)
    
    all_benchs = {fmt: csv.filter(pl.col("tool").is_in(tools_map[fmt]))["benchmark"].unique().count() for fmt in formats}

    df = pl.DataFrame([
    x
    for fmt, (fmt_tools, num_solved_r, num_solved_u, best_fmt_r, unique_fmt_r, best_fmt_u, unique_fmt_u) in data.items()
    for tool in fmt_tools
    for x in (
        [f"{fmt.upper()} (R)", name_fmt(tool), num_solved_r[tool], best_fmt_r[tool], unique_fmt_r[tool]], 
        [f"{fmt.upper()} (U)", name_fmt(tool), num_solved_u[tool], best_fmt_u[tool], unique_fmt_u[tool]])
    ],
    schema=["Format (total)", "Tool", "Solved", "Fastest", "Unique"]
    )
    tbl = df.to_pandas().to_latex(index=False)
    
    # .pivot(on="Tool", values=["Solved", "Fastest", "Unique"]).select([
    #     "Format (total)",
    #     cs.contains("Issy"),
    #     cs.contains("\\SweapStrix"),
    #     (~cs.contains("Strix") & cs.contains("\\sweap"))])

    
    # latex_table = df.to_pandas().to_latex(
    #     index=False,
    #     header=[fr"\textbf[[{x}]]" for x in df.schema.names()],
    #     bold_rows=True).replace("[[", "{").replace("]]", "}")

    # issy_columns = [i for i, name in enumerate(df.schema.names()) if name.endswith(tool1)]
    # sweap_columns = [i for i, name in enumerate(df.schema.names()) if name.endswith(tool2)]
    # columns = [*issy_columns, *sweap_columns]

    # lbl_issy = rf"\multicolumn{{{max(issy_columns) - min(issy_columns) + 1}}}{{c}}{{\textbf{{{tool1}}}}}"
    # lbl_sweap = rf"\multicolumn{{{max(sweap_columns) - min(sweap_columns) + 1}}}{{c}}{{\textbf{{{tool2}}}}}"
    # x = ""
    # for i in range(1, len(df.schema.names())):
    #     if i not in columns:
    #         x += " & "
    #     elif i == min(issy_columns):
    #         x += " & " + lbl_issy
    #     elif i == min(sweap_columns):
    #         x += " & " + lbl_sweap

    # latex_table = (
    #     latex_table
    #     .replace("toprule", f"toprule\n{x}\\\\")
    #     .replace("_Issy", "").replace("_\\SweapStrix", "")
    #     .replace("_\\sweap", ""))

    # header_ends = latex_table.index("\\midrule\n") + len("\\midrule\n")
    # body_ends = latex_table.index("\\bottomrule")

    # body = [ln.split("&") for ln in latex_table[header_ends:body_ends].splitlines()]
    # body = [ [col.replace("\\", "").strip() for col in ln] for ln in body]

    # for i, ln in enumerate(body):
    #     for j in (1, 2, 3):
    #         if int(ln[j]) > int(ln[j + 3]):
    #             body[i][j] = rf"\textbf{{{body[i][j].strip()}}}"
    #         elif int(ln[j]) < int(ln[j + 3]):
    #             body[i][j + 3] = rf"\textbf{{{body[i][j + 3].strip()}}} "
    #     body[i] = " & ".join(body[i]) + r" \\"

    # tbl = latex_table[:header_ends] + "\n".join(body) + latex_table[body_ends:]



    return data, df, tbl

formats = ["tsl", "rpg", "issy"]
data, df, tbl = get_benchs(formats, "Issy", "\\sweap")
print(tbl)

data, df, tbl = get_benchs(["prog"], "\\SweapStrix", "\\sweap")
print(tbl)
