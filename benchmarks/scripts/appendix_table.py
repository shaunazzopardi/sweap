#!/usr/bin/env python3
from subprocess import check_output, CalledProcessError
import csv
import glob
import sys
import re
from pathlib import Path


writer = csv.writer(sys.stdout)
prefix = re.compile(r"out-sweap(-noacc)?-+")

skip = (
    "solitary", "infinite-race", "chain-simple-param-70",
    "robot-collect-samples-v4",
    *(f"{b}-paper-{n}" for n in (5, 10, 50) for b in ("arbiter", "elevator")),
    *(f"arbiter-paper-unreal-{n}" for n in (5, 10, 50)),
    *(f"bloem-elevator-{t}-{n}" for n in (3, 5, 10, 50) for t in ("simple", "signal")),
    *(f"robot-grid-reach-{d}d-{n}" for n in (3, 5, 10, 50) for d in (1, 2)),
    *(f"reversible-lane-{r}-{n}" for n in (3, 5, 10, 50) for r in ("r", "u")),
)
rename = {
    "robot-grid-reach-repeated-with-obstacles-1d": "rep-reach-obst.-1d",
    "robot-grid-reach-repeated-with-obstacles-2d": "rep-reach-obst.-2d"
}

def process(fname, row_id):
    bench_name = Path(fname).stem.partition('.')[0]
    bench_name = re.sub(prefix, "", bench_name)
    bench_name = bench_name.replace("_", "-")
    bench_name = rename.get(bench_name, bench_name)
    if bench_name in skip:
        return False
    def shell(cmd):
        return check_output(cmd, shell=True, encoding="utf-8")
    def handle_predicates_line(line):
        preds = (
            line.
            strip().
            replace("adding ", "").
            replace(" to predicate abstraction", "").
            split(", "))
        preds = [p for p in preds if p]
        tr = sum(1 for p in preds if "_prev" in p)
        st = len(preds) - tr
        return st, tr

    init_preds = shell(
        f"""grep -A1 "Starting abstract synthesis loop." {fname} | tail -n1""")
    init_st, init_tr = handle_predicates_line(init_preds)


    try:
        all_pred_lines = shell(f"""grep "^adding" {fname}""").split("\n")
        all_pred_lines = [handle_predicates_line(x) for x in all_pred_lines if x]
    except CalledProcessError:
        all_pred_lines = []
    add_st, add_tr = 0, 0
    count_fair_ref, count_safe_ref = 0, 0
    if len(all_pred_lines):
        all_st, all_tr = zip(*all_pred_lines)
        add_st, add_tr = sum(all_st) - init_st, sum(all_tr) - init_tr

        count_fair_ref = shell(
            f"""grep "Structural Refinement" {fname} | wc -l""").strip()
        count_safe_ref = shell(
            f"""grep "safety refinement" {fname} | wc -l""").strip()
    

    writer.writerow([
        row_id, bench_name,
        init_st, init_tr, count_fair_ref, count_safe_ref, add_st, add_tr])
    return True


if __name__ == "__main__":
    header = [
        "row-id",
        "bench name (sweap_acc)", "init st", "init tr", 
        "liveness refinements", "safety refinements",
        "added st", "added tr"]

    logs_dir = Path(sys.argv[1])
    logs_sweap = [Path(x).resolve() for x in logs_dir.glob("out-sweap--*.log")]
    logs_sweap_noacc = [Path(x).resolve() for x in logs_dir.glob("out-sweap-noacc*.log")]
    writer.writerow(header)
    i = 2
    for log in sorted(logs_sweap_noacc):
        ok = process(log, i)
        if ok:
            i += 1
    print("-"*30)
    header[1] = "bench name (sweap_no-acc)"
    writer.writerow(header)
    i = 2
    for log in sorted(logs_sweap_noacc):
        ok = process(log, i)
        if ok:
            i += 1
