#!/usr/bin/env python3
from subprocess import check_output
import csv
import glob
import sys
import re
from pathlib import Path


writer = csv.writer(sys.stdout)
prefix = re.compile(r"out-sweap(-noacc)?-+")

def process(fname, row_id):
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

    bench_name = Path(fname).stem.partition('.')[0]
    bench_name = re.sub(prefix, "", bench_name)

    all_pred_lines = shell(f"""grep "^adding" {fname}""").split("\n")
    all_pred_lines = [handle_predicates_line(x) for x in all_pred_lines if x]
    add_st, add_tr = 0, 0
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


if __name__ == "__main__":
    header = [
        "row-id",
        "bench name (sweap_acc)", "init st", "init tr", 
        "liveness refinements", "safety refinements",
        "added st", "added tr"]

    logs_sweap = [Path(x).resolve() for x in glob.glob("logs/out-sweap--*.log")]
    logs_sweap_noacc = [Path(x).resolve() for x in glob.glob("logs/out-sweap-noacc*.log")]
    writer.writerow(header)
    for i, log in enumerate(sorted(logs_sweap), start=2):
        process(log, i)
    print("-"*30)
    header[1] = "bench name (sweap_no-acc)"
    writer.writerow(header)
    for i, log in enumerate(sorted(logs_sweap_noacc), start=2):
        process(log, i)
