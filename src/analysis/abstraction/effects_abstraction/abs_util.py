from analysis.abstraction.effects_abstraction.predicates.Predicate import Predicate
from prop_lang.util import atomic_predicates


def relevant_vars(g, us):
    preds_in_g = atomic_predicates(g)
    vars_g = set(v for p in preds_in_g for v in p.variablesin())

    vars_u_now = set()
    vars_u_next = set()
    for u in us:
        if u.left != u.right:
            vars_u_now.update(u.right.variablesin())
            vars_u_next.add(u.left)

    return vars_g, vars_u_now, vars_u_next


def partition_preds(preds, all_vars):
    v_to_p = {v: set() for v in all_vars}
    p_to_vs = {p: set() for p in preds}
    for p in preds:
        vars_p = p.variablesin()
        p_to_vs[p] = vars_p
        for v in vars_p:
            v_to_p[v].add(p)

    partitions = []
    v_to_partition = {}

    curr_preds = list(preds)
    while len(curr_preds) > 0:
        p = curr_preds.pop()
        rel_vars = p_to_vs[p]
        done_vars = set()
        part = {p}
        while len(rel_vars) > 0:
            new_preds = set()
            new_vars = set()
            for v in rel_vars:
                if v in done_vars:
                    continue
                else:
                    v_to_partition = {len(partitions)}
                    done_vars.add(v)
                    for p in v_to_p[v]:
                        new_preds.add(p)
                        new_vars.update(p_to_vs[p])
            rel_vars = new_vars
            part.update(new_preds)
        curr_preds = [p for p in curr_preds if p not in part]
        partitions.append(part)

    return {i:p for i, p in enumerate(partitions)}, v_to_p, v_to_partition


def update_pred_partition(pred, partitions, v_to_p, v_to_partition):
    vars_in_pred = pred.variablesin()
    parts_to_merge = set()
    new_part = None
    new_vs = set()

    if len(v_to_partition.keys()) != 0:
        for v in vars_in_pred:
            if v in v_to_partition.keys():
                v_to_p[v].add(pred)
                i = v_to_partition[v]

                if new_part is None:
                    new_part = i
                else:
                    if i != new_part:
                        parts_to_merge.add(i)
                        v_to_partition[v] = i
            else:
                new_vs.add(v)
    else:
        new_vs = vars_in_pred

    if len(new_vs) > 0:
        if new_part is None:
            # TODO better indices? can have variable sets instead, we are assured those are unique
            if len(partitions.keys()) == 0:
                i = 0
            else:
                i = max(partitions.keys()) + 1
            partitions[i] = {pred}
            for v in new_vs:
                v_to_partition[v] = i
                v_to_p[v] = {pred}
        else:
            for v in new_vs:
                v_to_partition[v] = new_part
                v_to_p[v] = {pred}

    if len(parts_to_merge) != 0:
        partitions[new_part].add(pred)
        for i in parts_to_merge:
            partitions[new_part] |= partitions[i]
            del partitions[i]

    return partitions, v_to_p, v_to_partition, new_part, parts_to_merge

def update_var_partition_mult(preds, partitions, v_to_p, v_to_partition):
    for p in preds:
        partitions, v_to_p, v_to_partition, _, _ = update_var_partition(p, partitions, v_to_p, v_to_partition)
    return partitions, v_to_p, v_to_partition


def update_var_partition(pred: Predicate, partitions, v_to_p, v_to_partition):
    vars_in_pred = set(pred.vars)
    parts_to_merge = set()
    new_part = None
    new_vs = set()

    if len(v_to_partition.keys()) != 0:
        for v in vars_in_pred:
            if v in v_to_partition.keys():
                v_to_p[v].add(pred)
                i = v_to_partition[v]

                if new_part is None:
                    new_part = i
                else:
                    if i != new_part:
                        parts_to_merge.add(i)
                        v_to_partition[v] = i
            else:
                new_vs.add(v)
    else:
        new_vs = vars_in_pred

    if len(new_vs) > 0:
        if new_part is None:
            # TODO better indices? can have variable sets instead, we are assured those are unique
            if len(partitions.keys()) == 0:
                i = 0
            else:
                i = max(partitions.keys()) + 1
            partitions[i] = new_vs
            new_part = i
            for v in new_vs:
                v_to_partition[v] = i
                v_to_p[v] = {pred}
        else:
            for v in new_vs:
                v_to_partition[v] = new_part
                v_to_p[v] = {pred}

    if len(parts_to_merge) != 0:
        if new_part not in partitions.keys():
            print()
        partitions[new_part].update(vars_in_pred)
        for i in parts_to_merge:
            partitions[new_part] |= partitions[i]
            for v in partitions[new_part]:
                v_to_partition[v] = new_part
            del partitions[i]

    return partitions, v_to_p, v_to_partition, new_part, parts_to_merge


def relevant_preds_guard(vars_g, partitions, v_to_partition):
    parts = [i for v in vars_g for i in v_to_partition[v]]
    return {i: partitions[i] for i in parts} # in the abstraction, all of these can be computed separately


def relevant_preds_update(vars_u_now, vars_u_next, partitions, v_to_p, v_to_partition):
    parts_now = [i for v in vars_u_now for i in v_to_partition[v]]
    now = {i: partitions[i] for i in parts_now}
    next = {v: v_to_p[v] for v in vars_u_next}
    return now, parts_now, next
