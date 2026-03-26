"""ISSY optimisation-summary bookkeeping helpers."""

_LAST_OPTIMISATION_SUMMARY = None


def new_optimisation_summary(spec_name: str) -> dict:
    return {"spec": spec_name, "events": []}


def record_optimisation(
    summary: dict | None,
    stage: str,
    kind: str,
    count: int,
):
    if summary is None:
        return
    if count <= 0:
        return
    summary["events"].append(
        {
            "stage": stage,
            "kind": kind,
            "count": int(count),
        }
    )


def record_optimisation_detail(
    summary: dict | None,
    stage: str,
    kind: str,
    detail: str,
):
    if summary is None:
        return
    details = summary.setdefault("details", [])
    details.append(
        {
            "stage": stage,
            "kind": kind,
            "detail": detail,
        }
    )


def _finalise_optimisation_summary(summary: dict | None) -> dict | None:
    if summary is None:
        return None
    totals_by_stage = {}
    totals_by_kind = {}
    for event in summary["events"]:
        stage = event["stage"]
        kind = event["kind"]
        count = int(event["count"])
        totals_by_stage[stage] = totals_by_stage.get(stage, 0) + count
        totals_by_kind[kind] = totals_by_kind.get(kind, 0) + count
    return {
        "spec": summary["spec"],
        "events": list(summary["events"]),
        "totals_by_stage": totals_by_stage,
        "totals_by_kind": totals_by_kind,
        "total_events": len(summary["events"]),
    }


def set_last_optimisation_summary(summary: dict | None):
    global _LAST_OPTIMISATION_SUMMARY
    _LAST_OPTIMISATION_SUMMARY = _finalise_optimisation_summary(summary)


def get_last_optimisation_summary() -> dict | None:
    if _LAST_OPTIMISATION_SUMMARY is None:
        return None
    return {
        "spec": _LAST_OPTIMISATION_SUMMARY["spec"],
        "events": [dict(e) for e in _LAST_OPTIMISATION_SUMMARY["events"]],
        "totals_by_stage": dict(_LAST_OPTIMISATION_SUMMARY["totals_by_stage"]),
        "totals_by_kind": dict(_LAST_OPTIMISATION_SUMMARY["totals_by_kind"]),
        "total_events": _LAST_OPTIMISATION_SUMMARY["total_events"],
    }


def reset_last_optimisation_summary():
    global _LAST_OPTIMISATION_SUMMARY
    _LAST_OPTIMISATION_SUMMARY = None
