import re

regex_keywords = list(
    map(
        re.compile,
        [
            r"turn$",
            r"true$",
            r"false$",
            r"in_loop[0-9]+_[0-9]+",
            r"prog$",
            r"cs$",
            r"pred_.*",
            r"bin_.*",
            r"mismatch$",
            r"compatible_.*",
            r"guard_.*",
            r"act_.*",
            r"identity_.*",
            r"counterstrategy_guard_.*",
            r"counterstrategy_act_.*",
            r"floor$",
            r"keep$",
            r"eq_con_.*",
            r"sat_con_.*",
            r"minigame_event_.*",
            r"env_lose$",
            r"lose$",
        ],
    )
)


def is_keyword(s: str):
    for k in list(regex_keywords):
        if k.match(s):
            raise Exception(
                "'"
                + s
                + "'"
                + " matches a reserved keyword/pattern "
                + str(k).replace("re.compile", "")
                + ", rename."
            )
