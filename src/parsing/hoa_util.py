from parsing.string_to_prop_logic import string_to_prop


def parse_raw_cond(arg):
    to_replace, orig_cond = arg
    raw_cond = orig_cond.replace("t", "true")
    raw_cond = raw_cond.replace("f", "false")  # probably we don't need this
    cond = string_to_prop(raw_cond, True)
    cond = cond.replace_vars(to_replace)
    env_cond = cond.left
    con_cond = cond.right
    return orig_cond, env_cond, con_cond
