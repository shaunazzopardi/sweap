from prop_lang.types.ops_and_rels import StringableEnum


class BoolAtoms(StringableEnum):
    TRUE = ("TRUE",)
    FALSE = ("FALSE",)


def parse_bool_atoms(bool_atoms_str: str) -> BoolAtoms:
    if bool_atoms_str.lower() in ["true", "tt"]:
        return BoolAtoms.TRUE
    elif bool_atoms_str.lower() in ["false", "ff"]:
        return BoolAtoms.FALSE
    else:
        raise Exception(
            bool_atoms_str
            + " is not a valid boolean value. Valid boolean values are `true'/`tt', or `false'/`ff' (capitilisation ignored)."
        )


natural_val_regex = "[0-9]+"
