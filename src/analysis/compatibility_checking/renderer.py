from __future__ import annotations

from analysis.compatibility_checking.types import StructuredNuXmvModel, VarDecl


def _render_var_decl(decl: VarDecl) -> str:
    return f"{decl.name} : {decl.typ}"


def _indent_multiline(text: str) -> str:
    return text.replace("\n", "\n\t")


def _render_decl_block(header: str, lines: list[str]) -> str:
    if not lines:
        return f"{header}\n"
    return header + "\n" + "".join(f"\t{_indent_multiline(line)};\n" for line in lines)


def _render_conj_block(header: str, terms: list[str]) -> str:
    if not terms:
        return f"{header}\n\tTRUE\n"
    lines = [header]
    for i, term in enumerate(terms):
        prefix = "\t(" if i == 0 else "\t& ("
        lines.append(prefix + _indent_multiline(term) + ")")
    return "\n".join(lines) + "\n"


def _post_process_nuxmv(text: str) -> str:
    return (
        text.replace("%", "mod")
        .replace("&&", "&")
        .replace("||", "|")
        .replace("==", "=")
    )


def post_process_nuxmv(text: str) -> str:
    return _post_process_nuxmv(text)


def render_structured_model(
    model: StructuredNuXmvModel, include_turn: bool = True
) -> str:
    vars_to_render = [
        decl
        for decl in model.vars
        if include_turn or not (decl.name == "turn" and decl.typ.startswith("{"))
    ]
    text = f"MODULE {model.name}\n"
    text += _render_decl_block("VAR", [_render_var_decl(v) for v in vars_to_render])
    text += _render_decl_block("DEFINE", [str(d) for d in model.define])
    text += _render_conj_block("INIT", [str(i) for i in model.init])
    text += _render_conj_block("INVAR", [str(i) for i in model.invar])
    text += _render_conj_block("TRANS", [str(t) for t in model.trans])
    return _post_process_nuxmv(text)
