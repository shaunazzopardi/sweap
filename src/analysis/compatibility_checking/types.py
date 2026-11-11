from __future__ import annotations

from dataclasses import dataclass, field


@dataclass(frozen=True)
class VarDecl:
    name: str
    typ: str


@dataclass(frozen=True)
class CompatOptions:
    dual: bool = False


@dataclass
class StructuredNuXmvModel:
    name: str
    vars: list[VarDecl] = field(default_factory=list)
    define: list[str] = field(default_factory=list)
    init: list[str] = field(default_factory=list)
    invar: list[str] = field(default_factory=list)
    trans: list[str] = field(default_factory=list)
