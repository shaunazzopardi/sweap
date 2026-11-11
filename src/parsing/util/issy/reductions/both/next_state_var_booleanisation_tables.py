import logging

from prop_lang.formula import Formula


class IssyBooleanisationTableWriter:
    @staticmethod
    def _format_numeric_region(region: tuple[int | None, int | None]) -> str:
        lb, ub = region
        lb_txt = "-inf" if lb is None else str(lb)
        ub_txt = "+inf" if ub is None else str(ub)
        if lb is not None and ub is not None and lb == ub:
            return f"= {lb}"
        return f"[{lb_txt}, {ub_txt}]"

    @classmethod
    def _format_region_union(
        cls, regions: list[tuple[int | None, int | None]]
    ) -> str:
        return " U ".join(cls._format_numeric_region(r) for r in regions)

    @staticmethod
    def _emit_table(title: str, headers: tuple[str, ...], rows: list[tuple[str, ...]]):
        if len(rows) == 0:
            return

        widths = [len(h) for h in headers]
        for row in rows:
            for i, cell in enumerate(row):
                widths[i] = max(widths[i], len(cell))

        separator = "+-" + "-+-".join("-" * w for w in widths) + "-+"
        header_row = "| " + " | ".join(
            headers[i].ljust(widths[i]) for i in range(len(headers))
        ) + " |"
        lines = [separator, header_row, separator]

        for row in rows:
            lines.append(
                "| "
                + " | ".join(row[i].ljust(widths[i]) for i in range(len(headers)))
                + " |"
            )
        lines.append(separator)

        table = "\n".join(lines)
        print(title)
        print(table)
        logging.info(title + "\n" + table)

    @classmethod
    def emit_numeric_boolean_domain_mapping(
        cls,
        domain_rows: list[
            tuple[str, list[tuple[int | None, int | None]], Formula]
        ],
        standin_to_encoding: dict[Formula, Formula],
    ):
        rows: list[tuple[str, str, str]] = []
        for var_name, numeric_regions, enc in domain_rows:
            resolved_enc = standin_to_encoding.get(enc, enc)
            rows.append(
                (var_name, cls._format_region_union(numeric_regions), str(resolved_enc))
            )

        cls._emit_table(
            "ISSY numeric->boolean domain mapping:",
            ("numeric_var", "numeric_domain", "boolean_encoding"),
            rows,
        )

    @classmethod
    def emit_numeric_predicate_boolean_mapping(
        cls, predicate_to_encodings: dict[str, set[str]]
    ):
        rows: list[tuple[str, str]] = []
        for raw_pred in sorted(predicate_to_encodings.keys()):
            encodings = sorted(predicate_to_encodings[raw_pred])
            if len(encodings) == 0:
                continue
            rows.append((raw_pred, " || ".join(encodings)))

        cls._emit_table(
            "ISSY predicate->boolean encoding mapping:",
            ("raw_predicate", "boolean_encoding"),
            rows,
        )
