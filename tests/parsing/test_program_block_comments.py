from unittest import TestCase

import parsec

import config
from parsing.string_to_program import (
    bool_decl_parser_untyped,
    _mask_comments,
    make_program_action_formula_parser,
    nondet_assignment,
    num_decl_parser,
    num_decl_parser_untyped,
    outputs,
    spaces,
    specification_parser,
    string_to_program,
)
from prop_lang.nondet import NonDeterministic


PROGRAM = """program comments {
    STATES { q: init }
    ENVIRONMENT EVENTS { request }
    CONTROLLER EVENTS { grant }
    VALUATION { x: integer := 0; }
    TRANSITIONS { q -> q [true $ x := x + 1] }
    SPECIFICATION { G (request -> F grant) }
}
"""


class TestProgramBlockComments(TestCase):
    def setUp(self):
        conf = config.Config.getConfig()
        self.addCleanup(setattr, conf, "workers", conf.workers)
        conf.workers = 1

    def test_line_comment_delimiters_cannot_change_program_structure(self):
        expected_program, expected_spec = string_to_program(PROGRAM)
        variants = [
            PROGRAM.replace('true $', 'true // $ x := 999\n $'),
            PROGRAM.replace('x: integer := 0;', 'x: integer := 0 // ; ghost: bool := false\n;'),
            PROGRAM.replace('F grant)', 'F grant) // } SPECIFICATION { false\n'),
        ]
        for source in variants:
            with self.subTest(source=source):
                program, spec = string_to_program(source)
                self.assertEqual(str(program), str(expected_program))
                self.assertEqual(str(spec), str(expected_spec))

    def test_commented_specification_brace_cannot_close_section(self):
        source = PROGRAM.replace(
            'SPECIFICATION { G (request -> F grant) }', 'SPECIFICATION { true // }'
        )
        with self.assertRaises(parsec.ParseError):
            string_to_program(source)

    def test_bare_carriage_return_does_not_end_line_comment(self):
        source = 'x // ignored\rif false\nnext'
        masked = _mask_comments(source)
        self.assertEqual(masked, 'x           \r        \nnext')


    def test_comments_preserve_program_and_specification(self):
        expected_program, expected_spec = string_to_program(PROGRAM)
        comment = "/* multiline\n } ] ; , $ # >> /* text */"
        variants = [
            comment + PROGRAM + comment,
            PROGRAM.replace("STATES", comment + "STATES"),
            PROGRAM.replace("q: init", "q:" + comment + "init"),
            PROGRAM.replace("integer := 0", "integer := " + comment + "0"),
            PROGRAM.replace("true $", "true " + comment + "$"),
            PROGRAM.replace("x + 1", "x +" + comment + "1"),
            PROGRAM.replace("request ->", "request " + comment + "->"),
            PROGRAM.replace("F grant", "F/**//**/grant"),
            PROGRAM.replace(
                "TRANSITIONS {", "TRANSITIONS [semantics=" + comment + "by-order] {"
            ),
            PROGRAM.replace("true $", "otherwise " + comment + "$"),
            PROGRAM.replace("F grant", "F // /* ignored\n grant"),
            PROGRAM.replace("program comments", "arena comments").replace(
                "SPECIFICATION", "OBJECTIVE " + comment
            ),
        ]
        for source in variants:
            with self.subTest(source=source):
                program, spec = string_to_program(source)
                self.assertEqual(str(spec), str(expected_spec))
                self.assertEqual(program.states, expected_program.states)
                self.assertEqual(str(program), str(expected_program))
                self.assertEqual(
                    [str(t) for t in program.transitions],
                    [str(t) for t in expected_program.transitions],
                )

    def test_preserves_positions_and_separates_tokens(self):
        source = "a/* x\r\ny */b"
        masked = _mask_comments(source)
        self.assertEqual(masked, "a    \r\n    b")
        self.assertEqual(len(masked), len(source))

    def test_text_without_comments_is_unchanged(self):
        for source in ("", PROGRAM, "x' = x / 2 + y * 3\r\n"):
            with self.subTest(source=source):
                self.assertEqual(_mask_comments(source), source)

    def test_mixed_comments_preserve_every_following_token_position(self):
        for newline in ("\n", "\r\n"):
            with self.subTest(newline=newline):
                source = "a/* x" + newline + "y */b// z" + newline + "c/**/d"
                expected = "a    " + newline + "    b    " + newline + "c    d"
                self.assertEqual(_mask_comments(source), expected)
                for token in ("a", "b", "c", "d"):
                    self.assertEqual(expected.index(token), source.index(token))

    def test_complete_comment_does_not_hide_unterminated_later_comment(self):
        source = "/* complete */\n// ignored /*\n/* incomplete"
        with self.assertRaises(parsec.ParseError) as error:
            _mask_comments(source)
        self.assertEqual(error.exception.index, source.rindex("/*"))

    def test_line_comments_do_not_open_block_comments(self):
        source = "// /* ignored\nG /* real */ a"
        masked = _mask_comments(source)
        self.assertEqual(masked, "             \nG            a")

    def test_unterminated_comments_are_rejected(self):
        for comment in ("/*", "/*/", "/* missing terminator"):
            with self.subTest(comment=comment):
                for source in (
                    "\n  " + comment + PROGRAM,
                    PROGRAM.replace("F grant", "F " + comment),
                    PROGRAM + comment,
                ):
                    with self.assertRaises(parsec.ParseError):
                        string_to_program(source)

    def test_specification_parser_accepts_preprocessed_comments(self):
        source = "SPECIFICATION { G /* }\n ignored */ grant }"
        formula = (specification_parser << parsec.eof()).parse(_mask_comments(source))
        self.assertEqual(str(formula), "G(grant)")

    def test_whitespace_accepts_multiple_comments(self):
        source = " /* one */\n/**//* two */ "
        (spaces() << parsec.eof()).parse(_mask_comments(source))

    def test_line_comments_preserve_program_and_specification(self):
        expected_program, expected_spec = string_to_program(PROGRAM)
        comment = "// ignored } ] ; , $ # >> /*\n"
        variants = [
            comment + PROGRAM,
            PROGRAM.rstrip() + "// trailing comment without newline",
            PROGRAM.replace("STATES", comment + "STATES"),
            PROGRAM.replace("q: init", "q:" + comment + "init"),
            PROGRAM.replace("integer := 0", "integer := " + comment + "0"),
            PROGRAM.replace("true $", "true " + comment + "$"),
            PROGRAM.replace("x + 1", "x + " + comment + "1"),
            PROGRAM.replace("F grant", "F " + comment + "grant"),
            PROGRAM.replace(
                "TRANSITIONS {", "TRANSITIONS [semantics=" + comment + "by-order] {"
            ),
        ]
        for source in variants:
            for newline in ("\n", "\r\n"):
                with self.subTest(source=source, newline=newline):
                    program, spec = string_to_program(source.replace("\n", newline))
                    self.assertEqual(str(program), str(expected_program))
                    self.assertEqual(str(spec), str(expected_spec))

    def test_whitespace_accepts_mixed_comments_and_line_comment_at_eof(self):
        source = "// /* ignored\r\n /* // ignored */ // final comment"
        (spaces() << parsec.eof()).parse(_mask_comments(source))

    def test_block_comment_ends_at_first_closing_delimiter(self):
        self.assertEqual(_mask_comments("/* outer /* inner */ trailing"), " " * 20 + " trailing")

    def test_expression_delimiters_are_ignored_only_inside_comments(self):
        source = "x / 2 /* >> ] */ // >> ]\nx >> grant"
        value = _mask_comments(source)
        self.assertEqual(value, "x / 2                   \nx >> grant")

    def test_relational_actions_ignore_commented_delimiters(self):
        parser = make_program_action_formula_parser({"x"}) << parsec.eof()
        expected = parser.parse("x' = x + 1")
        actual = parser.parse(_mask_comments("x' = x /* >> ] */ + 1"))
        self.assertEqual(str(actual), str(expected))

    def test_output_and_nondeterministic_expressions(self):
        result = (outputs << parsec.eof()).parse(_mask_comments(">> grant /* ],; */"))
        self.assertEqual([str(value).strip() for value in result], ["grant"])
        result = (nondet_assignment << parsec.eof()).parse(_mask_comments("*[x /* ] */ > 0]"))
        self.assertEqual(str(result), "(x > 0)")

    def test_comments_cannot_join_keyword_fragments(self):
        with self.assertRaises(parsec.ParseError):
            string_to_program(PROGRAM.replace("program", "pro/**/gram", 1))

    def test_parse_error_position_is_preserved_after_comments(self):
        source = "/* header\n comment */\n" + PROGRAM.replace("STATES", "INVALID")
        with self.assertRaises(parsec.ParseError) as error:
            string_to_program(source)
        self.assertEqual(error.exception.index, source.index("INVALID"))

    def test_unterminated_comment_reports_its_original_position(self):
        source = "// header\n  /* missing terminator"
        with self.assertRaises(parsec.ParseError) as error:
            string_to_program(source)
        self.assertEqual(error.exception.index, source.index("/*"))
        self.assertIn("closing */", str(error.exception))



    def test_comments_after_nondeterministic_initial_value(self):
        parser = num_decl_parser << parsec.eof()
        for suffix in ("   ", "/* explanation */", "// explanation\n"):
            with self.subTest(suffix=suffix):
                name, _, value = parser.parse(
                    _mask_comments("x: integer := *" + suffix)
                )
                self.assertEqual(name, "x")
                self.assertIsInstance(value, NonDeterministic)

    def test_commented_out_code_has_no_effect(self):
        expected_program, expected_spec = string_to_program(PROGRAM)
        variants = [
            PROGRAM.replace("STATES", "/* STATES { other: init } */\nSTATES"),
            PROGRAM.replace("TRANSITIONS", "// VALUATION { bad: invalid := ???; }\nTRANSITIONS"),
            PROGRAM.replace("q -> q [", "/* q -> missing [true $ x := 999], */ q -> q ["),
            PROGRAM.replace("SPECIFICATION", "// SPECIFICATION { false }\nSPECIFICATION"),
        ]
        for source in variants:
            with self.subTest(source=source):
                program, spec = string_to_program(source)
                self.assertEqual(str(program), str(expected_program))
                self.assertEqual(str(spec), str(expected_spec))

    def test_comments_do_not_join_numeric_or_operator_fragments(self):
        for original, replacement in (
            ("integer := 0", "integer := 1/**/2"),
            (":=", ":/**/="),
            ("q -> q", "q -/**/> q"),
        ):
            with self.subTest(replacement=replacement):
                with self.assertRaises(parsec.ParseError):
                    string_to_program(PROGRAM.replace(original, replacement))

    def test_stray_comment_terminator_is_not_removed(self):
        self.assertEqual(_mask_comments("*/"), "*/")
        with self.assertRaises(parsec.ParseError):
            string_to_program(PROGRAM + "*/")

    def test_comments_alone_are_not_a_program(self):
        for source in ("/**/", "// only a comment", "/* first */\n// second"):
            with self.subTest(source=source):
                with self.assertRaises(parsec.ParseError):
                    string_to_program(source)
