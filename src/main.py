import argparse
import logging
import os
import time
from argparse import ArgumentParser, Namespace

from pathlib import Path
from analysis.compatibility_checking.compatibility_checking import (
    create_nuxmv_model,
)
from analysis.model_checker import ModelChecker
from config import Config
from parsing.string_to_ltlmt import ToProgram, string_to_ltlmt
from parsing.string_to_program import string_to_program
from programs.program import Program
from prop_lang.formula import Formula
from synthesis.synthesis import synthesize

dirname = os.path.dirname(__file__)
strix_path = str(os.path.join(dirname, "../binaries"))

os.environ["PATH"] = strix_path + ":" + os.environ["PATH"]


def setup_argument_parser() -> ArgumentParser:
    parser = argparse.ArgumentParser()
    # input monitor
    parser.add_argument("--p", dest="program", help="Path to a .prog file.", type=str)
    parser.add_argument("--tsl", dest="tsl", help="Path to a .tsl file.", type=str)

    parser.add_argument(
        "--translate", dest="translate", help="Translation workflow.", type=str
    )

    # Synthesis workflow
    parser.add_argument(
        "--debug",
        dest="debug",
        help="Debugging mode (sanity checks enabled).",
        type=bool,
        nargs="?",
        const=True,
    )
    parser.add_argument(
        "--synthesise",
        dest="synthesise",
        help="Synthesis workflow.",
        type=bool,
        nargs="?",
        const=True,
    )
    parser.add_argument(
        "--finite-synthesise",
        dest="finite_synthesise",
        help="Finite synthesis workflow (only works with finite programs).",
        type=bool,
        nargs="?",
        const=True,
    )
    parser.add_argument(
        "--log",
        dest="log",
        help="Enable logging (output in working-directory/logs/<program-name>)",
        type=bool,
        nargs="?",
        const=True,
    )
    parser.add_argument("--tlsf", dest="tlsf", help="Path to a .tlsf file.", type=str)
    parser.add_argument(
        "--verify_controller",
        dest="verify_controller",
        help="Verifies controller, if realisable, satisfies given LTL specification against program.",
        type=bool,
        nargs="?",
        const=True,
    )
    parser.add_argument(
        "--lazy",
        dest="lazy",
        help="Lazy approach",
        type=bool,
        nargs="?",
        const=True,
    )
    parser.add_argument(
        "--only_safety",
        dest="only_safety",
        help="Do not use fairness refinements.",
        type=bool,
        nargs="?",
        const=True,
    )
    parser.add_argument(
        "--no_binary_enc",
        dest="no_binary_enc",
        help="Do not use binary encoding (implies --lazy).",
        type=bool,
        nargs="?",
        const=True,
    )
    parser.add_argument(
        "--dual",
        dest="dual",
        help="Tries the dual problem (exchanges environment and controller propositions and objectives).",
        type=bool,
        nargs="?",
        const=True,
    )

    return parser


def process_args(args: Namespace) -> (Program, Formula):
    conf = Config.getConfig()
    if args.debug is not None:
        conf.debug = True

    if not args.lazy and not args.only_safety:
        conf.eager_fairness = True
    else:
        conf.eager_fairness = False

    if args.no_binary_enc:
        conf.eager_fairness = False
        conf.no_binary_enc = True
    else:
        conf.no_binary_enc = False

    if args.verify_controller:
        conf._verify_controller = True
    else:
        conf._verify_controller = False

    if args.dual:
        conf._dual = True
    else:
        conf._dual = False

    conf.add_all_preds_in_prog = True

    if args.only_safety is not None:
        conf.only_safety = True

    if args.finite_synthesise is not None:
        conf.finite_synthesis = True

    if args.program is not None:
        name = ".".join(os.path.basename(args.program).split(".")[0:-1])
        conf.name = name
        with open(args.program) as prog_file:
            prog_str = prog_file.read()
        return string_to_program(prog_str)
    elif args.tsl is not None:
        with open(args.tsl).read() as ltlmt_formula:
            ltlmt = string_to_ltlmt(ltlmt_formula)
            tp = ToProgram()
            prog_name = Path(args.tsl).stem + "_tsl"
            return tp.ltlmt2prog(ltlmt, prog_name)
    else:
        raise Exception("Program path not specified.")


def handle_translation(target, program, ltl_spec):
    if target.lower() == "dot":
        print("\ndot version of program:\n\n" + str(program.to_dot()))
    elif target.lower() == "nuxmv":
        print(
            "\nnuxmv version of program:\n\n"
            + create_nuxmv_model(program.to_nuXmv_with_turns_for_con_verif())
        )
    elif target.lower() == "prog":
        print(
            "\nsymbolic automaton version of program:\n\n" + program.to_prog(ltl_spec)
        )
    elif target.lower() == "vmt":
        model = create_nuxmv_model(program.to_nuXmv_with_turns_for_con_verif())
        model_checker = ModelChecker()
        model_checker.to_vmt(model, ltl_spec, "model")
        vmt = open("model.vmt").read()
        os.remove("model.vmt")
        print("\nvmt version of program:\n\n" + vmt)
    else:
        print(
            target
            + " is not recognised. --translate options are 'dot' or 'nuxmv' or 'prog' or 'vmt'."
        )


def main():
    parser: ArgumentParser = setup_argument_parser()

    args: Namespace = parser.parse_args()

    if args.program is None and args.tsl is None:
        raise Exception("No input given! (Specify either --p or --tsl.)")
    if args.program is not None and args.tsl is not None:
        raise Exception("Cannot use both --p and --tsl.")

    program, ltl_spec = process_args(args)

    if args.log:
        logdir = os.getcwd() + "/logs/" + program.name + "/" + (str(time.time()))
        Config.getConfig()._log = logdir

        if not os.path.exists(logdir):
            os.makedirs(logdir)

        logging.basicConfig(
            filename=(str(logdir + "/.log")),
            encoding="utf-8",
            level=logging.INFO,
            format="%(asctime)s %(levelname)-8s %(message)s",
            datefmt="%Y-%m-%d %H:%M:%S",
            force=True,
        )

        logging.info(program.to_dot())
    else:
        logging.disable(logging.CRITICAL)

    if args.translate is not None:
        handle_translation(args.translate, program, ltl_spec)
    elif args.synthesise or args.finite_synthesise:
        ltl = ltl_spec
        if ltl is None:
            if args.tlsf is None:
                raise Exception("No property specified.")
        elif args.tlsf is not None:
            print("Spec in both program and as TLSF given, will use the TLSF.")

        start = time.time()
        (realiz, mm) = synthesize(program, ltl, args.tlsf)
        end = time.time()

        if (realiz and not args.dual) or (not realiz and args.dual):
            print("Realizable.")
        else:
            print("Unrealizable.")

        print(str(mm))

        print("Synthesis took: ", (end - start) * 10**3, "ms")

    else:
        raise Exception("Specify either --translate or --synthesise.")


if __name__ == "__main__":
    main()
