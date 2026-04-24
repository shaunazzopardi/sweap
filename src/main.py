import argparse
import logging
import os
import time

from analysis.compatibility_checking.program_to_nuxmv import (
    create_nuxmv_model,
    program_to_nuxmv_model,
)
import config

from argparse import ArgumentParser, Namespace
from pathlib import Path
from analysis.model_checker import ModelChecker
from config import Config
from parsing import string_to_issy
from parsing.string_to_ltlmt import ToProgram
from parsing.string_to_ltl import string_to_ltlmt
from parsing.string_to_program import string_to_program
from parsing.string_to_rpg import rpg_parsec
from programs.program import Program
from prop_lang.formula import Formula
from synthesis.machines.wrapped_hoa import WrappedHOA
from synthesis.synthesis import synthesize

dirname = os.path.dirname(__file__)
strix_path = str(os.path.join(dirname, "../binaries"))

os.environ["PATH"] = strix_path + ":" + os.environ["PATH"]


def setup_argument_parser() -> ArgumentParser:
    parser = argparse.ArgumentParser()

    input_group = parser.add_mutually_exclusive_group()

    input_group.add_argument(
        "--p", dest="program", help="Path to a .prog file.", type=str
    )
    input_group.add_argument("--tsl", dest="tsl", help="Path to a .tsl file.", type=str)
    input_group.add_argument("--rpg", dest="rpg", help="Path to a .rpg file.", type=str)
    input_group.add_argument(
        "--issy", dest="issy", help="Path to a .issy file.", type=str
    )

    action_group = parser.add_mutually_exclusive_group()

    action_group.add_argument(
        "--translate",
        dest="translate",
        help="Options for target language: `prog', `dot', `nuxmv', or `'vmt'. Assumes input through `--p', `--tsl', `--rpg', or '--issy'.",
        type=str,
    )
    action_group.add_argument(
        "--synthesise",
        "--synthesis",
        dest="synthesise",
        help="Synthesis workflow.",
        type=int,
        nargs="?",
        const=-1,
    )
    action_group.add_argument(
        "--finite_synthesise",
        dest="finite_synthesise",
        help="Finite synthesis workflow (only works with finite programs).",
        type=int,
        nargs="?",
        const=-1,
    )
    action_group.add_argument(
        "--model_check",
        dest="model_check",
        help="Model checking workflow (directly attempts infinite-state IC3 model checking on the problem).",
        type=bool,
        nargs="?",
        const=True,
    )

    parser.add_argument(
        "--out_dot",
        dest="out_dot",
        help="Parses HOA mealy/moore machine into DOT.",
        type=bool,
        nargs="?",
        const=True,
    )
    parser.add_argument(
        "--debug",
        dest="debug",
        help="Debugging mode (sanity checks enabled). "
        "Note this may get stuck during compatibility checking or verification, "
        "since given a positive result it model checks whether there is eventually a deadlock.",
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
        "--synthesis_backend",
        dest="synthesis_backend",
        help="Choice of synthesis backend, options: strix or semml (default).",
        type=str,
        nargs="?",
        default="semml",
    )
    parser.add_argument(
        "--abstraction_backend",
        dest="abstraction_backend",
        help="Choice of abstraction backend, options: effects.",
        type=str,
        nargs="?",
        default=config.effects,
    )
    parser.add_argument(
        "--verify_controller",
        dest="verify_controller",
        help="Verifies controller, if realisable, satisfies given LTL specification against program.",
        type=bool,
        nargs="?",
        const=True,
    )
    parser.add_argument(
        "--workers",
        dest="workers",
        help="Number of worker processes for parallel abstraction steps.",
        type=int,
    )
    parser.add_argument(
        "--synthesis_memory_limit_mb",
        dest="synthesis_memory_limit_mb",
        help="Optional memory limit (MB) for each LTL synthesis backend process. If omitted, unbounded.",
        type=int,
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
    # TODO: add option to fill in gaps between predicates in chains
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
        help="Tries the dual problem (gives controller control of state predicates).",
        type=bool,
        nargs="?",
        const=True,
    )
    return parser


def process_args(args: Namespace) -> tuple[Program, Formula]:
    conf = Config.getConfig()
    conf.debug = args.debug

    if not args.lazy and not args.only_safety:
        conf.eager_fairness = True
    else:
        conf.eager_fairness = False

    conf.only_safety = args.only_safety
    if args.finite_synthesise and args.lazy:
        raise Exception("--lazy cannot be used with finite_synthesise flag.")

    if args.no_binary_enc or args.translate:
        conf.no_binary_enc = True
    else:
        conf.no_binary_enc = False

    if args.verify_controller:
        conf._verify_controller = True
    else:
        conf._verify_controller = False

    if args.dual:
        conf.dual = True
    else:
        conf.dual = False

    conf.add_all_preds_in_prog = True

    conf.finite_synthesis = args.finite_synthesise
    if args.workers is not None:
        conf.workers = max(1, int(args.workers))
    if args.synthesis_memory_limit_mb is None:
        conf.synthesis_memory_limit_mb = None
    else:
        conf.synthesis_memory_limit_mb = (
            int(args.synthesis_memory_limit_mb)
            if int(args.synthesis_memory_limit_mb) > 0
            else None
        )

    if not args.synthesis_backend:
        raise Exception("--synthesis_backend present without an argument.")
    elif args.synthesis_backend not in config.synthesis_backends:
        raise Exception(args.synthesis_backend + " is not a valid synthesis backend.")
    else:
        conf.backend = args.synthesis_backend

    if not args.abstraction_backend:
        raise Exception("--abstraction_backend present without an argument.")
    elif args.abstraction_backend not in config.abstraction_backends:
        raise Exception(
            args.abstraction_backend + " is not a valid abstraction backend."
        )
    else:
        conf.abstraction_backend = args.abstraction_backend

    if args.program is not None:
        name = ".".join(os.path.basename(args.program).split(".")[0:-1])
        conf.name = name
        with open(args.program) as prog_file:
            prog_str = prog_file.read()
        return string_to_program(prog_str)
    elif args.tsl is not None:
        name = ".".join(os.path.basename(args.tsl).split(".")[0:-1])
        conf.name = name + "_tsl"
        with open(args.tsl) as ltlmt_formula:
            ltlmt, var_decs = string_to_ltlmt(ltlmt_formula.read())
            tp = ToProgram()
            prog_name = Path(args.tsl).stem + "_tsl"
            return tp.ltlmt2prog(ltlmt, prog_name, var_decs=var_decs)
    elif args.rpg is not None:
        name = ".".join(os.path.basename(args.rpg).split(".")[0:-1])
        conf.name = name + "_rpg"
        with open(args.rpg) as rpg_str:
            result = rpg_parsec(rpg_str.read(), conf.name)
            return result
    elif args.issy is not None:
        name = ".".join(os.path.basename(args.issy).split(".")[0:-1])
        conf.name = name + "_issy"
        with open(args.issy) as issy_str:
            result = string_to_issy.string_to_issy(issy_str.read(), conf.name)
            return result
    else:
        raise Exception(
            "No input given! " "(Specify one of --p, --issy, --rpg, or --tsl.)"
        )


def handle_translation(target, program, ltl_spec) -> str:
    if target.lower() == "dot":
        return str(program.to_dot())
    elif target.lower() == "nuxmv":
        return create_nuxmv_model(program_to_nuxmv_model(program))
    elif target.lower() == "prog":
        return program.to_prog(ltl_spec)
    elif target.lower() == "issy":
        return program.to_issy(ltl_spec)
    elif target.lower() == "vmt":
        model = create_nuxmv_model(program_to_nuxmv_model(program))
        model_checker = ModelChecker()
        model_checker.to_vmt(model, ltl_spec, "model")
        vmt = open("model.vmt").read()
        os.remove("model.vmt")
        return vmt
    else:
        raise Exception(
            target
            + " is not recognised. --translate options are 'prog' or 'issy' or 'dot' or 'nuxmv' or 'vmt'."
        )


def main():
    parser: ArgumentParser = setup_argument_parser()

    args: Namespace = parser.parse_args()

    _main(args)


def _main(args: Namespace):
    program, ltl_spec = process_args(args)

    if args.log:
        logdir = (
            os.getcwd() + "/logs/" + Config.getConfig().name + "/" + (str(time.time()))
        )
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
    else:
        logging.disable(logging.CRITICAL)

    logging.info("Input args: %s", vars(args))

    if args.translate:
        out = handle_translation(args.translate, program, ltl_spec)
        print(str(args.translate) + " version of the problem:\n\n" + out)
    elif args.model_check:
        nuxmv_script = handle_translation("nuxmv", program, ltl_spec)
        _, out = ModelChecker().invar_check(
            nuxmv_script, ltl_spec.to_nuxmv(), None, True
        )
        print(nuxmv_script)
        print(out)
    elif args.synthesise or args.finite_synthesise:
        ltl = ltl_spec
        if ltl is None:
            if args.tlsf is None:
                raise Exception("No property specified.")
        elif args.tlsf is not None:
            print("Spec in both program and as TLSF given, will use the TLSF.")

        start = time.time()

        bound = (
            args.synthesise if args.synthesise is not None else args.finite_synthesise
        )
        mm: WrappedHOA = synthesize(program, ltl, args.tlsf, bound)
        end = time.time()

        print(mm.hoa)
        if args.out_dot:
            print(mm.machine.to_dot())

        print("Realisable" if mm.realisable else "Unrealisable")
        print("Synthesis took: ", (end - start) * 10**3, "ms")

    else:
        raise Exception(
            "Specify either --translate or --synthesise or --finite_synthesise."
        )


if __name__ == "__main__":
    main()
