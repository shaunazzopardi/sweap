import argparse
import os

from config import Config
from analysis.compatibility_checking.compatibility_checking import (
    create_nuxmv_model,
    create_nuxmv_model_for_compatibility_checking,
)
from analysis.model_checker import ModelChecker
from parsing.string_to_ltlmt import ToProgram, string_to_ltlmt
from parsing.string_to_program import string_to_program
from synthesis.synthesis import finite_state_synth, synthesize
import logging
from pathlib import Path
import time
import os

dirname = os.path.dirname(__file__)
strix_path = str(os.path.join(dirname, "../binaries"))

os.environ["PATH"] = strix_path + ":" + os.environ["PATH"]


def main():
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
    parser.add_argument("--tlsf", dest="tlsf", help="Path to a .tlsf file.", type=str)

    # Strix workflow
    parser.add_argument(
        "--synth-strix",
        dest="synth_strix",
        help="Synthesise with Strix (only for finite-state problems).",
        type=bool,
        nargs="?",
        const=True,
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

    args = parser.parse_args()

    if args.program is None and args.tsl is None:
        raise Exception("No input given! (Specify either --p or --tsl.)")
    if args.program is not None and args.tsl is not None:
        raise Exception("Cannot use both --p and --tsl.")

    conf = Config.getConfig()
    if args.debug is not None:
        conf.debug = True

    if args.program is not None:
        prog_file = open(args.program, "r")
        prog_str = prog_file.read()
        program, ltl_spec = string_to_program(prog_str)
    elif args.tsl is not None:
        ltlmt_formula = open(args.tsl, "r").read()
        ltlmt = string_to_ltlmt(ltlmt_formula)
        tp = ToProgram()
        prog_name = Path(args.tsl).stem + "_tsl"
        program, ltl_spec = tp.ltlmt2prog(ltlmt, prog_name)
    else:
        raise Exception("Program path not specified.")

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

    logdir = Path(os.getcwd()) / "out" / program.name

    if not os.path.exists(logdir):
        os.makedirs(logdir)

    logging.basicConfig(
        filename=(str(logdir / (str(time.time()) + ".log"))),
        encoding="utf-8",
        level=logging.INFO,
        format="%(asctime)s %(levelname)-8s %(message)s",
        datefmt="%Y-%m-%d %H:%M:%S",
        force=True,
    )

    logging.info(program.to_dot())

    if args.translate is not None:
        if args.translate.lower() == "dot":
            print("\ndot version of program:\n\n" + str(program.to_dot()))
        elif args.translate.lower() == "nuxmv":
            print("\nnuxmv version of program:\n\n" + create_nuxmv_model(program.to_nuXmv_with_turns_for_con_verif()))
        elif args.translate.lower() == "prog":
            print("\nsymbolic automaton version of program:\n\n" + program.to_prog(ltl_spec))
        elif args.translate.lower() == "vmt":
            model = create_nuxmv_model(program.to_nuXmv_with_turns_for_con_verif())
            model_checker = ModelChecker()
            model_checker.to_vmt(model, ltl_spec, "model")
            vmt = open("model.vmt").read()
            os.remove("model.vmt")
            print("\nvmt version of program:\n\n" + vmt)
        else:
            print(
                args.translate
                + " is not recognised. --translate options are 'dot' or 'nuxmv' or 'prog' or 'vmt'."
            )
    elif args.synthesise or args.synth_strix:
        ltl = ltl_spec
        if ltl is None:
            if args.tlsf is None:
                raise Exception("No property specified.")
        elif args.tlsf is not None:
            print("Spec in both program and as TLSF given, will use the TLSF.")

        start = time.time()
        (realiz, mm) = (
            finite_state_synth(program, ltl, args.tlsf)
            if args.synth_strix
            else synthesize(program, ltl, args.tlsf, False)
        )
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
