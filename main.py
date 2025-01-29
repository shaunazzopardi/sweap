import argparse
import os

from config import Config
from analysis.compatibility_checking.compatibility_checking import create_nuxmv_model, \
    create_nuxmv_model_for_compatibility_checking
from analysis.model_checker import ModelChecker
from parsing.string_to_ltlmt import ToProgram, string_to_ltlmt
from parsing.string_to_program import string_to_program
from synthesis.synthesis import finite_state_synth, synthesize
import logging
from pathlib import Path

os.environ['PATH'] = "./binaries:" + os.environ['PATH']

import time


def main():
    parser = argparse.ArgumentParser()
    # input monitor
    parser.add_argument('--p', dest='program', help="Path to a .prog file.", type=str)
    parser.add_argument('--tsl', dest='tsl', help="Path to a .tsl file.", type=str)

    parser.add_argument('--translate', dest='translate', help="Translation workflow.", type=str)

    # Synthesis workflow
    parser.add_argument('--debug', dest='debug', help="Debugging mode (sanity checks enabled).", type=bool, nargs='?', const=True)
    parser.add_argument('--synthesise', dest='synthesise', help="Synthesis workflow.", type=bool, nargs='?', const=True)
    parser.add_argument('--tlsf', dest='tlsf', help="Path to a .tlsf file.", type=str)

    # Strix workflow
    parser.add_argument('--synth-strix', dest='synth_strix', help="Synthesise with Strix (only for finite-state problems).", type=bool, nargs='?', const=True)

    # parser.add_argument('--only_ranking', dest='only_ranking', help="For fairness refinements, only use ranking refinement.", type=bool, nargs='?', const=True)
    # parser.add_argument('--only_structural', dest='only_structural', help="For fairness refinements, only use structural refinement.", type=bool, nargs='?', const=True)
    # parser.add_argument('--eager_fairness', dest='eager_fairness', help="Synthesise ranking refinements for each predicate initially.", type=bool, nargs='?', const=True)
    parser.add_argument('--verify_controller', dest='verify_controller', help="Verifies controller, if realisable, satisfies given LTL specification against program.", type=bool, nargs='?', const=True)
    # parser.add_argument('--add_all_preds_in_prog', dest='add_all_preds_in_prog', help="Initially each predicate used in the program.", type=bool, nargs='?', const=True)
    parser.add_argument('--lazy', dest='lazy', help="Lazy approach", type=bool, nargs='?', const=True)
    parser.add_argument('--only_safety', dest='only_safety', help="Do not use fairness refinements.", type=bool, nargs='?', const=True)

    ##how to connect to strix (default just assume `strix' is in path)
    # parser.add_argument('--strix_docker', dest='docker', type=str, nargs='?', const=False)

    args = parser.parse_args()

    if args.program is None and args.tsl is None:
        raise Exception("No input given! (Specify either --p or --tsl.)")
    if args.program is not None and args.tsl is not None:
        raise Exception("Cannot use both --p and --tsl.")

    conf = Config.getConfig()
    if args.debug is not None:
        conf.debug = True

    if args.program is None and args.tsl is None:
        raise Exception("Program path not specified.")

    # if args.only_ranking is not None:
    #     if args.only_structural is not None:
    #         raise Exception("Cannot use both only_ranking and only_structural.")
    #     conf.prefer_ranking = False
    #     conf.only_ranking = True
    #     conf.only_structural = False
    #     conf.only_safety = False

    # if args.only_structural is not None:
    #     if args.only_ranking is not None:
    #         raise Exception("Cannot use both only_ranking and only_structural.")
    #     conf.prefer_ranking = False
    #     conf.only_ranking = False
    #     conf.only_structural = True
    #     conf.only_safety = False

    if not args.lazy and not args.only_safety:
        conf.eager_fairness = True
    else:
        conf.eager_fairness = False

    if args.verify_controller:
        conf._verify_controller = True
    else:
        conf._verify_controller = False

    conf.add_all_preds_in_prog = True

    if args.only_safety is not None:
        # if args.only_ranking is not None or args.only_structural is not None:
        #     raise Exception("Cannot use both only_safety with only_ranking and only_structural.")
        # conf.prefer_ranking = False
        # conf.only_ranking = False
        # conf.only_structural = False
        conf.only_safety = True

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

    logdir = Path(os.getcwd()) / "out" / program.name

    if not os.path.exists(logdir):
        os.makedirs(logdir)

    logging.basicConfig(filename=(str(logdir / (str(time.time()) + ".log"))),
                        encoding='utf-8',
                        level=logging.INFO,
                        format='%(asctime)s %(levelname)-8s %(message)s',
                        datefmt='%Y-%m-%d %H:%M:%S',
                        force=True)

    logging.info(program.to_dot())

    if args.translate is not None:
        if args.translate.lower() == "dot":
            print(program.to_dot())
        elif args.translate.lower() == "nuxmv":
            print(create_nuxmv_model_for_compatibility_checking(program.to_nuXmv_with_turns()))
        elif args.translate.lower() == "prog":
            print(program.to_prog(ltl_spec))
        elif args.translate.lower() == "vmt":
            model = create_nuxmv_model(program.to_nuXmv_with_turns())
            ltl_spec = None
            if args.ltl != None:
                ltl_spec = args.ltl
            model_checker = ModelChecker()
            model_checker.to_vmt(model, ltl_spec)
        else:
            print(args.translate + " is not recognised. --translate options are 'dot' or 'nuxmv' or 'prog' or 'vmt'.")
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
            else synthesize(program, ltl, args.tlsf, False))
        end = time.time()

        if realiz:
            print('Realizable.')
            print(str(mm))
        else:
            print('Unrealizable.')
            print(str(mm))

        print("Synthesis took: ", (end - start) * 10 ** 3, "ms")

    else:
        raise Exception("Specify either --translate or --synthesise.")


if __name__ == "__main__":
    main()
