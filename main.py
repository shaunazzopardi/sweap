import argparse
import os
from analysis.abstraction.effects_abstraction.effects_abstraction import EffectsAbstraction

from analysis.compatibility_checking.compatibility_checking import create_nuxmv_model
from analysis.model_checker import ModelChecker
from parsing.string_to_program import string_to_program
from prop_lang.util import finite_state_preds
from synthesis.synthesis import finite_state_synth, synthesize
import logging
from pathlib import Path

import time


def main():
    parser = argparse.ArgumentParser()
    # input monitor
    parser.add_argument('--p', dest='program', help="Path to a .prog file.", type=str)

    parser.add_argument('--translate', dest='translate', help="Translation workflow.", type=str)

    # Synthesis workflow
    parser.add_argument('--synthesise', dest='synthesise', help="Synthesis workflow.", type=bool, nargs='?', const=True)

    # Strix workflow
    parser.add_argument('--synth-strix', dest='synth_strix', help="Synthesise with Strix (only for finite-state problems).", type=bool, nargs='?', const=True)

    parser.add_argument('--tlsf', dest='tlsf', help="Path to a .tlfs file.", type=str)

    # how to connect to strix (default just assume `strix' is in path)
    parser.add_argument('--strix_docker', dest='docker', type=str, nargs='?', const=False)

    args = parser.parse_args()

    if args.program is None:
        raise Exception("Program path not specified.")

    prog_file = open(args.program, "r")
    prog_str = prog_file.read()
    program, ltl_spec = string_to_program(prog_str)

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
            print(create_nuxmv_model(program.to_nuXmv_with_turns()))
        elif args.translate.lower() == "vmt":
            model = create_nuxmv_model(program.to_nuXmv_with_turns())
            ltl_spec = None
            if args.ltl != None:
                ltl_spec = args.ltl
            model_checker = ModelChecker()
            model_checker.to_vmt(model, ltl_spec)
        else:
            print(args.translate + " is not recognised. --translate options are 'dot' or 'nuxmv' or 'vmt'.")
    elif args.synthesise:
        ltl = ltl_spec
        if ltl is None:
            if args.tlsf is None:
                raise Exception("No property specified.")
        elif args.tlsf is not None:
            print("Spec in both program and as TLSF given, will use the TLSF.")

        start = time.time()
        (realiz, mm) = synthesize(program, ltl, args.tlsf, args.docker)
        end = time.time()

        if realiz:
            print('Realizable.')
            print(str(mm))
        else:
            print('Unrealizable.')
            print(str(mm))

        print("Synthesis took: ", (end - start) * 10 ** 3, "ms")
    elif args.synth_strix:
        ltl = ltl_spec
        if ltl is None:
            if args.tlsf is None:
                raise Exception("No property specified.")
        elif args.tlsf is not None:
            print("Spec in both program and as TLSF given, will use the TLSF.")
        finite_state_synth(program, ltl, args.tlsf)

    else:
        raise Exception("Specify either --translate or --synthesise.")


if __name__ == "__main__":
    main()
