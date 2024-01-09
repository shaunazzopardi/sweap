import argparse
import os

import config
from analysis.compatibility_checking.compatibility_checking import create_nuxmv_model
from analysis.model_checker import ModelChecker
from parsing.string_to_program import string_to_program
from synthesis.synthesis import synthesize
import logging

import time


def main():
    parser = argparse.ArgumentParser()
    # input monitor
    parser.add_argument('--p', dest='program', help="Path to a .prog file.", type=str)

    parser.add_argument('--translate', dest='translate', help="Translation workflow.", type=str)

    # Synthesis workflow
    parser.add_argument('--synthesise', dest='synthesise', help="Synthesis workflow.", type=bool, nargs='?', const=True)

    parser.add_argument('--only_ranking', dest='only_ranking', help="For fairness refinements, only use ranking refinement.", type=bool, nargs='?', const=True)
    parser.add_argument('--only_structural', dest='only_structural', help="For fairness refinements, only use structural refinement.", type=bool, nargs='?', const=True)
    parser.add_argument('--only_safety', dest='only_safety', help="Do not use fairness refinements.", type=bool, nargs='?', const=True)

    # how to connect to strix (default just assume `strix' is in path)
    parser.add_argument('--strix_docker', dest='docker', type=str, nargs='?', const=False)

    args = parser.parse_args()

    if args.program is None:
        raise Exception("Program path not specified.")

    if args.only_ranking is not None:
        if args.only_structural is not None:
            raise Exception("Cannot use both only_ranking and only_structural.")
        config.prefer_ranking = False
        config.only_ranking = True
        config.only_structural = False
        config.only_safety = False

    if args.only_structural is not None:
        if args.only_ranking is not None:
            raise Exception("Cannot use both only_ranking and only_structural.")
        config.prefer_ranking = False
        config.only_ranking = False
        config.only_structural = True
        config.only_safety = False

    if args.only_safety is not None:
        if args.only_ranking is not None or args.only_structural is not None:
            raise Exception("Cannot use both only_safety with only_ranking and only_structural.")
        config.prefer_ranking = False
        config.only_ranking = False
        config.only_structural = False
        config.only_safety = True

    prog_file = open(args.program, "r")
    prog_str = prog_file.read()
    program, ltl_spec = string_to_program(prog_str)

    if not os.path.exists(str(os.getcwd()) + "\\out\\" + program.name):
        os.makedirs(str(os.getcwd()) + "\\out\\" + program.name)

    logging.basicConfig(filename=(str(os.getcwd()) + "\\out\\"
                                  + program.name + "\\"
                                  + str(time.time()) + ".log"),
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
    else:
        raise Exception("Specify either --translate or --synthesise.")


if __name__ == "__main__":
    main()
