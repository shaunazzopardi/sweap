import argparse
import logging
import os
from tempfile import NamedTemporaryFile
import time
from pathlib import Path

from analysis.compatibility_checking.compatibility_checking import \
    create_nuxmv_model
from analysis.model_checker import ModelChecker
from parsing.dsl.transform import dsl_to_prog_and_tlsf, dsl_to_program
from parsing.string_to_program import string_to_program
from synthesis.synthesis import synthesize


def main():
    parser = argparse.ArgumentParser()
    # input monitor
    parser.add_argument('--p', dest='program', help="Path to a .prog file.", type=str)

    parser.add_argument('--translate', dest='translate', help="Translation workflow.", type=str)

    # Synthesis workflow
    parser.add_argument('--synthesise', dest='synthesise', help="Synthesis workflow.", type=bool, nargs='?', const=True)

    parser.add_argument('--l', dest='ltl', help="Inline LTL formula.", type=str)
    parser.add_argument('--tlsf', dest='tlsf', help="Path to a .tlfs file.", type=str)

    # how to connect to strix (default just assume `strix' is in path)
    parser.add_argument('--strix_docker', dest='docker', type=str, nargs='?', const=False)

    args = parser.parse_args()

    if args.program is None:
        raise Exception("Program path not specified.")

    fname = Path(args.program)
    with open(args.program, "r") as prog_file:
        prog_str = prog_file.read()

    guarantees, assumes, dsl_prog, dsl_tlsf = None, None, None, None
    if fname.suffix == ".dsl":
        program, guarantees, assumes = dsl_to_program(fname.name, prog_str)
        (dsl_prog, dsl_tlsf) = dsl_to_prog_and_tlsf(
            program, args.ltl, args.tlsf, guarantees, assumes)
        with NamedTemporaryFile("w", delete=False) as dsl_tlsf_file:
            dsl_tlsf_file.write(dsl_tlsf)
        args.tlsf = dsl_tlsf_file.name
    else:
        program = string_to_program(prog_str)

    logdir = Path(os.getcwd()) / "out" / program.name

    if not os.path.exists(logdir):
        os.makedirs(logdir)

    logging.basicConfig(filename=(logdir / (str(time.time()) + ".log")),
                        encoding='utf-8',
                        level=logging.INFO,
                        format='%(asctime)s %(levelname)-8s %(message)s',
                        datefmt='%Y-%m-%d %H:%M:%S',
                        force=True)

    logging.info(program.to_dot())

    if args.translate is not None:
        if args.translate.lower() == "dot":
            print(program.to_dot())
        elif args.translate.lower() == "prog-tlsf":
            print(dsl_prog, "\n\n", dsl_tlsf)
        elif args.translate.lower() == "nuxmv":
            print(create_nuxmv_model(program.to_nuXmv_with_turns()))
        elif args.translate.lower() == "vmt":
            model = create_nuxmv_model(program.to_nuXmv_with_turns())
            ltl_spec = None
            if args.ltl is not None:
                ltl_spec = args.ltl
            model_checker = ModelChecker()
            model_checker.to_vmt(model, ltl_spec)
        else:
            print(args.translate + " is not recognised. --translate options are 'dot' or 'nuxmv' or 'vmt'.")
    elif args.synthesise:
        if args.ltl is None and args.tlsf is None:
            raise Exception("No property specified.")

        start = time.time()
        (realiz, mm) = synthesize(program, args.ltl, args.tlsf, args.docker)
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
