import logging
import os
import time

import psutil
from pysmt.environment import Environment

import config
from analysis.compatibility_checking.log_replay_verifier import (
    verify_wrapped_hoa_against_program,
)
from parsing.string_to_ltlmt import ToProgram
from parsing.string_to_ltl import string_to_ltlmt
from programs.util import reset_caches as program_util_reset_caches
from prop_lang.util import reset_caches as prop_lang_util_reset_caches
from prop_lang.util import run_with_timeout_and_memory_limit
from synthesis.synthesis import synthesize

dirname = os.path.dirname(__file__)
strix_path = str(os.path.join(dirname, "../../../binaries"))

os.environ["PATH"] = strix_path + ":" + os.environ["PATH"]
RESULT_FIELDNAMES = [
    "file",
    "realisable",
    "verification_10s",
    "parse_time_seconds",
    "synthesis_time_seconds",
    "total_time_seconds",
]
# Retry a failed synthesis attempt by reparsing and rerunning with fallback mode.
DUAL_FALLBACK_ENABLED = False


def test_synthesis():
    import csv
    import time

    dirname = os.path.dirname(__file__)
    benchmarks_dir = str(os.path.join(dirname, "../../raboniel"))
    csv_dir = os.path.join(dirname, "../../raboniel/results")
    if not os.path.exists(csv_dir):
        os.makedirs(csv_dir)
    csv_name = "synthesis_results-15Apr-verif2.csv"
    csv_path = os.path.join(csv_dir, csv_name)

    cnt = 0
    ignore = """"""

    # verifies controller
    config.Config.getConfig().dual = False
    print(f"TSL dual fallback enabled: {DUAL_FALLBACK_ENABLED}")

    # Read existing results to avoid reprocessing
    processed_files = set()
    if os.path.exists(csv_path):
        existing_rows = []
        with open(csv_path, "r", newline="") as csvfile:
            reader = csv.DictReader(csvfile)
            existing_fieldnames = reader.fieldnames or []
            for row in reader:
                file_key = row["file"]
                processed_files.add(file_key)
                existing_rows.append(row)
        print(f"Found {len(processed_files)} already processed files.")
        if "verification_10s" not in existing_fieldnames:
            with open(csv_path, "w", newline="") as csvfile:
                writer = csv.DictWriter(csvfile, fieldnames=RESULT_FIELDNAMES)
                writer.writeheader()
                for row in existing_rows:
                    writer.writerow(
                        {
                            field: row.get(
                                field,
                                ("N/A" if field == "verification_10s" else ""),
                            )
                            for field in RESULT_FIELDNAMES
                        }
                    )
    else:
        # Initialize CSV file with headers if it doesn't exist
        with open(csv_path, "w", newline="") as csvfile:
            writer = csv.DictWriter(csvfile, fieldnames=RESULT_FIELDNAMES)
            writer.writeheader()

    # iterate over all files in the directory and subdirectories
    for root, dirs, files in os.walk(benchmarks_dir):
        for file in files:
            if file.endswith(".tslmt") and file not in ignore:
                config.Config.getConfig().name = str(file)
                logdir = (
                    os.getcwd()
                    + "/logs/"
                    + str(file).split(".")[0]
                    + "/"
                    + (str(time.time()))
                )
                config.Config.getConfig().log = (
                    logdir + "/tsl/" + csv_name.replace(".csv", "")
                )

                if not os.path.exists(logdir):
                    os.makedirs(logdir)

                logging.basicConfig(
                    filename=(logdir + "/.log"),
                    encoding="utf-8",
                    level=logging.INFO,
                    format="%(asctime)s %(levelname)-8s %(message)s",
                    datefmt="%Y-%m-%d %H:%M:%S",
                    force=True,
                )
                conf_snapshot = config.Config.getConfig()
                initial_replay_input_args = {
                    "program": None,
                    "tsl": os.path.join(root, file),
                    "rpg": None,
                    "issy": None,
                    "translate": None,
                    "synthesise": -1,
                    "finite_synthesise": bool(
                        getattr(conf_snapshot, "finite_synthesis", False)
                    ),
                    "model_check": None,
                    "out_dot": None,
                    "debug": bool(conf_snapshot.debug),
                    "log": conf_snapshot.log,
                    "tlsf": None,
                    "synthesis_backend": conf_snapshot.backend,
                    "abstraction_backend": conf_snapshot.abstraction_backend,
                    "verify_controller": bool(conf_snapshot.verify_controller),
                    "workers": getattr(conf_snapshot, "workers", None),
                    "synthesis_memory_limit_mb": getattr(
                        conf_snapshot, "synthesis_memory_limit_mb", None
                    ),
                    "lazy": getattr(conf_snapshot, "lazy", None),
                    "only_safety": getattr(conf_snapshot, "only_safety", None),
                    "no_binary_enc": bool(conf_snapshot.no_binary_enc),
                    "dual": bool(conf_snapshot.dual),
                }
                logging.info("Input args: %s", initial_replay_input_args)
                logging.info(
                    "Config args: %s",
                    {
                        "dual": bool(conf_snapshot.dual),
                        "verify_controller": bool(conf_snapshot.verify_controller),
                        "backend": conf_snapshot.backend,
                        "abstraction_backend": conf_snapshot.abstraction_backend,
                        "workers": getattr(conf_snapshot, "workers", None),
                        "no_binary_enc": bool(conf_snapshot.no_binary_enc),
                    },
                )

                import gc

                gc.collect()
                program_util_reset_caches()
                prop_lang_util_reset_caches()

                file_key = file

                # Skip if already processed
                if file_key in processed_files:
                    print(f"Skipping {file} from {root} (already processed).")
                    continue

                file_path = os.path.join(root, file)
                with open(file_path, "r") as f:
                    content = f.read()
                    print(f"Parsing {file} from {root}.")

                    result = {
                        "file": file,
                        "realisable": "N/A",
                        "verification_10s": "N/A",
                        "parse_time_seconds": 0.0,
                        "synthesis_time_seconds": 0.0,
                        "total_time_seconds": 0.0,
                    }

                    total_start_time = time.time()
                    synthesis_start_time = None

                    # Time the parsing step
                    with Environment() as env:
                        parse_start_time = time.time()
                        try:

                            def _parse_tsl_content(tsl_text: str, tsl_file: str):
                                parsed = string_to_ltlmt(tsl_text)
                                return ToProgram().ltlmt2prog(parsed, tsl_file)

                            def _run_parse_attempt(dual_mode: bool):
                                config.Config.getConfig().dual = dual_mode
                                return run_with_timeout_and_memory_limit(
                                    _parse_tsl_content,
                                    [content, file],
                                    timeout=10,
                                    max_memory_gb=50,
                                )

                            success, res = _run_parse_attempt(
                                config.Config.getConfig().dual,
                            )

                            gc.collect()
                            program_util_reset_caches()
                            prop_lang_util_reset_caches()

                            parse_end_time = time.time()
                            result["parse_time_seconds"] = round(
                                parse_end_time - parse_start_time, 3
                            )

                            if not success:
                                if res == "Timeout":
                                    result["realisable"] = "TO(parse)"
                                elif res == "Memory limit exceeded":
                                    result["realisable"] = "OOM(parse)"
                                else:
                                    result["realisable"] = f"ERR(parse): {res}"

                            if success:
                                prog, ltl = res
                                synthesis_start_time = time.time()
                                synthesis_timeout_seconds = 50
                                original_dual = config.Config.getConfig().dual

                                def _fallback_mode(dual_mode: bool):
                                    return not dual_mode

                                def _to_original_realisable(
                                    solver_realisable: bool,
                                ) -> bool:
                                    return solver_realisable

                                def _kill_solver_processes():
                                    proc_names = ["strix", "semml"]
                                    for proc in psutil.process_iter():
                                        if proc.name() in proc_names:
                                            proc.kill()

                                def _run_synthesis_attempt(
                                    dual_mode: bool,
                                    attempt_prog,
                                    attempt_ltl,
                                    timeout_seconds=synthesis_timeout_seconds,
                                    verify_controller=False,
                                ):
                                    conf = config.Config.getConfig()
                                    original_verify_controller = conf.verify_controller
                                    conf.dual = dual_mode
                                    if verify_controller is not None:
                                        conf.verify_controller = verify_controller

                                    replay_input_args = {
                                        "program": None,
                                        "tsl": file_path,
                                        "rpg": None,
                                        "issy": None,
                                        "translate": None,
                                        "synthesise": -1,
                                        "finite_synthesise": bool(
                                            getattr(conf, "finite_synthesis", False)
                                        ),
                                        "model_check": None,
                                        "out_dot": None,
                                        "debug": bool(conf.debug),
                                        "log": conf.log,
                                        "tlsf": None,
                                        "synthesis_backend": conf.backend,
                                        "abstraction_backend": conf.abstraction_backend,
                                        "verify_controller": bool(
                                            verify_controller
                                            if verify_controller is not None
                                            else conf.verify_controller
                                        ),
                                        "workers": getattr(conf, "workers", None),
                                        "synthesis_memory_limit_mb": getattr(
                                            conf, "synthesis_memory_limit_mb", None
                                        ),
                                        "lazy": getattr(conf, "lazy", None),
                                        "only_safety": getattr(
                                            conf, "only_safety", None
                                        ),
                                        "no_binary_enc": bool(conf.no_binary_enc),
                                        "dual": bool(dual_mode),
                                    }
                                    logging.info("Input args: %s", replay_input_args)
                                    try:
                                        attempt_success, attempt_result = (
                                            run_with_timeout_and_memory_limit(
                                                synthesize,
                                                [attempt_prog, attempt_ltl, None, -1],
                                                timeout=timeout_seconds,
                                                max_memory_gb=50,
                                            )
                                        )
                                    finally:
                                        _kill_solver_processes()
                                        conf.verify_controller = (
                                            original_verify_controller
                                        )
                                    return attempt_success, attempt_result

                                def _verify_wrapped_hoa(
                                    verify_prog,
                                    verify_ltl,
                                    wrapped_hoa,
                                ):
                                    conf = config.Config.getConfig()
                                    original_log = conf.log
                                    original_verify = conf.verify_controller
                                    try:
                                        conf.log = None
                                        conf.verify_controller = False
                                        verify_wrapped_hoa_against_program(
                                            verify_prog,
                                            verify_ltl,
                                            None,
                                            wrapped_hoa,
                                        )
                                        return True
                                    finally:
                                        conf.log = original_log
                                        conf.verify_controller = original_verify

                                try:
                                    success, hoa = _run_synthesis_attempt(
                                        original_dual, prog, ltl
                                    )
                                    used_dual_fallback = False
                                    dual_retry_parse_failed = False
                                    verification_prog = prog
                                    verification_ltl = ltl

                                    if (
                                        not success
                                        and DUAL_FALLBACK_ENABLED
                                        and (not used_dual_fallback)
                                    ):
                                        fallback_dual = _fallback_mode(original_dual)
                                        dual_parse_start_time = time.time()
                                        dual_parse_success, dual_parse_res = (
                                            _run_parse_attempt(fallback_dual)
                                        )
                                        dual_parse_end_time = time.time()
                                        result["parse_time_seconds"] = round(
                                            result["parse_time_seconds"]
                                            + (
                                                dual_parse_end_time
                                                - dual_parse_start_time
                                            ),
                                            3,
                                        )

                                        if dual_parse_success:
                                            dual_prog, dual_ltl = dual_parse_res
                                            success, hoa = _run_synthesis_attempt(
                                                fallback_dual,
                                                dual_prog,
                                                dual_ltl,
                                            )
                                            verification_prog = dual_prog
                                            verification_ltl = dual_ltl
                                            used_dual_fallback = True
                                        else:
                                            dual_retry_parse_failed = True
                                            if dual_parse_res == "Timeout":
                                                result["realisable"] = (
                                                    "TO(parse-dual-alt)"
                                                )
                                            elif (
                                                dual_parse_res
                                                == "Memory limit exceeded"
                                            ):
                                                result["realisable"] = (
                                                    "OOM(parse-dual-alt)"
                                                )
                                            else:
                                                result["realisable"] = (
                                                    f"ERR(parse-dual-alt): {dual_parse_res}"
                                                )

                                    if dual_retry_parse_failed:
                                        pass
                                    elif success:
                                        realisable = (
                                            _to_original_realisable(hoa.realisable)
                                            if hoa is not None
                                            else "N/A"
                                        )
                                        if used_dual_fallback:
                                            if realisable in [True, False]:
                                                result["realisable"] = (
                                                    f"{str(realisable)} (dual-alt)"
                                                )
                                            else:
                                                result["realisable"] = (
                                                    f"{realisable} (dual-alt)"
                                                )
                                        else:
                                            result["realisable"] = realisable
                                        if hoa is not None:
                                            (
                                                verification_success,
                                                verification_result,
                                            ) = run_with_timeout_and_memory_limit(
                                                _verify_wrapped_hoa,
                                                [
                                                    verification_prog,
                                                    verification_ltl,
                                                    hoa,
                                                ],
                                                timeout=10,
                                                max_memory_gb=50,
                                            )
                                            if verification_success:
                                                result["verification_10s"] = True
                                            elif (
                                                verification_result
                                                == "Memory limit exceeded"
                                            ):
                                                result["verification_10s"] = "OOM"
                                            elif verification_result == "Timeout":
                                                result["verification_10s"] = "TO"
                                            elif (
                                                "does not enforce the required LTL property"
                                                in str(verification_result)
                                            ):
                                                result["verification_10s"] = False
                                            else:
                                                result["verification_10s"] = (
                                                    f"ERR(verif): {verification_result}"
                                                )
                                    else:
                                        if hoa == "Memory limit exceeded":
                                            result["realisable"] = "OOM"
                                        elif hoa == "Timeout":
                                            result["realisable"] = "TO"
                                        else:
                                            result["realisable"] = f"ERR: {hoa}"
                                finally:
                                    config.Config.getConfig().dual = original_dual
                        except Exception as e:
                            if "Could not find a controller" not in str(e):
                                print(f"Error parsing {file}: {e}")
                                result["realisable"] = f"Error: {str(e)}"
                            else:
                                raise e
                        synthesis_end_time = time.time()
                        result["synthesis_time_seconds"] = round(
                            (
                                synthesis_end_time - synthesis_start_time
                                if synthesis_start_time
                                else -1
                            ),
                            3,
                        )

                    total_end_time = time.time()
                    result["total_time_seconds"] = round(
                        total_end_time - total_start_time, 3
                    )

                    # Append result to CSV file immediately
                    with open(csv_path, "a", newline="") as csvfile:
                        writer = csv.DictWriter(csvfile, fieldnames=RESULT_FIELDNAMES)
                        writer.writerow(result)

                    print(
                        f"Result for {file}: Realisable={result['realisable']}, Parse: {result['parse_time_seconds']}s, Synthesis: {result['synthesis_time_seconds']}s, Total: {result['total_time_seconds']}s"
                    )

    print(f"Finished parsing with {cnt} errors.")
    print(f"Results written to {csv_path}")


def test_parsing():
    config.Config.getConfig().debug = True

    dirname = os.path.dirname(__file__)
    benchmarks_dir = str(os.path.join(dirname, "../../raboniel/"))

    cnt = 0
    # iterate over all files in the directory
    for file in os.listdir(benchmarks_dir):
        import gc

        gc.collect()
        program_util_reset_caches()
        prop_lang_util_reset_caches()
        if file.endswith(".tslmt"):
            with open(os.path.join(benchmarks_dir, file), "r") as f:
                content = f.read()
                with Environment() as env:
                    try:
                        print("parsing " + file)
                        f = string_to_ltlmt(content)
                    except Exception as e:
                        print(f"Error parsing {file}: {e}")
                        raise (e)
                    ToProgram().ltlmt2prog(f, file)
    print(f"Finished parsing with {cnt} errors.")


if __name__ == "__main__":
    start = time.time()
    test_parsing()
    end = time.time()
    print(f"Completed in {round(end - start, 3)} seconds.")
