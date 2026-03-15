import logging
import os

import psutil
from pysmt.environment import Environment

import config
from parsing.string_to_ltlmt import ToProgram
from parsing.string_to_ltl import string_to_ltlmt
from programs.util import reset_caches as program_util_reset_caches
from prop_lang.util import reset_caches as prop_lang_util_reset_caches
from prop_lang.util import run_with_timeout_and_memory_limit
from synthesis.synthesis import synthesize

dirname = os.path.dirname(__file__)
strix_path = str(os.path.join(dirname, "../../../binaries"))

os.environ["PATH"] = strix_path + ":" + os.environ["PATH"]


def test_synthesis():
    import csv
    import time

    dirname = os.path.dirname(__file__)
    benchmarks_dir = str(os.path.join(dirname, "../../raboniel"))
    csv_dir = os.path.join(dirname, "../../raboniel/results")
    if not os.path.exists(csv_dir):
        os.makedirs(csv_dir)
    csv_path = os.path.join(csv_dir, "synthesis_results-2Mar.csv")

    cnt = 0
    ignore = """"""

    # verifies controller
    config.Config.getConfig()._set_v_c(False)

    # Read existing results to avoid reprocessing
    processed_files = set()
    if os.path.exists(csv_path):
        with open(csv_path, "r", newline="") as csvfile:
            reader = csv.DictReader(csvfile)
            for row in reader:
                file_key = row["file"]
                processed_files.add(file_key)
        print(f"Found {len(processed_files)} already processed files.")
    else:
        # Initialize CSV file with headers if it doesn't exist
        with open(csv_path, "w", newline="") as csvfile:
            fieldnames = [
                "file",
                "realisable",
                "parse_time_seconds",
                "synthesis_time_seconds",
                "total_time_seconds",
            ]
            writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
            writer.writeheader()

    # iterate over all files in the directory and subdirectories
    for root, dirs, files in os.walk(benchmarks_dir):
        for file in files:
            if file.endswith(".tslmt") and file not in ignore:
                logdir = benchmarks_dir + "/logs/" + file + "/" + (str(time.time()))

                if not os.path.exists(logdir):
                    os.makedirs(logdir)

                config.Config.getConfig().name = file.split(".")[0]
                config.Config.getConfig()._log = logdir
                logging.basicConfig(
                    filename=(logdir + "/.log"),
                    encoding="utf-8",
                    level=logging.INFO,
                    format="%(asctime)s %(levelname)-8s %(message)s",
                    datefmt="%Y-%m-%d %H:%M:%S",
                    force=True,
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
                                config.Config.getConfig().dual
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

                                def _kill_solver_processes():
                                    proc_names = ["strix", "semml"]
                                    for proc in psutil.process_iter():
                                        if proc.name() in proc_names:
                                            proc.kill()

                                def _run_synthesis_attempt(
                                    dual_mode: bool, attempt_prog, attempt_ltl
                                ):
                                    config.Config.getConfig().dual = dual_mode
                                    attempt_success, attempt_result = (
                                        run_with_timeout_and_memory_limit(
                                            synthesize,
                                            [attempt_prog, attempt_ltl, None, -1],
                                            timeout=synthesis_timeout_seconds,
                                            max_memory_gb=50,
                                        )
                                    )
                                    _kill_solver_processes()
                                    return attempt_success, attempt_result

                                try:
                                    success, hoa = _run_synthesis_attempt(
                                        original_dual, prog, ltl
                                    )
                                    used_dual_fallback = False
                                    dual_retry_parse_failed = False

                                    if not success:
                                        dual_parse_start_time = time.time()
                                        dual_parse_success, dual_parse_res = (
                                            _run_parse_attempt(True)
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
                                                True, dual_prog, dual_ltl
                                            )
                                            used_dual_fallback = True
                                        else:
                                            dual_retry_parse_failed = True
                                            if dual_parse_res == "Timeout":
                                                result["realisable"] = "TO(parse-dual)"
                                            elif (
                                                dual_parse_res
                                                == "Memory limit exceeded"
                                            ):
                                                result["realisable"] = "OOM(parse-dual)"
                                            else:
                                                result["realisable"] = (
                                                    f"ERR(parse-dual): {dual_parse_res}"
                                                )

                                    if dual_retry_parse_failed:
                                        pass
                                    elif success:
                                        if config.Config.getConfig().dual:
                                            realisable = (
                                                not hoa.is_controller
                                                if hoa is not None
                                                else "N/A"
                                            )
                                        else:
                                            realisable = (
                                                hoa.is_controller
                                                if hoa is not None
                                                else "N/A"
                                            )
                                        if used_dual_fallback:
                                            if realisable in [True, False]:
                                                result["realisable"] = (
                                                    f"{str(realisable)} (dual)"
                                                )
                                            else:
                                                result["realisable"] = (
                                                    f"{realisable} (dual)"
                                                )
                                        else:
                                            result["realisable"] = realisable
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
                        fieldnames = [
                            "file",
                            "realisable",
                            "parse_time_seconds",
                            "synthesis_time_seconds",
                            "total_time_seconds",
                        ]
                        writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
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
    test_parsing()
