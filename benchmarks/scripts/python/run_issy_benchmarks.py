import os

from pysmt.environment import Environment

import config
from parsing.string_to_issy import issy_parser, string_to_issy
from parsing.string_to_rpg import rpg_parsec
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
    benchmarks_dir = str(os.path.join(dirname, "../../issy"))
    csv_dir = os.path.join(dirname, "../../issy/results")
    if not os.path.exists(csv_dir):
        os.makedirs(csv_dir)
    csv_path = os.path.join(csv_dir, "synthesis_results.csv")

    cnt = 0
    ignore = """"""

    # verifies controller
    config.Config.getConfig()._set_v_c(True)
    config.Config.getConfig().backend = "semml"
    config.Config.getConfig().dual = False

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
            if file.endswith(".issy") and file not in ignore:
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
                            success, res = run_with_timeout_and_memory_limit(
                                string_to_issy,
                                [content, file],
                                timeout=40,
                                max_memory_gb=50,
                            )

                            parse_end_time = time.time()
                            result["parse_time_seconds"] = round(
                                parse_end_time - parse_start_time, 3
                            )
                            if not success:
                                raise Exception(res)
                            if success:
                                prog, ltl = res
                                # Time the synthesis step
                                # Time the synthesis step
                                synthesis_start_time = time.time()

                                success, hoa = run_with_timeout_and_memory_limit(
                                    synthesize,
                                    [prog, ltl, None, -1],
                                    timeout=40,
                                    max_memory_gb=50,
                                )
                                if success:
                                    if config.Config.getConfig().dual:
                                        result["realisable"] = (
                                            not hoa.is_controller
                                            if hoa is not None
                                            else "N/A"
                                        )
                                    else:
                                        result["realisable"] = (
                                            hoa.is_controller
                                            if hoa is not None
                                            else "N/A"
                                        )
                                else:
                                    # Handle timeout or OOM
                                    if hoa == "Memory limit exceeded":
                                        result["realisable"] = "OOM"
                                    elif hoa == "Timeout":
                                        result["realisable"] = "TO"
                                    else:
                                        result["realisable"] = f"ERR: {hoa}"
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
    dirname = os.path.dirname(__file__)
    benchmarks_dir = str(os.path.join(dirname, "../../rpgsolve/"))

    cnt = 0
    # iterate over all files in the directory
    for file in os.listdir(benchmarks_dir):
        if file.endswith(".rpg"):
            with open(os.path.join(benchmarks_dir, file), "r") as f:
                content = f.read()
                with Environment() as env:
                    print("Parsing " + file)
                    f = string_to_issy(content, "name")
                    print("Parsed " + file)
    print(f"Finished parsing with {cnt} errors.")


if __name__ == "__main__":
    test_synthesis()
