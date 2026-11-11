import logging
import os
import re
import resource
import signal
import subprocess
import config

from tempfile import NamedTemporaryFile
from synthesis.ltl.ltl_synthesis_problem import LTLSynthesisProblem
from synthesis.machines.wrapped_hoa import WrappedHOA

dirname = os.path.dirname(__file__)
strix_path = str(os.path.join(dirname, "../../../binaries/strix_tlsf_file.sh"))
semml_path = str(os.path.join(dirname, "../../../binaries/semml/semml.py"))
semml_py_path = str(os.path.join(dirname, "../../../binaries/semml/venv/bin/python"))


def _run_backend(
    cmd: list[str],
    env: dict[str, str],
    timeout_s: int | None,
    memory_limit_mb: int | None,
) -> tuple[int, str]:
    preexec_fn = None
    if memory_limit_mb is not None and memory_limit_mb > 0:
        memory_bytes = int(memory_limit_mb * 1024 * 1024)

        def _set_mem_limit():
            resource.setrlimit(resource.RLIMIT_AS, (memory_bytes, memory_bytes))

        preexec_fn = _set_mem_limit

    process = subprocess.Popen(
        cmd,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=False,
        env=env,
        start_new_session=True,
        preexec_fn=preexec_fn,
    )
    timed_out = False
    try:
        out, _ = process.communicate(timeout=timeout_s)
    except subprocess.TimeoutExpired:
        timed_out = True
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except Exception:
            process.kill()
        out, _ = process.communicate()

    if out is None:
        out = b""

    return_code = 124 if timed_out else process.returncode
    return return_code, out.decode("utf-8", errors="replace")


def _extract_status_and_hoa(raw_output: str) -> tuple[str, str, str]:
    lines = raw_output.splitlines()
    ansi_escape = re.compile(r"\x1B\[[0-?]*[ -/]*[@-~]")

    status = None
    status_idx = -1
    status_re = re.compile(r"\b(REALIZABLE|UNREALIZABLE)\b", flags=re.IGNORECASE)
    for i, line in enumerate(lines):
        stripped = ansi_escape.sub("", line).strip()
        m = status_re.search(stripped)
        if m is not None:
            status = m.group(1).upper()
            status_idx = i
            break

    if status is None:
        raise Exception("OOM or TO or error.\n\n" + raw_output)

    hoa_start_idx = -1
    for i in range(status_idx + 1, len(lines)):
        if lines[i].strip().startswith("HOA:"):
            hoa_start_idx = i
            break

    # Fallback: some backends may print only the HOA body after the status.
    if hoa_start_idx == -1:
        for i in range(status_idx + 1, len(lines)):
            if lines[i].strip() != "":
                hoa_start_idx = i
                break

    if hoa_start_idx == -1:
        raise Exception("Finite synthesis engine did not return an HOA block.")

    hoa_lines = []
    for i in range(hoa_start_idx, len(lines)):
        hoa_lines.append(lines[i])
        if lines[i].strip() == "--END--":
            break

    hoa = "\n".join(hoa_lines)
    cleaned_output = status + "\n" + hoa
    return status, hoa, cleaned_output


def ltl_synthesis(synthesis_problem: LTLSynthesisProblem, symbol_table) -> WrappedHOA:
    try:
        logging.info(synthesis_problem.tlsf)
        with NamedTemporaryFile("w", suffix=".tlsf", delete=False) as tmp:
            tmp.write(synthesis_problem.tlsf)
            tmp.close()

            backend = config.Config.getConfig().backend
            mem_limit_mb = config.Config.getConfig().synthesis_memory_limit_mb
            run_env = os.environ.copy()
            timeout_s = None
            if backend == "strix":
                cmd = [strix_path, tmp.name, "-m", "both", "--onthefly", "none"]
            elif backend == "semml":
                cmd = [semml_path, "--tlsf", tmp.name]
                if os.path.exists(semml_py_path):
                    cmd = [semml_py_path] + cmd

                # If synthesis memory limit is set, also cap JVM heap.
                if mem_limit_mb is not None and mem_limit_mb > 0:
                    heap_opt = f"-Xmx{mem_limit_mb}m"
                    current_java_opts = run_env.get("JAVA_TOOL_OPTIONS", "").strip()
                    if heap_opt not in current_java_opts.split():
                        run_env["JAVA_TOOL_OPTIONS"] = (
                            current_java_opts + " " + heap_opt
                        ).strip()

                # Optional backend timeout override (seconds).
                # 0 or unset => no timeout at this layer.
                timeout_raw = run_env.get("SWEAP_SYNTH_BACKEND_TIMEOUT_SEC", "0")
                try:
                    timeout_val = int(timeout_raw)
                except ValueError:
                    timeout_val = 0
                timeout_s = timeout_val if timeout_val > 0 else None
            else:
                raise Exception("Unrecognised synthesis backend " + str(backend))

            try:
                so = _run_backend(cmd, run_env, timeout_s, mem_limit_mb)
                raw_output: str = so[1]
                logging.info(raw_output)
                if so[0] == 124:
                    raise Exception(
                        "Timeout: finite synthesis backend exceeded timeout."
                    )
                real, hoa, output = _extract_status_and_hoa(raw_output)
            except Exception as err:
                logging.info(err)
                if "Killed" in str(err):
                    raise Exception(
                        "OutOfMemory: Finite synthesis engine ran out of memory."
                    )
                else:
                    raise err

            if "UNREALIZABLE" in real:
                logging.info(
                    "\nINFO: Finite synthesis engine thinks the current abstract problem is unrealisable! I will check..\n"
                )
                return WrappedHOA(hoa, False, synthesis_problem, symbol_table)
            elif "REALIZABLE" in real:
                logging.info(
                    "\nINFO: Finite synthesis engine determines the current abstract problem realisable!\n"
                )
                return WrappedHOA(hoa, True, synthesis_problem, symbol_table)
            else:
                logging.info("\n".join(synthesis_problem.tlsf))
                logging.info(output)
                if "java.lang.OutOfMemoryError" in output:
                    raise Exception(
                        "OutOfMemory: Finite synthesis engine ran out of memory."
                    )
                raise Exception(
                    "Finite synthesis engine not returning appropriate value.\n\n"
                    + " ".join(cmd)
                    + "\n\n"
                    + output
                    + "\n\n"
                    + synthesis_problem.tlsf
                )
    except Exception as err:
        raise err
