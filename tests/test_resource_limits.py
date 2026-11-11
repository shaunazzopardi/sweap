"""Errors induced by deadline cleanup must remain timeout results."""

import multiprocessing
import subprocess
import sys
import time
from unittest import TestCase
from unittest.mock import patch

import psutil

from benchmarks.scripts.python.resource_limits import run_with_timeout_and_memory_limit


def subprocess_then_error():
    completed = subprocess.run([sys.executable, "-c", "import time; time.sleep(30)"])
    raise RuntimeError(f"subprocess exited with {completed.returncode}")


def ordinary_error():
    raise RuntimeError("failed before the deadline")


class TestTimeoutCleanup(TestCase):
    def test_cleanup_error_does_not_replace_timeout(self):
        wait = psutil.wait_procs

        def allow_worker_to_report_cleanup_error(processes, timeout):
            result = wait(processes, timeout=timeout)
            # Keep cleanup active long enough for the worker to report the
            # subprocess's SIGTERM exit, reproducing the CPAchecker race.
            time.sleep(0.2)
            return result

        with patch("psutil.wait_procs", side_effect=allow_worker_to_report_cleanup_error):
            result = run_with_timeout_and_memory_limit(subprocess_then_error, [], 0.3, 50)
        self.assertEqual((False, "Timeout"), result)

    def test_real_error_before_deadline_is_preserved(self):
        result = run_with_timeout_and_memory_limit(ordinary_error, [], 2, 50)
        self.assertEqual((False, "failed before the deadline"), result)


    def test_local_callable_with_forkserver_default(self):
        previous_method = multiprocessing.get_start_method()
        multiprocessing.set_start_method("forkserver", force=True)
        try:
            self.assertEqual(
                run_with_timeout_and_memory_limit(lambda x: x * 2, [5], 2, 50),
                (True, 10),
            )
            self.assertEqual(
                run_with_timeout_and_memory_limit(lambda: time.sleep(5), [], 0.05, 50),
                (False, "Timeout"),
            )
            self.assertEqual(multiprocessing.get_start_method(), "forkserver")
        finally:
            multiprocessing.set_start_method(previous_method, force=True)
