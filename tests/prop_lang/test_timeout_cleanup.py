"""Errors induced by deadline cleanup must remain timeout results."""

import subprocess
import sys
import time
from unittest import TestCase
from unittest.mock import patch

import psutil

from prop_lang.util import run_with_timeout_and_memory_limit


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
