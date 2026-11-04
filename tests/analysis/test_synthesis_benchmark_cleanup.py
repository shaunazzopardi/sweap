from contextlib import contextmanager
from unittest import TestCase
from unittest.mock import Mock, patch

import psutil

from benchmarks.scripts.python.run_benchmarks import kill_solver_processes


@contextmanager
def solver_processes(processes):
    # Cleanup may enumerate all processes or only this runner's descendants.
    # Keep the exception-handling tests independent of that discovery policy.
    with patch(
        "benchmarks.scripts.python.run_benchmarks.psutil.process_iter",
        return_value=processes,
    ), patch(
        "benchmarks.scripts.python.run_benchmarks.psutil.Process.children",
        return_value=processes,
    ):
        yield


class TestSolverCleanup(TestCase):
    def test_process_exiting_during_name_lookup_does_not_abort_cleanup(self):
        vanished = Mock()
        vanished.name.side_effect = psutil.NoSuchProcess(1070188, name="bash")
        solver = Mock()
        solver.name.return_value = "strix"
        other = Mock()
        other.name.return_value = "bash"
        with solver_processes([vanished, other, solver]):
            kill_solver_processes()
        vanished.kill.assert_not_called()
        other.kill.assert_not_called()
        solver.kill.assert_called_once_with()

    def test_process_errors_during_kill_do_not_abort_remaining_cleanup(self):
        for error in (psutil.NoSuchProcess(123), psutil.AccessDenied(123)):
            with self.subTest(error=error):
                failed = Mock()
                failed.name.return_value = "semml"
                failed.kill.side_effect = error
                solver = Mock()
                solver.name.return_value = "strix"
                with solver_processes([failed, solver]):
                    kill_solver_processes()
                solver.kill.assert_called_once_with()

    def test_access_denied_during_name_lookup_is_ignored(self):
        denied = Mock()
        denied.name.side_effect = psutil.AccessDenied(123)
        with solver_processes([denied]):
            kill_solver_processes()
        denied.kill.assert_not_called()
