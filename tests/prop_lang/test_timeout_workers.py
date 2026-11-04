import multiprocessing
import time
import unittest

from prop_lang.util import (
    run_with_timeout,
    run_with_timeout_and_memory_limit,
    run_with_timeout_pickled,
)


class TestTimeoutWorkers(unittest.TestCase):
    def test_local_callables_with_forkserver_default(self):
        previous_method = multiprocessing.get_start_method()
        multiprocessing.set_start_method("forkserver", force=True)
        try:
            for runner in (
                run_with_timeout,
                run_with_timeout_pickled,
                lambda f, args, timeout: run_with_timeout_and_memory_limit(
                    f, args, timeout, 50
                ),
            ):
                with self.subTest(runner=runner):
                    self.assertEqual(runner(lambda x: x * 2, [5], 2), (True, 10))
                    self.assertFalse(runner(lambda: time.sleep(5), [], 0.05)[0])
            self.assertEqual(multiprocessing.get_start_method(), "forkserver")
        finally:
            multiprocessing.set_start_method(previous_method, force=True)

    def test_worker_exception(self):
        def fail():
            raise ValueError("worker failure")

        self.assertEqual(
            run_with_timeout_and_memory_limit(fail, [], 2, 50),
            (False, "worker failure"),
        )
