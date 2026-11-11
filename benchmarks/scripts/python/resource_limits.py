"""Process deadlines and memory limits for benchmark phases."""


def run_with_timeout_and_memory_limit(f, args, timeout, max_memory_gb):
    import time
    import resource
    from multiprocessing import get_context

    if timeout == -1:
        return True, f(*args)

    # These workers accept local functions and closures, which require fork.
    context = get_context("fork")

    with context.Manager() as manager:
        result_dict = manager.dict()

        def _kill_process_tree(root_pid: int):
            try:
                import psutil

                root = psutil.Process(root_pid)
                children = root.children(recursive=True)
                for child in children:
                    try:
                        child.terminate()
                    except Exception:
                        pass
                gone, alive = psutil.wait_procs(children, timeout=0.5)
                for child in alive:
                    try:
                        child.kill()
                    except Exception:
                        pass
            except Exception:
                pass

        def target(func, func_args, shared_dict, memory_limit_gb):
            try:
                memory_bytes = int(memory_limit_gb * 1024 * 1024 * 1024)
                resource.setrlimit(resource.RLIMIT_AS, (memory_bytes, memory_bytes))
                result = func(*func_args)
                shared_dict["status"] = "success"
                shared_dict["result"] = result
            except MemoryError:
                shared_dict["status"] = "oom"
            except BrokenPipeError:
                pass
            except Exception as e:
                shared_dict["status"] = "error"
                shared_dict["result"] = str(e)

        process = context.Process(target=target, args=(f, args, result_dict, max_memory_gb))
        process.start()

        start_time = time.time()
        while time.time() - start_time < timeout:
            if not process.is_alive():
                break
            time.sleep(0.01)

        timed_out = process.is_alive()
        if timed_out:
            _kill_process_tree(process.pid)
            process.terminate()
        process.join(1.0)

        # Cleanup can make a subprocess fail before its worker is terminated.
        # Such an error is a consequence of the expired deadline.
        if timed_out:
            return False, "Timeout"

        status = result_dict.get("status", None)
        result = result_dict.get("result", None)

        if status == "success":
            return True, result
        elif status == "oom":
            return False, "Memory limit exceeded"
        elif status == "error":
            return False, result
        else:
            return False, "Timeout"
