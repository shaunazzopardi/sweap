# Replication instructions

## Step 1. Memory limit

Set a memory limit of 16 Gib by running

```sh
ulimit -v 16777216
```

## Step 2. Run the experiments

Experiments are executed through `make`. Example invocations:

```sh
make raboniel   # Runs a single tool
make            # Alias for "make all", runs all tool except temos
make everything # Runs all tools
```

We only support GNU Make. 

This will generate, for every benchmark under `benchmarks/<tool>`,
a corresponding log file `<bench-name>.<tool-name>.log`.

The shortnames for each tool we use are:
```
raboniel rpgsolve rpgsolve-syn rpg-stela sweap sweap-noacc temos
```

Notice that running with the default timeout (1200 seconds) will take
a _long_ time. We suggest overriding the timeout value as follows:

```sh
make TIMEOUT=300  # i.e., 5 minutes
```

Afterwards, one can delete the logs for all experiments that timed out by
running

```sh
make clean-timeouts
```

(Type `y[Enter]` at the confirmation prompt). This allows to re-run
`make` with a different timeout without retrying the experiments that
already terminated.

## Step 3. Tabulate the results

Invoke

```sh
benchmarks/scripts/gen_csv.py benchmarks
```

The script will tabulate in CSV format all results found in the directory
passed as its argument (`benchmarks`, in this case). It will report a unique
id, the name of the benchmark, and a numeric value for each tool.

A value of `1` denotes that the benchmark was not run on that tool. A value of
`2` indicates that the tool encountered an error (typically OOM, but more
information may be found in the log files). All other values indicate the
experiment's running time in milliseconds.

For the table in Appendix D3, invoke

```sh
benchmarks/scripts/appendix_table.py benchmarks
```

This will tabulate (again, in CSV) the number of state and transition
predicates used in the initial abstraction, the number and kind of refinements
applied, and the number of (state/transition) predicates in the final
abstraction (i.e., before either solution or timeout/OOM).

We are aware that the contents of this CSV may differ from those in our
manuscript, especially for experiments that time out. A faster machine than
ours may still time out, but perform more refinement and thus add a higher
number of predicates to the abstraction.

