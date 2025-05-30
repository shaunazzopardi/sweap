# Replication instructions

## Step 1. Memory limit

Set a memory limit of 16 Gib by running

```sh
ulimit -v 16777216
```

## Step 2. Run the experiments

Experiments are executed through `make`. We only support GNU Make. 
Example invocations:

```sh
make raboniel   # Runs a single tool
make            # Alias for "make all", runs all tool except temos
make everything # Runs all tools
```

This will generate, for every benchmark under `benchmarks/<tool>`,
a corresponding log file `<bench-name>.<tool-name>.log`.

The shortnames for each tool we use are:
```
raboniel rpgsolve rpgsolve-syn rpg-stela sweap sweap-noacc temos
```

Notice that running with the default timeout (1200 seconds) will take
a _long_ time. To set a custom timeout, invoke `make` as follows:

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

We do *not* recommend running the tools in parallel. In particular, we do not
yet support running 2 or more instances of `sweap` simultaneously.
Users with a powerful machine who want to speed things up may try running the
recipes for *other* tools with `make -j2`, but we cannot guarantee that this
will always work.

## Step 3. Tabulate the results

Invoke `make tables`.  Internally this calls 

```sh
benchmarks/scripts/process_logs.py benchmarks
```

The script will tabulate all results found in the directory passed as its
argument (`benchmarks`, in this case). Results are stored in
`benchmarks/results` in `.tex` format. For convenience, we also record some
results into a `results.csv` CSV file.

The CSV file contains a line for each benchmark and a column for each tool.
Columns have the following semantics. A value of `0` denotes that the benchmark
was not run on that tool. A value of `1` indicates that the tool encountered an
error (typically OOM, but more information may be found in the corresponding log
files). All other positive values indicate the experiment's running time in
milliseconds; values greater than 1200000 (i.e., 20 minutes) denote a timeout.
A negative value indicates that the tool terminated with an incorrect verdict.
In this case, the absolute value of the result indicates the runtime.

To generate all plots in the paper and appendix, invoke `make plots`.
Plots will also be stored in `benchmarks/results`

We are aware that the results may differ from those in our manuscript,
especially for experiments that time out. A faster machine than ours may still
time out, but perform more refinements and thus add a higher number of
predicates to the abstraction.

## Appendix. System configuration

We applied the following changes to our OS, to make performance more uniform
(and typically better). We ran these commands on Ubuntu 22.04 but similar
ones should be available on most Linux OSs.
**Some of these operations may require superuser privileges.**

```bash
# Force OS to only swap when memory is full
$ sysctl vm.swappiness=0
# Force a high-performance frequency governor on all CPU cores
$ for ((i=0;i<$(nproc);i++)); do sudo cpufreq-set -c $i -r -g performance; done
# Disable simultaneous multithreading (Hyper-Threading)
$ echo off > /sys/devices/system/cpu/smt/control
```
