# sweap

sweap is a prototype tool that implements a symbolic approach to reactive synthesis. The setting is that of an arena defined as a symbolic automaton, possibly infinite-state, and an LTL (modulo theories) objective. The output is a controller or counterstrategy in HOA format.

Currently the only theory implemented is that of Linear Integer Arithmetic. 

`paper.pdf` contains a detailed description of the theory underlying the tool, and presents an evaluation against other similar tools. To run the evaluation run the scripts in `./benchmarks/scripts/`.

**Developers**: Shaun Azzopardi and Luca Di Stefano

**Contributors to theory**: Shaun Azzopardi, Nir Piterman, Luca Di Stefano, and Gerardo Schneider

## Installation

### Requirements

- This tool was developed and tested on Ubuntu 22.04.04 LTS.
- The tool was developed and tested with Python 3.10 (ensure you also have `pip` installed), we recommend using this version.
- The tool is distributed with several required binaries:
  - `strix` - Strix 21.0.0, https://github.com/meyerphi/strix/releases/tag/21.0.0
  - `cpa.sh` - CPAchecker 2.3, https://gitlab.com/sosy-lab/software/cpachecker/
  - `syfco` - syfco 1.1, https://github.com/reactive-systems/syfco
- Spot (https://spot.lre.epita.fr/) with Python bindings is required.
  - Some ISSY/LTL reduction paths import `spot` directly at runtime.
  - The Spot Python module must be available in the same Python environment used to run `sweap`.
- For CPAChecker:
  - Ensure you have Java 17 installed,
  - set the environment variable `JAVA' to your Java 17 executable:
    - for example, `JAVA=/usr/lib/jvm/java-17-openjdk-amd64/bin/java`
  - CPAChecker requires the mathsat5j shared library for msat:
    - This is undocumented, but we follow the instructions [here](https://groups.google.com/g/cpachecker-users/c/QxPDzTXxscU).
    - Download MathSat, https://mathsat.fbk.eu/l
    - Download `java-smt` https://github.com/sosy-lab/java-smt/tree/master
    - Download gmp from http://gmplib.org/
      - extract, `cd` to directory and run:
        - `./configure --enable-cxx --with-pic --disable-shared --enable-fat`
        - `make`
    - go to `<java-smt-dir>/lib/native/source/libmathsat5j`
    - run `./compile.sh <math-sat-dir> <gmp-dir`
    - This should generate `libmathsat5j.so`
      - Move this to somewhere on java.library.path (e.g., `/usr/lib/`), or modify `./sweap/binaries/CPAChecker-2.3-unix/scripts/cpa.sh` to include a directory containing this file to the library path, i.e. add and set `-Djava.library.path=`

- `sweap` also requires nuXmv 2.0.0, download from https://nuxmv.fbk.eu/, and add to the path or put the binary in `./binaries` (ensure the nuXmv binary is named `nuxmv`).

### Setup

- Clone the repository
- In the root directory:
- Give execution permissions to:the required binaries: `chmod -R +x ./binaries/*`
  - Install dependencies: 
  - By running `./setup.sh` (may need to run `chmod +x ./setup.sh` before)
  - OR
    - run `pip install -r ./requirements.txt`
    - Setting up pySMT:
      - Install msat for pySMT: `pysmt-install --msat`
      - Install z3 for pySMT: `pysmt-install --z3`
      - Install bdd for pySMT: `pysmt-install --bdd`
        - We experienced an error in this step sometimes, of the form:
          - `FileNotFoundError: [Errno 2] No such file or directory: '/home/<user>/.smt_solvers/bdd/repycudd-ecb03d6d231273343178f566cc4d7258dcce52b4/repycudd.py'`
        - Delete the directory `/home/<user>/.smt_solvers/bdd/` and running the command again worked for us.

- Install Spot Python bindings in the same virtual environment used for `sweap`:
  - Activate your venv first, then build/install Spot with that interpreter:
```bash
source .venv/bin/activate
cd /path/to/spot-2.14.5
make distclean || true
./configure --prefix="$VIRTUAL_ENV" PYTHON="$VIRTUAL_ENV/bin/python"
make -j"$(nproc)"
make install
```
  - Verify the binding is visible from the venv:
```bash
python -c "import spot; print(spot.__file__)"
```
  - Note: manual copying of Spot bindings from another Python installation may fail if Python ABI versions differ (e.g., `cpython-312` bindings with a Python 3.10 venv).

## Usage

### Input: Symbolic Synthesis Problems

The input to the tool is a symbolic reactive synthesis problem that specifies the arena as a symbolic automaton or program, and an LTL objective.

We describe briefly the format of this input file, starting at a high-level. You can find multiple examples in `./benchmarks/sweap`.

The input file is a text file with the following template:

```
program <name> {
    STATES {<states>}

    ENVIRONMENT EVENTS {<events>}

    CONTROLLER EVENTS {<events>}

    VALUATION {<valuation>}

    TRANSITIONS {<transitions>}

    SPECIFICATION {<ltl>}
}
```
Find below the grammar in EBNF and regex for each section:
```
<name> := [_a-zA-Z][_a-zA-Z0-9$@\_\-]*

<state> := [a-zA-Z0-9@$_-]+
<states> := <state> : init [, <state>]*

<event> := <name> 
<events> := <name> [, <name>]*

<num> := (-)?[0-9]+
<type> := (bool|int|nat|(<num>\.\.<num>))
<var> := <name>
<val> := <var> : <type> := <val>
<valuation> := (<val> [; <val>]*)?

<LIA-predicate> := <var> == <var> | <var> != <var> | <var> < <var> | <var> <= <var> | <var> > <var> | <var> >= <var>
<formula> := <var> | <LIA-predicate> | !<formula> | <formula> && <formula> | <formula> || <formula> | <formula> -> <formula>

<guard> := formula

<LIA-term> := <var> | <num> | <LIA-term> + <LIA-term> | <LIA-term> - <LIA-term> 
<assignment> := <var> := <LIA-term>

<transition> := <state> -> <state> [<guard> $ <assignments>]
<transitions> := (<transition> [, <transition>]*)?

<ltl> := <formula> | !<ltl> | <ltl> && <ltl> | <ltl> || <ltl> | <ltl> -> <ltl> | X (<formula>) | F (<formula>) | G (<formula>) | (<formula>) U (<formula>)
```

The real format is a bit less strict, e.g., the long form names for types are also parsed, `;` can be used instead of `,`, and `&` and `|` can be used instead of `&&` and `||`.

An important aspect is that we require the defined transitions to be **deterministic**. That is, we require that from every state the guards of each transition are mutually exclusive. Nonetheless, even if the program is non-deterministic, unless the `--debug` flag is used, the tool will not raise an exception. However, in this case refinement is not complete and may not succeed.

#### Example 

Below is an example problem. This essentially captures the arbiter problem, where the environment can request access to a number of resources, and the controller can grant access to each of these. The controller's objective is to eventually grant access to all the requested resources, and not more.

It defines an arbiter with two states (`q0` and `q1`), where `q0` is the initial state. 

It defines one environment events/variables (`request`) and two controller events/variables (`grant` and `finished`). 

The valuation section defines one natural variables `cnt`. 

The transitions section defines the transitions between the states based on the environment and controller events. Note at state `q0` the environment can increase the value of `cnt` by setting request to true, and force a transition to `q1` by setting `request` to false. In state `q1`, when `cnt != 0`, the controller can grant each request by setting `grant` to `true`. If the controller calls `finished` when `cnt` is `0` then the program transitions back to `q0`. At `q1` the transition function is not complete, the interpretation here is that the arena defines when the arena state transforms, any behaviour that does not activate a guard results in stuttering. Note the defined arena is deterministic.

The specification section defines the LTL formula that the controller should satisfy, namely that the controller should always eventually return to state `q0` from state `q1`.

````
program arbiter {
    STATES {
        q0 : init, q1
    }

    ENVIRONMENT EVENTS {
        request
    }

    CONTROLLER EVENTS {
        grant, finished
    }

    VALUATION {
        cnt : natural := 0;
    }

    TRANSITIONS {
        q0 -> q0 [request $ cnt := cnt + 1],
        q0 -> q1 [!request],
        q1 -> q1 [grant & cnt != 0 $ cnt := cnt - 1],
        q1 -> q0 [cnt == 0 & finished $]
    }

    SPECIFICATION {
        G(q1 -> F q0)
    }
}
````

### Output Format

The output of the tool is a controller or counterstrategy in Hanoi-Omega Automata (HOA) format v1, see https://adl.github.io/hoaf/ for documentation about this standard format.

Using HOA format allows for interoperability with other tools that rely on this standard, e.g. spot (https://spot.lre.epita.fr/), for further analysis and automata manipulation.


### Correctness

To validate the correctness of the tool we took several measures:

  - the output of the tool is model checked against the inputted problem (by default for counterstrategies, and with the `--verify_controller` flag for controllers);
  - testing (see `./tests/synthesis/test_synthesis` which checks that some synthesis problems, developed to avoid regression, are given the expected verdict); and
  - comparison of realisability results for the given benchmarks with other tools.

### Running the Tool

To run the tool on a symbolic synthesis problem, run the following command in the root directory:

```
PATH=./binaries:$PATH PYTHONPATH=./src python main.py --p <path-to-problem-file> --synthesise
```

#### Other input formats

`sweap` supports multiple input formats:

- `--p <file.prog>`:
  - Standard input format for `sweap`.
- `--issy <file.issy>`:
  - Parsed and normalised with ISSY reductions (`string_to_issy`), including formula/game reductions and Spot-based update-restriction inference where applicable.
- `--tsl <file.tsl>`:
  - Parsed as TSL/LTL modulo theories.
- `--rpg <file.rpg>`:
  - Parsed via the RPG parser and converted to the same internal model (`rpg_parsec`).

These input formats can go through the synthesis pipeline `--synthesise`. Standard one-shot enumerative finite synthesis of programs can be performed through `--finite_synthesise`.

`sweap` also provides a translation mode,`--translate`, the pipeline stops after front-end parsing and emits the requested target (`prog`, `dot`, `nuxmv`, `issy`, or `vmt`) without running synthesis.


Other flags may be useful to the interested user:

- `--dual` performs synthesis of the dual problem, i.e. flips the problem by setting the concrete controller as the abstract environment, and the concrete environment as the abstract controller, and negating the original specification. This results in an under-approximation of the arena (given it is now controlled by the controller, which is the environment in the abstract problem). This is likely to not terminate for realisable problems, but should be used to check for unrealisability.
- ``--verify_controller`` verifies that the controller satisfies the intended LTL specification in the context of the arena.
- ``--only_safety`` attempts the synthesis problem without any liveness refinements.
- ``--no_binary_enc`` attempts the synthesis problem without binary encoding of the predicates, instead of creating a new proposition for each predicate.
- ``--debug`` runs the tool in debug mode, which raises enables inline checks that verifies: 
  - determinism of the arena (i.e., that the guards of the transitions from each state are mutually exclusive);
  - correctness of abstraction refinement; and
  - correctness of certain steps in ISSY translation to sweap problems.
