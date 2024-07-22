# sweap

sweap is a prototype tool that implements a symbolic approach to reactive synthesis. The setting is that of an arena defined as a symbolic automaton, possibly infinite-state, and an LTL (modulo theories) objective. The output is a controller or counterstrategy in HOA format.

Currently the only theory implemented is that of Linear Integer Arithmetic. 

## Installation

### Requirements

- This tool was developed and tested on Ubuntu 22.04.04 LTS.
- The tool was developed and tested with Python 3.10 (ensure you also have `pip` installed), we recommend using this version.
- The tool is distributed with several required binaries:
  - `strix` - Strix 21.0.0, https://github.com/meyerphi/strix/releases/tag/21.0.0
  - `nuxmv` - nuXmv 2.0.0,  https://nuxmv.fbk.eu/
  - `cpa.sh` - CPAchecker 2.3, https://gitlab.com/sosy-lab/software/cpachecker/
  - `syfco` - syfco 1.1, https://github.com/reactive-systems/syfco
- For CPAChecker:
  - Ensure you have Java 17 installed,
  - set the environment variable `JAVA' to your Java 17 executable:
    - for example, `JAVA=/usr/lib/jvm/java-17-openjdk-amd64/bin/java`

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

## Usage

### Symbolic Synthesis Problems

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

#### Example 

Below is an example problem. This essentially captures the arbiter problem, where the environment can request access to a number of resources, and the controller can grant access to each of these. The controller's objective is to eventually grant access to all the requested resources, and not more.

It defines an arbiter with two states (`q0` and `q1`), where `q0` is the initial state. 

It defines one environment events/variables (`request`) and two controller events/variables (`grant` and `finished`). 

The valuation section defines one natural variables `cnt`. 

The transitions section defines the transitions between the states based on the environment and controller events. Note at state `q0` the environment can increase the value of `cnt` by setting request to true, and force a transition to `q1` by setting `request` to false. In state `q1` the controller can grant each request by setting `grant` to `true`. If the controller calls `finished` when `cnt` is `0` then the program transitions back to `q0`. 

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
        q1 -> q1 [grant $ cnt := cnt - 1],
        q1 -> q0 [cnt == 0 & finished $]
    }

    SPECIFICATION {
        G(q1 -> F q0)
    }
}
````

### Running the Tool

To run the tool on a symbolic synthesis problem, run the following command:

```
PATH=./binaries:$PATH python main.py --p <path-to-problem-file> --synthesise
```

If you want to run the tool with acceleration (initially identifying relevant ranking refinements from predicates in the problem), add the `--accelerate` flag: 


```
PATH=./binaries:$PATH python main.py --p <path-to-problem-file> --synthesise --accelerate
```

For advanced flags run `main.py` with the `--h` flag.