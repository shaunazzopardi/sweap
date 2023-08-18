#TODO

------

### In progress

1. Luca -> UI with Jupyter.
2. Luca -> With pysmt we cannot deal with integer remainder and division: 
   - Proposal: Use z3 for smt solving formulas with remainder and division; .

### Not in progress

1. Combine LTL and program files
2. Consider adding invariants to program file, to reduce transition size if we want them to be deterministic.
3. If program transitions are not deterministic then we may not get a good counterexample, since whatever transition the environment wants to choose, will have a counterexample to it in the monitor, i.e. the choice of the other non-deterministic transition  (see arbiter/program2.prog). This would probably be solved if instead of looking at the transition the monitor took, we instead look at the transition the environment wanted to take, since then the interpolation is on the state the environment wanted to be, rather than any of the other possible non-deterministic monitor states. We can do this by associated each predicate abstraction transition with the respective monitor transition, and then we can associate each env transition with a pred abstr transition, and back to monitor (maybe we get a set of con-env transitions rather than 1).
4. More examples.
5. Make the predicate abstraction incremental.
    1. Use the incremental meaning_within
    2. See if we can find an SMT solver that can keep the SMT context (?) of each transition in the previous transition,
       so that then we just need to evaluate the new information against the old context, rather than creating a totally
       new instance of the problem.