# need function for env loop refinement
# need function for con loop refinement
from analysis.abstraction.interface.predicate_abstraction import PredicateAbstraction


def structural_refinement(predicate_abstraction: PredicateAbstraction,
                          terminating_loop,
                          entry_condition,
                          exit_condition,
                          symbol_table):
    ## TODO this will encode the loop
    # option 1: action-based encoding, however will miss sequence between con and env combined transitions,
    #           without new actions to combine them; would need an adhoc implementation for the effects abstraction,
    #           or modifying how we deal with transition predicates in the ltl abstraction

    # option 2: as the old one; transform the program to structurally separate the terminating loop from the rest of
    #           the program; would have the redo the predicate abstraction for all the previous predicates on the new
    #           program; or modify the abstraction to deal with predicates that can also talk about control states
    pass