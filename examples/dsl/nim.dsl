// The game of Nim (https://en.wikipedia.org/wiki/Nim)

// In this version the player taking the last item wins,
// we can easily switch that by changing some assumes to asserts and vice versa.
int row0 := 1;
int row1 := 3;
int row2 := 5;
int row3 := 7;

enum row { ZERO, ONE, TWO, THREE };

row chosenRow := ZERO;

// Whose turn is it?
bool envTurn := true;
// Has the current player chosen a row already?
bool hasChosen := false;

// First, choose a non-empty row and remove 1 item.
method extern envChoose (row choice) {
    assume(envTurn && !hasChosen);
    assume(choice == ZERO -> row0 > 0);
    assume(choice == ONE -> row1 > 0);
    assume(choice == TWO -> row2 > 0);
    assume(choice == THREE -> row3 > 0);
    // If the board is cleared, controller loses
    assert(row0 + row1 + row2 + row3 > 1);
    
    if (choice == ZERO) {row0--; }
    if (choice == ONE) { row1--; }
    if (choice == TWO) { row2--; }
    if (choice == THREE) { row3--; }
    chosenRow := choice;
    hasChosen := true;
}

// After a row has been chosen, environment can keep removing items...
method extern envRemoveNext () {
    assume(envTurn && hasChosen);
    assume(chosenRow == ZERO -> row0 > 0);
    assume(chosenRow == ONE -> row1 > 0);
    assume(chosenRow == TWO -> row2 > 0);
    assume(chosenRow == THREE -> row3 > 0);
    // If the board is cleared, environment wins
    assert(row0 + row1 + row2 + row3 > 1);

    if (chosenRow == ZERO) { row0--; }
    if (chosenRow == ONE) { row1--; }
    if (chosenRow == TWO) { row2--; }
    if (chosenRow == THREE) { row3--; }    
}

// ... or pass
method extern envPass() {
    assume(envTurn && hasChosen);
    envTurn := false;
    hasChosen := false;
}

// Same for the controller, more or less
method intern conChoose (row choice) {
    assert(!envTurn && !hasChosen);
    assert(chosenRow == ZERO -> row0 > 0);
    assert(chosenRow == ONE -> row1 > 0);
    assert(chosenRow == TWO -> row2 > 0);
    assert(chosenRow == THREE -> row3 > 0);
    // If the board is cleared, controller wins
    assume(row0 + row1 + row2 + row3 > 1);
    
    if (choice == ZERO) {row0--; }
    if (choice == ONE) { row1--; }
    if (choice == TWO) { row2--; }
    if (choice == THREE) { row3--; }
    chosenRow := choice;
    hasChosen := true;
}

method intern conRemoveNext () {
    assert(!envTurn && hasChosen);
    assert(chosenRow == ZERO -> row0 > 0);
    assert(chosenRow == ONE -> row1 > 0);
    assert(chosenRow == TWO -> row2 > 0);
    assert(chosenRow == THREE -> row3 > 0);
    // If the board is cleared, controller wins
    assume(row0 + row1 + row2 + row3 > 1);

    if (chosenRow == ZERO) { row0--; }
    else if (chosenRow == ONE) { row1--; }
    else if (chosenRow == TWO) { row2--; }
    else if (chosenRow == THREE) { row3--; }
}

method intern conPass() {
    assert(!envTurn && hasChosen);
    envTurn := true;
    hasChosen := false;
}
