int topQueue := 0;
int botQueue := 0;

bool doneInit := false;


method extern init (bool incrTop, bool incrBot) {
    assume(!doneInit);
    if (incrTop) topQueue++;
    if (incrBot) botQueue++;
}

method extern done() {
    assume(!doneInit);
    doneInit := true;
}

method extern topGTbot () {
    assume(doneInit);
    assume(topQueue > botQueue);
}

method extern topLTEbot () {
    assume(doneInit);
    assume(topQueue <= botQueue);
}

method intern empty () {
    assert(doneInit);
    assert(topQueue == 0);
    assert(botQueue == 0);
}

method intern goDown() {
    assert(doneInit);
    assert(topQueue > 0);
    topQueue--;
}

method intern goUp() {
    assert(doneInit);
    assert(botQueue > 0);
    botQueue--;
}

method intern stutter() {}

guarantee {
    G (done -> F empty);
    G (topGTbot -> goDown);
    G (topLTEbot -> (goUp || empty));
}

// Main takeaways:
// - We can't deal with nondet. initial state as nicely
// - Expressions in LTL would be nicer

// // https://github.com/Barnard-PL-Labs/temos/blob/art-eval-pldi22/benchmarks/escalator/smart/smart.tslmt
// // A smart escalator, that guarantees that everybody waiting in the queue for the escalator will be able to take it. It also guarantees that it is democratic, moving in the direction where there are more people waiting.
// //#LIA#

// goDown = [ topQueue <- sub topQueue c1()];
// goUp =   [ botQueue <- sub botQueue c1()];

// always assume {
//     gte botQueue c0();
//     gte topQueue c0();
// }

// always guarantee {
//   // Fairly send the direction with more people
//   gt botQueue topQueue    -> goUp;
//   !(gt botQueue topQueue) -> goDown;

//   // One direction at a time
//   !(goDown && goUp);

//   // All users leave
//   F eq botQueue c0();
//   F eq topQueue c0();
// }