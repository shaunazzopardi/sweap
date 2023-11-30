int loc := 0;

method extern locIs0 () { assume(loc == 0); }
method extern locIs100 () { assume(loc == 100); }
method extern check () {
    assume(loc != 0);
    assume(loc != 100);
    assert(loc >= 0);
    assert(loc <= 100);
}

method intern incr () { loc++; }
method intern decr () { loc--; }

guarantee {
    G (incr -> X(check -> incr));
    G (decr -> X(check -> decr));
    G (locIs0 -> !decr);
    G (locIs100 -> !incr);
}

// This is hard:
//G (incr -> incr U locIs100);
//G (decr -> decr U locIs0);

// // https://github.com/Barnard-PL-Labs/temos/blob/art-eval-pldi22/benchmarks/pong/bouncing/bouncing.tslmt
// // An "automatic" pong game where the ball bounces between the walls. The game must guarantee that the ball must continue bouncing between the walls.
// //#LIA#
// initially assume {
//     eq loc c0();
// }

// always guarantee {
//     [loc <- sub loc c1()] -> [loc <- sub loc c1()] W (eq loc c0());
//     [loc <- add loc c1()] -> [loc <- add loc c1()] W (eq loc c100());
//     eq loc c100() -> [loc <- sub loc c1()];
//     eq loc c0()   -> [loc <- add loc c1()];
//     (lte c0() loc && lte loc c100());
// }
