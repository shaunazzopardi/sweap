int location := 0;

method extern locIs0 () { assume(location == 0); }
method extern locIs1 () { assume(location == 1); }

method intern sub () { location--;}
method intern add () { location++;}

guarantee {
    G (locIs1 -> sub);
    G (locIs0 -> add);
    G (sub -> sub U locIs0);
    G (add -> add U locIs1);
    G (locIs0 || locIs1);
}

// // https://github.com/Barnard-PL-Labs/temos/blob/art-eval-pldi22/benchmarks/pong/automatic/automatic.tslmt
// // An "autoamtic" pong game where the ball bounces between the walls. It also guarantees that once the ball is flying in one direction, it will in fact hit the wall on the other direction.
// //#LIA#
// initially assume {
//     eq location c0();
// }

// always guarantee {
//     [location <- sub location c1()] -> [location <- sub location c1()] U (eq location c0());
//     [location <- add location c1()] -> [location <- add location c1()] U (eq location c1());
//     eq location c1() -> [location <- sub location c1()];
//     eq location c0()   -> [location <- add location c1()];
//     (lte c0() location && lte location c1());
// }