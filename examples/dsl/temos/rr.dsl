int ptr := 0;

method extern ptrIs0 () { assume(ptr == 0); }
method extern ptrIs1 () { assume(ptr == 1); }

method GF intern run0 (bool ptrUp) { 
    if (ptrUp) ptr++;
    else ptr--;
}
method GF intern run1 (bool ptrUp) {
    if (ptrUp) ptr++;
    else ptr--;
}

guarantee {
    G (ptrIs0 || ptrIs1);
    G (ptrIs0 -> run0);
    G (ptrIs1 -> run1);
}

// //https://github.com/Barnard-PL-Labs/temos/blob/art-eval-pldi22/benchmarks/scheduler/rr/rr.tslmt
// // A round robin scheduler that guarantees that queued jobs must run infinitely often.
// //#LIA#
// always guarantee {
//     [ptr <- add ptr c1()] || [ptr <- sub ptr c1()];

//     G F [next <- job0];
//     G F [next <- job1];

//     eq ptr c0() -> [next <- job0];
//     eq ptr c1() -> [next <- job1];
// }