int runtime1 := 0;
int runtime2 := 0;
bool preempt := false;

method extern run1 () { preempt := true; }
method extern run2 () { preempt := true; }
method extern stutter () { preempt := false; }

method intern next1 () {
    assert(preempt || runtime1 <= runtime2);
    runtime1++; 
}

method intern next2 () {
    assert(preempt || runtime2 <= runtime1);
    runtime2++; 
}

guarantee {
    G (run1 -> next1);
    G (run2 -> next2);
    G ((!run1 && !run2) ) -> ((G F next1) && (G F next2));
}


// // https://github.com/Barnard-PL-Labs/temos/blob/art-eval-pldi22/benchmarks/scheduler/preemptive/preemptive.tslmt
// // A preemptive CPU scheduler that can interrupt tasks.
// //#LIA#
// preempt = run job1 || run job2;

// always assume {
//     !(run job1 && run job2);
// }

// always guarantee {
//     [next <- job1] || [next <- job2];

//     run job1 -> [next <- job1];
//     run job2 -> [next <- job2];

//     [next <- job1] <-> [runtime1 <- add runtime1 c1()];
//     [next <- job2] <-> [runtime2 <- add runtime2 c1()];

//     !preempt -> ((gt runtime1 runtime2 -> [next <- job1]) &&
//                  (gt runtime2 runtime1 -> [next <- job2]));
    
//     G !preempt -> ((G F [next <- job1]) && (G F [next <- job2]));
// }