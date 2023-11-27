int runtime1 := 0;
int runtime2 := 0;

// Environment can enqueue/dequeue jobs 1 and 2
method extern none () {}
method extern enq1 () {}
method extern enq2 () {}
method extern enq12 () {}

// Controller has to decide which job to run next (if any)
// but it cannot run a job that has a strictly higher runtime than the other
method intern next1 () { 
    assert(runtime1 <= runtime2);
    runtime1++;
}
method intern next2 () {
    assert(runtime2 <= runtime1);
    runtime2++;
}
method intern nextIdle () { }

// Enqueued job is eventually either run or dequeued
// Dequeued job is never run unless it is enqueued again
guarantee {
    G (enq1 || enq12) -> ((F next1) || (F (enq2 || none)));
    G (enq2 || enq12) -> ((F next2) || (F (enq1 || none)));
    G ((enq2 || none) -> ((G !next1) || (!next1 U (enq1 || enq12))));
    G ((enq1 || none) -> ((G !next2) || (!next2 U (enq2 || enq12))));
}

// https://github.com/Barnard-PL-Labs/temos/blob/art-eval-pldi22/benchmarks/scheduler/cfs/cfs.tslmt
// A simplified version of the Linux Completely Fair Scheduler.
//#LIA#

// always assume {
//     !(enqueue job1 && dequeue job1);
//     !(enqueue job2 && dequeue job2);
// }

// guarantee {
//     ![next <- job1] W enqueue job1;
//     ![next <- job2] W enqueue job2;
// }

// always guarantee {
//     [next <- job1] || [next <- job2] || [next <- idle];

//     enqueue job1 -> (F [next <- job1]) || F dequeue job1;
//     enqueue job2 -> (F [next <- job2]) || F dequeue job2;

//     dequeue job1 -> ![next <- job1] W enqueue job1;
//     dequeue job2 -> ![next <- job2] W enqueue job2;

//     enqueue job2 -> ((gt vruntime1 vruntime2 -> ![next <- job1]) W dequeue job2);
//     enqueue job1 -> ((gt vruntime2 vruntime1 -> ![next <- job2]) W dequeue job1);

//     [next <- job1] <-> [vruntime1 <- add vruntime1 c1()];
//     [next <- job2] <-> [vruntime2 <- add vruntime2 c1()];
// }
