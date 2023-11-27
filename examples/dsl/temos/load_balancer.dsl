int cpu0 := 0;
int cpu1 := 0;

method extern enqueueA () { assume(cpu0 <= cpu1); }
method extern enqueueB () { assume(cpu0 > cpu1); }

// Environment cannot always stutter
method !FG extern estutter() {}


method intern incrLoad (bool tocpu0) {
    if (tocpu0) { cpu0++; }
    else        { cpu1++; }
}

method intern swap0to1 () {
    assert(cpu0 > 0);
    cpu0--;
    cpu1++;
}

method intern swap1to0 () {
    assert(cpu1 > 0);
    cpu0++;
    cpu1--;
}


method intern stutter () {}

// We must synthesise a controller such that
// - enqueue is only called after an askEnqueue
// - enqueue is always called after an askEnqueue
// - no CPU has a lighter load forever
// TODO use LTL with expressions
// G F (cpu0 >= cpu1)
// G F (cpu1 >= cpu0)

guarantee {
    G (enqueueA -> incrLoad);
    G (enqueueB -> incrLoad);
    G (estutter -> !incrLoad);
    G F enqueueA;
    G F enqueueB;
}

// https://github.com/Barnard-PL-Labs/temos/blob/art-eval-pldi22/benchmarks/scheduler/load_balancer/load_balancer.tslmt 
// A load-balancing CPU scheduling algorithm that determines which CPU to allocate tasks to. It will always apply tasks to a CPU with a lighter load.
//#LIA#
//always guarantee {
//    enqueue && gt cpu0 cpu1 -> [cpu0 <- add cpu0 c1()];
//    enqueue && gt cpu1 cpu0 -> [cpu1 <- add cpu1 c1()];
//
//    (!(enqueue) && gt cpu0 cpu1) -> [cpu0 <- add cpu0 c1()] && [cpu1 <- sub cpu1 c0()];
//    (!(enqueue) && gt cpu1 cpu0) -> [cpu1 <- add cpu1 c1()] && [cpu0 <- sub cpu0 c0()];
//
//    !(G gt cpu0 cpu1);
//    !(G gt cpu1 cpu0);
//}