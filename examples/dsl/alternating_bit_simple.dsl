method extern say0 () {}
method extern say1 () {}

method intern ack0() {}
method intern ack1 () {}

guarantee {
    G (say0 -> ack0);
    G (say1 -> ack1);
}