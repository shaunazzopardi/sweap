bool last_ack := true;

method GF extern send0 () {
    assume(last_ack);
}
method GF extern send1 () {
    assume(!last_ack);
}

method intern ack0 () {
    last_ack := false;
}
method intern ack1 () {
    last_ack := true;
}

guarantee {
    G (send0 -> F ack0);
    G (send1 -> F ack1);
}