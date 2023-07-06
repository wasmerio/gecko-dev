function f(i) {
    print("call " + i);
    return 42;
}

for (let i = 0; i < 10; i++) {
    let retval = f(i);
    if (retval != 42) {
        print("bad retval");
    }
}
