function foo(i) {
    switch (i) {
        case 0: print("zero"); break;
        case 1: print("one"); break;
        case 2: print("two"); break;
        default: print("default"); break;
    }
}

foo(1);
foo(0);
foo(2);
foo(3);
foo(100);
foo(1.0);
foo(0.0);
foo(-0.0);
foo(null);
