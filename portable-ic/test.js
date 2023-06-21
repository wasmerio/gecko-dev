function foo() {
    try {
        throw 1;
    } catch (e) {
        print("foo caught " + e);
        throw e + 1;
    } finally {
        print("finally in foo");
    }
}

try {
    foo()
} catch (e) {
    print("toplevel caught " + e);
} finally {
    print("finally in toplevel");
}
