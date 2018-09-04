// !API_VERSION: 1.3
// !JVM_DEFAULT_MODE: compatibility
// JVM_TARGET: 1.8


// FILE: Foo.java
public class Foo implements Test {

    String foo() {
        return Test.DefaultImpls.foo(this)
    }
}

