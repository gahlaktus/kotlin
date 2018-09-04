// !API_VERSION: 1.3
// !JVM_DEFAULT_MODE: compatibility
// JVM_TARGET: 1.8


// FILE: Foo.java
public class Foo implements Test {

    String foo() {
        return Test.DefaultImpls.value(this);
    }
}

// FILE: main.kt
// JVM_TARGET: 1.8
// WITH_RUNTIME
interface Base {
    fun value(): String
}

interface SubA : Base

interface SubB : Base {
    @JvmDefault
    override fun value(): String = "OK"
}

interface Test : SubA, SubB {}

fun box(): String {
    if (Foo().value() != "OK") return "fail 1"
    return Foo().foo()
}