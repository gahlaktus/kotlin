// !API_VERSION: 1.3
// !JVM_DEFAULT_MODE: enable
// JVM_TARGET: 1.8
// WITH_RUNTIME

interface Base {
    val test: String

    val testDelegated: String
        get() = "fail"

}

interface SubA : Base

interface SubB : Base {
    @JvmDefault
    override val test: String
        get() = "O"
}

interface Test : SubA, SubB {}


class Delegate : Test {
    override val test: String
        get() = "fail"

    override val testDelegated: String
        get() = "K"
}

class TestClass(val foo: Test) : Test by foo

fun box(): String {
    val testClass = TestClass(Delegate())
    return testClass.test + testClass.testDelegated
}
