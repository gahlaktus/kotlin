open class Class {
    open fun foo(): Int = 4
}

interface Interface {
    fun foo(): Int
}

class ChildClass : Class(), Interface {
    override <caret>fun foo() = super.foo()
}
