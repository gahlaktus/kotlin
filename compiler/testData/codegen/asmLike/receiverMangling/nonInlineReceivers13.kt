// LOCAL_VARIABLE_TABLE
// LANGUAGE_VERSION: 1.3

fun String.foo(count: Int) {
    val x = false

    block {
        this@foo + this@block.toString() + x.toString() + count.toString()
    }
}

fun block(block: Long.() -> Unit) = 5L.block()