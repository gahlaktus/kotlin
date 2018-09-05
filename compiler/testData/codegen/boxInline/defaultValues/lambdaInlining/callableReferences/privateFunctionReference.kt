// IGNORE_BACKEND: JVM_IR
// FILE: 1.kt
// LANGUAGE_VERSION: 1.2
// SKIP_INLINE_CHECK_IN: inlineFun$default
package test

private fun ok() = "OK"

internal inline fun inlineFun(): String {
    val x: () -> String = { ok() }
    return x()
}

// FILE: 2.kt

import test.*

fun box(): String {
    return inlineFun()
}
