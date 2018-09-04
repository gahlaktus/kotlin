// !API_VERSION: 1.3
// !JVM_DEFAULT_MODE: enable
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

interface SubAB : SubA, SubB {
}

fun box(): String  {
    return object : SubAB {}.value()
}