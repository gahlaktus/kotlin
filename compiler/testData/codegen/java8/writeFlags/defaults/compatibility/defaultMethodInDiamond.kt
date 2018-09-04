// !API_VERSION: 1.3
// !JVM_DEFAULT_MODE: compatibility
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

interface Test : SubA, SubB {

    fun defaultImplTrigger() = "123"
}

// TESTED_OBJECT_KIND: function
// TESTED_OBJECTS: Test$DefaultImpls, value
// FLAGS: ACC_PUBLIC, ACC_STATIC

// TESTED_OBJECT_KIND: function
// TESTED_OBJECTS: Test, value
// ABSENT: TRUE

