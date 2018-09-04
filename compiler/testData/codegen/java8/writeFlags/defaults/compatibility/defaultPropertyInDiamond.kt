// !API_VERSION: 1.3
// !JVM_DEFAULT_MODE: compatibility
// JVM_TARGET: 1.8
// WITH_RUNTIME

interface Base {
    var value: String
}

interface SubA : Base

interface SubB : Base {
    @JvmDefault
    override var value
        get() = "OK"
        set(value) {}
}

interface Test : SubA, SubB {

    fun defaultImplTrigger() = "123"
}

// TESTED_OBJECT_KIND: function
// TESTED_OBJECTS: Test, getValue
// ABSENT: TRUE

// TESTED_OBJECT_KIND: function
// TESTED_OBJECTS: Test, setValue
// ABSENT: TRUE

// TESTED_OBJECT_KIND: function
// TESTED_OBJECTS: Test$DefaultImpls, getValue
// FLAGS: ACC_PUBLIC, ACC_STATIC

// TESTED_OBJECT_KIND: function
// TESTED_OBJECTS: Test$DefaultImpls, setValue
// FLAGS: ACC_PUBLIC, ACC_STATIC