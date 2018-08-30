/*
 * Copyright 2010-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license
 * that can be found in the license/LICENSE.txt file.
 */

package org.jetbrains.kotlin.asJava.classes

import com.intellij.psi.*
import junit.framework.TestCase.fail
import org.jetbrains.kotlin.idea.test.KotlinLightCodeInsightFixtureTestCase
import org.jetbrains.kotlin.idea.test.KotlinLightCodeInsightFixtureTestCaseBase
import org.jetbrains.kotlin.idea.test.KotlinWithJdkAndRuntimeLightProjectDescriptor
import org.jetbrains.kotlin.psi.KtClassOrObject
import org.jetbrains.kotlin.psi.KtFile

class UltraLightClassTest : KotlinLightCodeInsightFixtureTestCase() {
    override fun getProjectDescriptor() = KotlinWithJdkAndRuntimeLightProjectDescriptor.INSTANCE

    fun testSimpleFunctions() {
        checkClassEquivalence(
            """
class Foo {
  open fun bar(a: Int, b:Any, c:Foo): Unit {}
  internal fun bar2(a: Sequence, b: Unresolved) {}
  private fun bar3(x: Foo.Inner, vararg y: Inner) = "str"
  fun bar4() = 42

  operator fun plus(increment: Int): Foo {}
  fun String.onString(a: (Int) -> Any?): Foo {}

  class Inner {}
}
"""
        )
    }

    fun testClassModifiers() {
        checkClassEquivalence(
            """
package pkg

open class Open {
  private class Private: Open {}
  protected inner class Private2 {}
  internal class StaticInternal {}
}
internal class OuterInternal {}
private class TopLevelPrivate {}

sealed class Season {
    class Nested: Season()
}"""
        )
    }

    fun testGenerics() {
        checkClassEquivalence(
            """
abstract class C<T>(var constructorParam: List<CharSequence>) {
  fun foo<V, U : V>(p1: V, p2: C<V>, p4: Sequence<V>): T {}

  inline fun <reified T : Enum<T>> printAllValues() {
    print(enumValues<T>().joinToString { it.name })
  }

  val <Q : T> Q.w: Q get() = null!!

  var sListProp: List<String>?
  var sSetProp: Set<String>?
  var sMutableSetProp: MutableSet<String>?
  var sHashSetProp: HashSet<String>?
  var csListProp: List<CharSequence>?

  abstract fun listCS(l: List<CharSequence>): List<CharSequence>
  abstract fun listS(l: List<String>): List<String>
  abstract fun mutables(cin: MutableCollection<in Number>, sOut: MutableList<out C<*>>): MutableSet<CharSequence>
  abstract fun nested(l: List<List<CharSequence>>): Collection<Collection<CharSequence>>
}

open class K<out T: K<T>> { }
class Sub: K<K<*>>()
"""
        )
    }

    fun testAnnotations() {
        val decls = myFixture.addFileToProject(
            "decls.kt", """
import kotlin.reflect.KClass

annotation class Anno(val p: String = "", val x: Array<Anno> = arrayOf(Anno(p="a"), Anno(p="b")))

@Target(AnnotationTarget.CLASS, AnnotationTarget.FUNCTION,
        AnnotationTarget.VALUE_PARAMETER, AnnotationTarget.EXPRESSION)
@Retention(AnnotationRetention.SOURCE)
@MustBeDocumented
@Deprecated("This anno is deprecated, use === instead", ReplaceWith("this === other"))
annotation class Fancy

annotation class ReplaceWith(val expression: String)

annotation class Deprecated(
    val message: String,
    val replaceWith: ReplaceWith = ReplaceWith(""))

annotation class Ann(val arg1: KClass<*>, val arg2: KClass<out Any>)
"""
        ) as KtFile

        checkClassEquivalence(decls, clsLoadingExpected = true)

        checkClassEquivalence(
            """
@Anno class F: Runnable {
  @Anno("f") fun f(@Anno p: String) {}
  @Anno("p") var prop = "x"
}


class Foo @Anno constructor(dependency: MyDependency) {
  var x: String? = null
        @Anno set

    @Anno
    fun String.f4() {}
}

@Ann(String::class, Int::class) class MyClass

class Example(@field:Ann val foo,    // annotate Java field
              @get:Ann val bar,      // annotate Java getter
              @param:Ann val quux)   // annotate Java constructor parameter
"""
        )
    }

    fun testProperties() {
        checkClassEquivalence(
            """
class Foo(a: Int, val b:Foo, var c:Boolean, private val d: List, protected val e: Long = 2) {
  val f1 = 2

  protected var f2 = 3

  var name: String = "x"

  val isEmpty get() = false
  var isEmptyMutable: Boolean?
  var islowercase: Boolean?
  var isEmptyInt: Int?
  var getInt: Int?
  private var noAccessors: String

  internal var stringRepresentation: String
    get() = this.toString()
    set(value) {
        setDataFromString(value)
    }

  const val SUBSYSTEM_DEPRECATED: String = "This subsystem is deprecated"

  var counter = 0
    set(value) {
        if (value >= 0) field = value
    }
  var counter2 : Int?
    get() = field
    set(value) {
        if (value >= 0) field = value
    }
  lateinit var subject: Unresolved

  var delegatedProp: String by Delegate()
  var lazyProp: String by lazy { "abc" }

  val Int.intProp: Int
    get() = 1
}

"""
        )
    }

    fun testInheritance() {
        checkClassEquivalence(
            """
interface Intf {
  fun v(): Int
}
interface IntfWithProp : Intf {
  val x: Int
}
abstract class Base(p: Int) {
    open protected fun v(): Int? { }
    fun nv() { }
    abstract fun abs(): Int

    internal open val x: Int get() { }
    open var y = 1
    open protected var z = 1
}
class Derived(p: Int) : Base(p), IntfWithProp {
    override fun v() = unknown()
    override val x = 3
    override fun abs() = 0
}
abstract class AnotherDerived(override val x: Int, override val y: Int, override val z: Int) : Base(2) {
    final override fun v() { }
    abstract fun noReturn(s: String)
}
"""
        )
    }

    fun testObjects() {
        checkClassEquivalence(
            """
class C {
    companion object {
        @JvmStatic fun foo() {}
        fun bar() {}
        @JvmStatic var x: String = ""

        var I.c: String
            @JvmStatic get() = "OK"
            @JvmStatic set(t: String) {}

        var c1: String
            get() = "OK"
            @JvmStatic set(t: String) {}
    }
}

class C1 {
  private companion object {}
}

interface I {
  companion object { }
}

object Obj : java.lang.Runnable {
    @JvmStatic var x: String = ""
    override fun run() {}
    @JvmStatic fun zoo(): Int = 2
}
"""
        )
    }

    fun testInlineClasses() {
        checkClassEquivalence(
            """
inline class UInt(private val value: Int) { }
inline enum class Foo(val x: Int) {
    A(0), B(1);

    fun example() { }
}

inline class RefinedFoo(val f: Foo) {
    inline fun <T> array(): Array<T> = f.objects() as Array<T>
}

inline class InlinedDelegate<T>(var node: T) {
    operator fun setValue(thisRef: A, property: KProperty<*>, value: T) {
        if (node !== value) {
            thisRef.notify(node, value)
        }
        node = value
    }

    operator fun getValue(thisRef: A, property: KProperty<*>): T {
        return node
    }
}
""",
            mayLoadCls = true
        )
    }

    fun testDataClasses() {
        checkClassEquivalence(
            """
data class User(val name: String = "", val age: Int = 0)

data class Person(val name: String) {
    var age: Int = 0
}
""", mayLoadCls = true
        )
    }

    fun testImplementingKotlinCollections() {
        checkClassEquivalence(
            """
class MyList : List<String> {
  override operator fun get(index: Int): String {}
}
interface ASet<T> : MutableCollection<T> {}
abstract class MySet<T> : ASet<T> {
  override fun remove(elem: String): Boolean {}

}
""", mayLoadCls = true
        )
    }

    fun testCoroutines() {
        checkClassEquivalence(
            """
class Foo {
  suspend fun doSomething(foo: Foo): Bar {}
}
class Bar {
  fun <T> async(block: suspend () -> T)
}

interface Base {
    suspend fun foo()
}

class Derived: Base {
    override suspend fun foo() { ... }
}
""", mayLoadCls = true
        )
    }

    fun testEnums() {
        checkClassEquivalence(
            """
import java.util.function.*

enum class Direction {
    NORTH, SOUTH, WEST, EAST
}

enum class Color(val rgb: Int) {
        RED(0xFF0000),
        GREEN(0x00FF00),
        BLUE(0x0000FF)
}

enum class ProtocolState {
    WAITING {
        override fun signal() = TALKING
    },

    TALKING {
        override fun signal() = WAITING
    };

    abstract fun signal(): ProtocolState
}

enum class IntArithmetics : BinaryOperator<Int>, IntBinaryOperator {
    PLUS {
        override fun apply(t: Int, u: Int): Int = t + u
    },
    TIMES {
        override fun apply(t: Int, u: Int): Int = t * u
    };

    override fun applyAsInt(t: Int, u: Int) = apply(t, u)
}
""",
            mayLoadCls = true
        )
    }

    fun testDelegatingToInterfaces() {
        checkClassEquivalence(
            """
interface Base {
    fun printMessage()
    fun printMessageLine()
}

class BaseImpl(val x: Int) : Base {
    override fun printMessage() { print(x) }
    override fun printMessageLine() { println(x) }
}

class Derived(b: Base) : Base by b {
    override fun printMessage() { print("abc") }
}
""",
            mayLoadCls = true
        )
    }

    fun testThrowsAnnotation() {
        checkClassEquivalence(
            """
class MyException : Exception
class C @Throws(Exception::class) constructor(a: Int = 1) {
    @Throws(java.io.IOException::class, MyException::class)
    fun readFile(name: String): String {}
}
"""
        )
    }


    fun testImportAliases() {
        checkClassEquivalence(
            """
import kotlin.jvm.JvmStatic as JS
object O {
  @JS fun foo() {}
}
""", mayLoadCls = true
        )
    }


    fun testTypeAliases() {
        myFixture.addFileToProject("aliases.kt", "typealias JO = JvmOverloads")
        checkClassEquivalence(
            """
object O {
  @JO fun foo(a: Int = 1, b: String = "") {}
}
""",
            mayLoadCls = true
        )
    }



    private fun checkClassEquivalence(text: String, mayLoadCls: Boolean = false) {
        val file = myFixture.addFileToProject("a.kt", text) as KtFile
        checkClassEquivalence(file, mayLoadCls)
    }

}

/**
 * @return true if loaded cls
 */
internal fun checkClassEquivalence(file: KtFile, clsLoadingExpected: Boolean?): Boolean {
    var loadedCls = false
    val ktClasses = file.declarations.filterIsInstance<KtClassOrObject>().toList()
    val goldText = ktClasses.joinToString("\n\n") {
        val gold = KtLightClassForSourceDeclaration.create(it)
        if (gold != null) {
            KotlinLightCodeInsightFixtureTestCaseBase.assertFalse(gold.javaClass.name.contains("Ultra"))
        }
        gold?.render().orEmpty()
    }
    val newText = ktClasses.joinToString("\n\n") {
        val clazz = KtLightClassForSourceDeclaration.createUltraLight(it)
        if (clazz != null) {
            val result = clazz.render()
            if (clazz.isClsDelegateLoaded) {
                loadedCls = true
            }
            if (clsLoadingExpected == false && clazz.isClsDelegateLoaded) {
                fail("Cls delegate isn't expected to be loaded!")
            }
            result
        } else ""
    }
    if (goldText != newText) {
        println(file.virtualFilePath)
        KotlinLightCodeInsightFixtureTestCaseBase.assertEquals(
            "//Classic implementation:\n$goldText",
            "//Light implementation:\n$newText"
        )
    }
    if (clsLoadingExpected == true && !loadedCls) {
        fail("mayLoadCls should be false")
    }
    return loadedCls
}

private fun PsiClass.render(): String {
    fun PsiAnnotation.renderAnnotation() =
        "@" + qualifiedName + "(" + parameterList.attributes.joinToString { it.name + "=" + (it.value?.text ?: "?") } + ")"

    fun PsiModifierListOwner.renderModifiers() =
        annotations.joinToString("") { it.renderAnnotation() + (if (this is PsiParameter) " " else "\n") } +
                PsiModifier.MODIFIERS.filter(::hasModifierProperty).joinToString("") { "$it " }

    fun PsiType.renderType() = getCanonicalText(true)

    fun PsiReferenceList?.renderRefList(keyword: String): String {
        if (this == null || this.referencedTypes.isEmpty()) return ""
        return " " + keyword + " " + referencedTypes.joinToString { it.renderType() }
    }

    fun PsiVariable.renderVar(): String {
        var result = this.renderModifiers() + type.renderType() + " " + name
        if (this is PsiParameter && this.isVarArgs) {
            result += " /* vararg */"
        }
        computeConstantValue()?.let { result += " /* constant value $it */" }
        return result
    }

    fun PsiTypeParameterListOwner.renderTypeParams() =
        if (typeParameters.isEmpty()) ""
        else "<" + typeParameters.joinToString {
            val bounds =
                if (it.extendsListTypes.isNotEmpty())
                    " extends " + it.extendsListTypes.joinToString(" & ", transform = PsiClassType::renderType)
                else ""
            it.name!! + bounds
        } + "> "

    fun PsiMethod.renderMethod() =
        renderModifiers() +
                (if (isVarArgs) "/* vararg */ " else "") +
                renderTypeParams() +
                (returnType?.renderType() ?: "") + " " +
                name +
                "(" + parameterList.parameters.joinToString { it.renderModifiers() + it.type.renderType() } + ")" +
                (this as? PsiAnnotationMethod)?.defaultValue?.let { " default " + it.text }.orEmpty() +
                throwsList.referencedTypes.let { thrownTypes ->
                    if (thrownTypes.isEmpty()) ""
                    else " throws " + thrownTypes.joinToString { it.renderType() }
                } +
                ";"

    val classWord = when {
        isAnnotationType -> "@interface"
        isInterface -> "interface"
        isEnum -> "enum"
        else -> "class"
    }

    return renderModifiers() +
            classWord + " " +
            name + " /* " + qualifiedName + "*/" +
            renderTypeParams() +
            extendsList.renderRefList("extends") +
            implementsList.renderRefList("implements") +
            " {\n" +
            (if (isEnum) fields.filterIsInstance<PsiEnumConstant>().joinToString(",\n") { it.name } + ";\n\n" else "") +
            fields.filterNot { it is PsiEnumConstant }.map { it.renderVar().prependIndent("  ") + ";\n\n" }.sorted().joinToString("") +
            methods.map { it.renderMethod().prependIndent("  ") + "\n\n" }.sorted().joinToString("") +
            innerClasses.map { it.render().prependIndent("  ") }.sorted().joinToString("") +
            "}"
}
