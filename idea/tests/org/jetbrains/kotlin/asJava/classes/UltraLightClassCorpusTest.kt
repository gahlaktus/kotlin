/*
 * Copyright 2010-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license
 * that can be found in the license/LICENSE.txt file.
 */

package org.jetbrains.kotlin.asJava.classes

import org.jetbrains.kotlin.idea.test.KotlinLightCodeInsightFixtureTestCase
import org.jetbrains.kotlin.idea.test.KotlinWithJdkAndRuntimeLightProjectDescriptor
import org.jetbrains.kotlin.psi.KtFile
import org.jetbrains.kotlin.test.testFramework.runInEdtAndWait
import org.junit.After
import org.junit.AfterClass
import org.junit.Before
import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.Parameterized
import java.io.File

@RunWith(Parameterized::class)
class UltraLightClassCorpusTest(val filePath: String) : KotlinLightCodeInsightFixtureTestCase() {
    override fun getProjectDescriptor() = KotlinWithJdkAndRuntimeLightProjectDescriptor.INSTANCE

    @Before
    public override fun setUp() = super.setUp()

    @After
    public override fun tearDown() = super.tearDown()

    @Test
    fun test() {
        runInEdtAndWait {
            val file = myFixture.addFileToProject(filePath, File(filePath).readText()) as KtFile
            if (checkClassEquivalence(file, null)) {
                fallbackTests++
            }
            totalTests++
        }
    }

    companion object {
        var totalTests: Int = 0
        var fallbackTests: Int = 0

        @JvmStatic
        @Parameterized.Parameters(name = "{0}")
        fun data(): Collection<Any> = File("compiler/testData/asJava")
            .walkTopDown()
            .filter { it.path.endsWith(".kt") }
            .filter { it.name != "AllOpenAnnotatedClasses.kt" } //tests allopen compiler plugin that we don't have in this test
            .map { arrayOf(it.path) }
            .toList()

        @JvmStatic
        @AfterClass
        fun printStats() {
            println("Loaded heavy cls in $fallbackTests out of $totalTests tests")
        }
    }
}