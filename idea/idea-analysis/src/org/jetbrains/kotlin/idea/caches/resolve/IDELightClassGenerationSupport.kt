/*
 * Copyright 2010-2016 JetBrains s.r.o.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package org.jetbrains.kotlin.idea.caches.resolve

import com.intellij.openapi.module.ModuleUtilCore
import com.intellij.openapi.project.Project
import com.intellij.openapi.util.text.StringUtil
import com.intellij.psi.PsiElement
import com.intellij.psi.search.GlobalSearchScope
import com.intellij.psi.util.CachedValueProvider
import com.intellij.psi.util.CachedValuesManager
import com.intellij.psi.util.PsiModificationTracker
import com.intellij.util.containers.ConcurrentFactoryMap
import org.jetbrains.kotlin.asJava.LightClassBuilder
import org.jetbrains.kotlin.asJava.LightClassGenerationSupport
import org.jetbrains.kotlin.asJava.builder.InvalidLightClassDataHolder
import org.jetbrains.kotlin.asJava.builder.LightClassDataHolder
import org.jetbrains.kotlin.asJava.classes.UltraLightSupport
import org.jetbrains.kotlin.asJava.classes.shouldNotBeVisibleAsLightClass
import org.jetbrains.kotlin.asJava.finder.JavaElementFinder
import org.jetbrains.kotlin.descriptors.ClassifierDescriptor
import org.jetbrains.kotlin.descriptors.DeclarationDescriptor
import org.jetbrains.kotlin.descriptors.annotations.AnnotationDescriptor
import org.jetbrains.kotlin.idea.caches.lightClasses.IDELightClassContexts
import org.jetbrains.kotlin.idea.caches.lightClasses.LazyLightClassDataHolder
import org.jetbrains.kotlin.idea.facet.KotlinFacet
import org.jetbrains.kotlin.idea.resolve.frontendService
import org.jetbrains.kotlin.idea.stubindex.KotlinTypeAliasShortNameIndex
import org.jetbrains.kotlin.lexer.KtTokens
import org.jetbrains.kotlin.name.FqName
import org.jetbrains.kotlin.name.Name
import org.jetbrains.kotlin.psi.*
import org.jetbrains.kotlin.psi.psiUtil.hasExpectModifier
import org.jetbrains.kotlin.resolve.BindingContext
import org.jetbrains.kotlin.resolve.descriptorUtil.fqNameSafe
import org.jetbrains.kotlin.resolve.descriptorUtil.getAllSuperClassifiers
import org.jetbrains.kotlin.resolve.lazy.BodyResolveMode
import org.jetbrains.kotlin.resolve.lazy.NoDescriptorForDeclarationException
import java.util.concurrent.ConcurrentMap

class IDELightClassGenerationSupport(private val project: Project) : LightClassGenerationSupport() {
    override fun ultraLightSupport(element: KtClassOrObject): UltraLightSupport? {
        val module = ModuleUtilCore.findModuleForPsiElement(element) ?: return null
        val facet = KotlinFacet.get(module)
        if (facet != null && facet.configuration.settings.compilerArguments?.pluginClasspaths.isNullOrEmpty()) {
            return null
        }

        val decl = findTooComplexDeclaration(element)
        if (decl != null) {
            //todo log
            println("Using heavy light classes for ${element.fqName?.asString()} because of ${StringUtil.trimLog(decl.text, 100)}")
            return null
        }

        return object : UltraLightSupport {
            override val moduleName: String = module.name

            override fun findAnnotation(kt: KtAnnotated, fqName: FqName): AnnotationDescriptor? = kt
                .annotationEntries
                .filter { it.shortName == fqName.shortName() || hasAlias(kt, fqName.shortName()) }
                .mapNotNull { analyze(it).get(BindingContext.ANNOTATION, it) }
                .find { it.fqName == fqName }
        }
    }

    private fun findTooComplexDeclaration(kt: KtDeclaration): PsiElement? {
        fun KtAnnotationEntry.seemsNonTrivial(): Boolean {
            val name = shortName
            return name == null || hasAlias(kt, name) || name.asString().startsWith("Jvm") && name.asString() != "JvmStatic"
        }

        if (kt.hasExpectModifier() ||
            kt.hasModifier(KtTokens.ANNOTATION_KEYWORD) ||
            kt.hasModifier(KtTokens.INLINE_KEYWORD) && kt is KtClassOrObject ||
            kt.hasModifier(KtTokens.DATA_KEYWORD) ||
            kt.hasModifier(KtTokens.ENUM_KEYWORD) ||
            kt.hasModifier(KtTokens.SUSPEND_KEYWORD)) {
            return kt
        }

        kt.annotationEntries.find(KtAnnotationEntry::seemsNonTrivial)?.let { return it }

        if (kt is KtClassOrObject) {
            kt.superTypeListEntries.find { it is KtDelegatedSuperTypeEntry }?.let { return it }

            for (d in kt.declarations) {
                if (d is KtClassOrObject && !(d is KtObjectDeclaration && d.isCompanion())) continue
                
                findTooComplexDeclaration(d)?.let { return it }
            }

            if (implementsKotlinCollection(kt)) {
                return kt.getSuperTypeList()
            }
        }
        if (kt is KtCallableDeclaration) {
            kt.valueParameters.mapNotNull { findTooComplexDeclaration(it) }.firstOrNull()?.let { return it }
        }

        return null

    }

    private fun implementsKotlinCollection(kt: KtClassOrObject): Boolean {
        val implementsInterfaces = kt.superTypeListEntries.any { it is KtSuperTypeEntry }
        return implementsInterfaces &&
                (resolveToDescriptor(kt) as? ClassifierDescriptor)?.getAllSuperClassifiers()?.any {
                    it.fqNameSafe.asString().startsWith("kotlin.collections.")
                } == true
    }

    private fun hasAlias(kt: KtElement, shortName: Name): Boolean = allAliases(kt.containingKtFile)[shortName.asString()] == true

    private fun allAliases(file: KtFile): ConcurrentMap<String, Boolean> = CachedValuesManager.getCachedValue(file) {
        val importAliases = file.importDirectives.mapNotNull { it.aliasName }.toSet()
        val map = ConcurrentFactoryMap.createMap<String, Boolean> { s ->
            s in importAliases || KotlinTypeAliasShortNameIndex.getInstance().get(s, project, file.resolveScope).isNotEmpty()
        }
        CachedValueProvider.Result.create<ConcurrentMap<String, Boolean>>(map, PsiModificationTracker.MODIFICATION_COUNT)
    }

    private val scopeFileComparator = JavaElementFinder.byClasspathComparator(GlobalSearchScope.allScope(project))

    override fun createDataHolderForClass(classOrObject: KtClassOrObject, builder: LightClassBuilder): LightClassDataHolder.ForClass {
        return when {
            classOrObject.shouldNotBeVisibleAsLightClass() -> InvalidLightClassDataHolder
            classOrObject.isLocal -> LazyLightClassDataHolder.ForClass(
                builder,
                exactContextProvider = { IDELightClassContexts.contextForLocalClassOrObject(classOrObject) },
                dummyContextProvider = null,
                diagnosticsHolderProvider = { classOrObject.getDiagnosticsHolder() }
            )
            else -> LazyLightClassDataHolder.ForClass(
                builder,
                exactContextProvider = { IDELightClassContexts.contextForNonLocalClassOrObject(classOrObject) },
                dummyContextProvider = { IDELightClassContexts.lightContextForClassOrObject(classOrObject) },
                diagnosticsHolderProvider = { classOrObject.getDiagnosticsHolder() }
            )
        }
    }


    override fun createDataHolderForFacade(files: Collection<KtFile>, builder: LightClassBuilder): LightClassDataHolder.ForFacade {
        assert(!files.isEmpty()) { "No files in facade" }

        val sortedFiles = files.sortedWith(scopeFileComparator)

        return LazyLightClassDataHolder.ForFacade(
            builder,
            exactContextProvider = { IDELightClassContexts.contextForFacade(sortedFiles) },
            dummyContextProvider = { IDELightClassContexts.lightContextForFacade(sortedFiles) },
            diagnosticsHolderProvider = { files.first().getDiagnosticsHolder() }
        )
    }

    override fun createDataHolderForScript(script: KtScript, builder: LightClassBuilder): LightClassDataHolder.ForScript {
        return LazyLightClassDataHolder.ForScript(
            builder,
            exactContextProvider = { IDELightClassContexts.contextForScript(script) },
            dummyContextProvider = { null },
            diagnosticsHolderProvider = { script.getDiagnosticsHolder() }
        )
    }

    private fun KtElement.getDiagnosticsHolder() =
        getResolutionFacade().frontendService<LazyLightClassDataHolder.DiagnosticsHolder>()

    override fun resolveToDescriptor(declaration: KtDeclaration): DeclarationDescriptor? {
        try {
            return declaration.resolveToDescriptorIfAny(BodyResolveMode.FULL)
        } catch (e: NoDescriptorForDeclarationException) {
            return null
        }
    }

    override fun analyze(element: KtElement) = element.analyze(BodyResolveMode.PARTIAL)

    override fun analyzeWithContent(element: KtClassOrObject) = element.analyzeWithContent()
}

