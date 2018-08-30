/*
 * Copyright 2010-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license
 * that can be found in the license/LICENSE.txt file.
 */

package org.jetbrains.kotlin.asJava.classes

import com.intellij.psi.*
import com.intellij.psi.impl.PsiClassImplUtil
import com.intellij.psi.impl.PsiImplUtil
import com.intellij.psi.impl.light.*
import org.jetbrains.annotations.NonNls
import org.jetbrains.kotlin.asJava.LightClassGenerationSupport
import org.jetbrains.kotlin.asJava.builder.LightClassData
import org.jetbrains.kotlin.asJava.builder.LightMemberOriginForDeclaration
import org.jetbrains.kotlin.asJava.elements.*
import org.jetbrains.kotlin.codegen.FunctionCodegen
import org.jetbrains.kotlin.codegen.state.KotlinTypeMapper
import org.jetbrains.kotlin.descriptors.*
import org.jetbrains.kotlin.descriptors.annotations.AnnotationDescriptor
import org.jetbrains.kotlin.lexer.KtTokens
import org.jetbrains.kotlin.load.java.JvmAbi
import org.jetbrains.kotlin.load.kotlin.TypeMappingMode
import org.jetbrains.kotlin.name.FqName
import org.jetbrains.kotlin.name.SpecialNames
import org.jetbrains.kotlin.psi.*
import org.jetbrains.kotlin.psi.psiUtil.containingClass
import org.jetbrains.kotlin.resolve.annotations.JVM_STATIC_ANNOTATION_FQ_NAME
import org.jetbrains.kotlin.resolve.annotations.argumentValue
import org.jetbrains.kotlin.resolve.constants.EnumValue
import org.jetbrains.kotlin.resolve.descriptorUtil.fqNameSafe
import org.jetbrains.kotlin.resolve.descriptorUtil.isPublishedApi
import org.jetbrains.kotlin.resolve.jvm.annotations.STRICTFP_ANNOTATION_FQ_NAME
import org.jetbrains.kotlin.resolve.jvm.annotations.SYNCHRONIZED_ANNOTATION_FQ_NAME
import org.jetbrains.kotlin.resolve.jvm.annotations.TRANSIENT_ANNOTATION_FQ_NAME
import org.jetbrains.kotlin.resolve.jvm.annotations.VOLATILE_ANNOTATION_FQ_NAME
import org.jetbrains.kotlin.resolve.jvm.diagnostics.JvmDeclarationOriginKind
import org.jetbrains.kotlin.types.KotlinType

internal class KtUltraLightClass(kt: KtClassOrObject) : KtLightClassImpl(kt) {
    private val support: UltraLightSupport? by lazyPub { LightClassGenerationSupport.getInstance(project).ultraLightSupport(classOrObject) }

    override fun isFinal(isFinalByPsi: Boolean) = if (support == null) super.isFinal(isFinalByPsi) else isFinalByPsi

    override fun findLightClassData(): LightClassData {
        if (!isClsDelegateLoaded && support != null) {
            throw IllegalStateException("Cls delegate shouldn't be loaded for not too complex ultra-light classes!")
        }
        return super.findLightClassData()
    }

    private fun allSuperTypes() =
        getDescriptor()?.typeConstructor?.supertypes?.mapNotNull {
            it.asPsiType(classOrObject, support!!, TypeMappingMode.SUPER_TYPE) as? PsiClassType
        }.orEmpty()

    override fun createExtendsList(): PsiReferenceList? =
        if (support == null) super.createExtendsList()
        else LightReferenceListBuilder(manager, language, PsiReferenceList.Role.EXTENDS_LIST).also { list ->
            allSuperTypes()
                .filter { (isInterface || it.resolve()?.isInterface == false) && !it.equalsToText(CommonClassNames.JAVA_LANG_OBJECT) }
                .forEach(list::addReference)
        }

    override fun createImplementsList(): PsiReferenceList? =
        if (support == null) super.createImplementsList()
        else LightReferenceListBuilder(manager, language, PsiReferenceList.Role.IMPLEMENTS_LIST).also { list ->
            if (!isInterface) {
                allSuperTypes()
                    .filter { it.resolve()?.isInterface == true && (!isAnnotationType || !it.equalsToText(CommonClassNames.JAVA_LANG_ANNOTATION_ANNOTATION)) }
                    .forEach(list::addReference)
            }
        }

    override fun buildTypeParameterList(): PsiTypeParameterList =
        if (support == null) super.buildTypeParameterList() else buildTypeParameterList(classOrObject, this, support!!)

    // the following logic should be in the platform (super), overrides can be removed once that happens
    override fun getInterfaces(): Array<PsiClass> = PsiClassImplUtil.getInterfaces(this)
    override fun getSuperClass(): PsiClass? = PsiClassImplUtil.getSuperClass(this)
    override fun getSupers(): Array<PsiClass> = PsiClassImplUtil.getSupers(this)
    override fun getSuperTypes(): Array<PsiClassType> = PsiClassImplUtil.getSuperTypes(this)

    override fun getRBrace(): PsiElement? = null
    override fun getLBrace(): PsiElement? = null

    private val _ownFields: List<KtLightField> by lazyPub {
        val result = arrayListOf<KtLightField>()
        val usedNames = hashSetOf<String>()
        for (param in propertyParameters()) {
            val modifiers = hashSetOf<String>()
            modifiers.add(PsiModifier.PRIVATE)
            if (!param.isMutable)
                modifiers.add(PsiModifier.FINAL)
            result.add(KtUltraLightField(param, generateUniqueName(usedNames, param.name.orEmpty()), this, support!!, modifiers))
        }

        if (!isInterface &&
            !(classOrObject is KtObjectDeclaration && classOrObject.isCompanion() && containingClass?.isInterface == false)
        ) {
            for (prop in classOrObject.declarations.filterIsInstance<KtProperty>()) {
                propertyField(prop, usedNames, forceStatic = classOrObject is KtObjectDeclaration)?.let(result::add)
            }
        }

        classOrObject.companionObjects.firstOrNull()?.let { companion ->
            result.add(
                KtUltraLightField(
                    companion,
                    generateUniqueName(usedNames, companion.name.orEmpty()),
                    this,
                    support!!,
                    setOf(PsiModifier.STATIC, PsiModifier.FINAL, simpleVisibility(companion))
                )
            )

            for (prop in companion.declarations.filterIsInstance<KtProperty>()) {
                if (isInterface && !prop.hasModifier(KtTokens.CONST_KEYWORD)) continue

                propertyField(prop, usedNames, true)?.let(result::add)
            }
        }
        if (isNamedObject()) {
            result.add(
                KtUltraLightField(
                    classOrObject,
                    JvmAbi.INSTANCE_FIELD,
                    this,
                    support!!,
                    setOf(PsiModifier.STATIC, PsiModifier.FINAL, PsiModifier.PUBLIC)
                )
            )
        }

        result
    }

    private fun generateUniqueName(usedNames: HashSet<String>, base: String): String {
        if (usedNames.add(base)) return base
        var i = 1
        while (true) {
            val suggestion = "$base$$i"
            if (usedNames.add(suggestion)) return suggestion
            i++
        }
    }

    private fun isNamedObject() = classOrObject is KtObjectDeclaration && !classOrObject.isCompanion()

    private fun propertyField(prop: KtProperty, usedNames: HashSet<String>, forceStatic: Boolean): KtLightField? {
        val initializer = prop.initializer
        if (initializer == null && prop.accessors.isNotEmpty()) return null

        val hasDelegate = prop.hasDelegate()
        val fieldName = generateUniqueName(usedNames, (prop.name ?: "") + (if (hasDelegate) "\$delegate" else ""))

        val modifiers = hashSetOf<String>()
        if (prop.hasModifier(KtTokens.CONST_KEYWORD) || prop.hasModifier(KtTokens.LATEINIT_KEYWORD))
            modifiers.add(PsiModifier.PUBLIC)
        else
            modifiers.add(PsiModifier.PRIVATE)

        if (!prop.isVar || prop.hasModifier(KtTokens.CONST_KEYWORD) || hasDelegate)
            modifiers.add(PsiModifier.FINAL)

        if (forceStatic || isNamedObject() && isJvmStatic(prop))
            modifiers.add(PsiModifier.STATIC)

        return KtUltraLightField(prop, fieldName, this, support!!, modifiers)
    }

    override fun getOwnFields(): List<KtLightField> = if (support == null) super.getOwnFields() else _ownFields

    private fun propertyParameters() = classOrObject.primaryConstructorParameters.filter { it.hasValOrVar() }

    private val _ownMethods: List<KtLightMethod> by lazyPub {
        val result = arrayListOf<KtLightMethod>()
        for (decl in classOrObject.declarations.filterNot { isHiddenByDeprecation(it) }) {
            if (decl.hasModifier(KtTokens.PRIVATE_KEYWORD) && isInterface) continue
            when (decl) {
                is KtNamedFunction -> result.add(asJavaMethod(decl, false))
                is KtProperty -> result.addAll(propertyAccessors(decl, decl.name, decl.isVar, false))
            }
        }
        for (param in propertyParameters()) {
            result.addAll(propertyAccessors(param, param.name, param.isMutable, false))
        }
        if (!isInterface) {
            result.addAll(createConstructors())
        }
        classOrObject.companionObjects.firstOrNull()?.let { companion ->
            for (decl in companion.declarations.filterNot { isHiddenByDeprecation(it) }) {
                when (decl) {
                    is KtNamedFunction -> if (isJvmStatic(decl)) result.add(asJavaMethod(decl, true))
                    is KtProperty -> result.addAll(propertyAccessors(decl, decl.name, decl.isVar, true))
                }
            }
        }
        result
    }

    private fun createConstructors(): List<KtLightMethod> {
        val result = arrayListOf<KtLightMethod>()
        val constructors = classOrObject.allConstructors
        if (constructors.isEmpty()) {
            result.add(defaultConstructor())
        }
        for (ctx in constructors) {
            result.add(asJavaMethod(ctx, false))
            if (ctx == classOrObject.primaryConstructor &&
                ctx.valueParameters.isNotEmpty() &&
                ctx.valueParameters.all { it.defaultValue != null } &&
                constructors.none { it.valueParameters.isEmpty() }
            ) {
                result.add(noArgConstructor(simpleVisibility(ctx), ctx))

            }
        }
        return result
    }

    private fun defaultConstructor(): KtUltraLightMethod {
        val visibility =
            if (classOrObject is KtObjectDeclaration || classOrObject.hasModifier(KtTokens.SEALED_KEYWORD))
                PsiModifier.PRIVATE
            else PsiModifier.PUBLIC
        return noArgConstructor(visibility, classOrObject)
    }

    private fun simpleVisibility(ctx: KtDeclaration): String = when {
        ctx.hasModifier(KtTokens.PRIVATE_KEYWORD) -> PsiModifier.PRIVATE
        ctx.hasModifier(KtTokens.PROTECTED_KEYWORD) -> PsiModifier.PROTECTED
        else -> PsiModifier.PUBLIC
    }

    private fun noArgConstructor(visibility: String, decl: KtDeclaration): KtUltraLightMethod = KtUltraLightMethod(
        LightMethodBuilder(manager, language, name.orEmpty()).setConstructor(true).addModifier(visibility),
        decl,
        support!!,
        this
    )

    private fun isHiddenByDeprecation(decl: KtDeclaration): Boolean =
        (support!!.findAnnotation(decl, FqName("kotlin.Deprecated"))?.argumentValue("level") as? EnumValue)?.enumEntryName?.asString() == "HIDDEN"

    private fun isJvmStatic(decl: KtAnnotated): Boolean = decl.hasAnnotation(JVM_STATIC_ANNOTATION_FQ_NAME)

    override fun getOwnMethods(): List<KtLightMethod> = if (support == null) super.getOwnMethods() else _ownMethods

    private fun asJavaMethod(f: KtFunction, forceStatic: Boolean): KtLightMethod {
        val isConstructor = f is KtConstructor<*>
        val name = if (isConstructor) this.name else mangleIfNeeded(f, f.name ?: SpecialNames.NO_NAME_PROVIDED.asString())
        val method = lightMethod(name.orEmpty(), listOf(f), forceStatic)
        val wrapper = KtUltraLightMethod(method, f, support!!, this)
        addReceiverParameter(f, wrapper)
        for (param in f.valueParameters) {
            method.addParameter(KtUltraLightParameter(param.name.orEmpty(), param, support!!, wrapper, null))
        }
        val returnType: PsiType? by lazyPub {
            if (isConstructor) null
            else methodReturnType(f)
        }
        method.setMethodReturnType({ returnType })
        return wrapper
    }

    private fun addReceiverParameter(f: KtDeclaration, method: KtUltraLightMethod) {
        val receiver = (f as? KtCallableDeclaration)?.receiverTypeReference
        if (receiver != null) {
            method.delegate.addParameter(KtUltraLightParameter("\$self", f, support!!, method, receiver))
        }
    }

    private fun methodReturnType(f: KtDeclaration): PsiType {
        val desc = f.resolve()?.let { if (it is PropertyDescriptor) it.getter else it }
        val kotlinType = (desc as? FunctionDescriptor)?.returnType ?: return PsiType.NULL
        val mode = when {
            KotlinTypeMapper.forceBoxedReturnType(desc) -> TypeMappingMode.RETURN_TYPE_BOXED
            else -> TypeMappingMode.getOptimalModeForReturnType(kotlinType, false)
        }
        return kotlinType.asPsiType(f, support!!, mode)
    }

    private fun lightMethod(name: String, decls: List<KtDeclaration>, forceStatic: Boolean): LightMethodBuilder = LightMethodBuilder(
        manager, language, name,
        LightParameterListBuilder(manager, language),
        object : LightModifierList(manager, language) {
            override fun hasModifierProperty(name: String): Boolean {
                if (name == PsiModifier.PUBLIC || name == PsiModifier.PROTECTED || name == PsiModifier.PRIVATE) {
                    if (decls.any { it.hasModifier(KtTokens.PROTECTED_KEYWORD) }) return name == PsiModifier.PROTECTED
                    if (decls.any { isPrivate(it) }) return name == PsiModifier.PRIVATE

                    val overriding = decls.find { it.hasModifier(KtTokens.OVERRIDE_KEYWORD) }
                    when ((overriding?.resolve() as? CallableDescriptor)?.effectiveVisibility()) {
                        EffectiveVisibility.Public -> return name == PsiModifier.PUBLIC
                        EffectiveVisibility.Private -> return name == PsiModifier.PRIVATE
                        is EffectiveVisibility.Protected, is EffectiveVisibility.InternalProtected -> return name == PsiModifier.PROTECTED
                    }

                    return name == PsiModifier.PUBLIC
                }

                return when (name) {
                    PsiModifier.FINAL -> !isInterface && decls.any { it !is KtConstructor<*> && isFinal(it) }
                    PsiModifier.ABSTRACT -> isInterface || decls.any { it.hasModifier(KtTokens.ABSTRACT_KEYWORD) }
                    PsiModifier.STATIC -> forceStatic || isNamedObject() && decls.any { isJvmStatic(it) }
                    PsiModifier.STRICTFP -> decls.any { it is KtFunction && it.hasAnnotation(STRICTFP_ANNOTATION_FQ_NAME) }
                    PsiModifier.SYNCHRONIZED -> decls.any { it is KtFunction && it.hasAnnotation(SYNCHRONIZED_ANNOTATION_FQ_NAME) }
                    else -> false
                }
            }

            fun isPrivate(decl: KtDeclaration) =
                decl.hasModifier(KtTokens.PRIVATE_KEYWORD) ||
                        decl is KtFunction && decl.typeParameters.any { it.hasModifier(KtTokens.REIFIED_KEYWORD) }
        }
    ).setConstructor(decls.any { it is KtConstructor<*> || it is KtClassOrObject })

    private fun mangleIfNeeded(f: KtDeclaration, name: String) =
        if (isInternal(f) && f.resolve()?.isPublishedApi() != true)
            KotlinTypeMapper.InternalNameMapper.mangleInternalName(name, support!!.moduleName)
        else name

    private fun KtAnnotated.hasAnnotation(name: FqName) = support!!.findAnnotation(this, name) != null

    private fun isInternal(f: KtDeclaration): Boolean {
        if (f.hasModifier(KtTokens.OVERRIDE_KEYWORD)) {
            val desc = f.resolve()
            return desc is CallableDescriptor &&
                    desc.visibility.effectiveVisibility(desc, false) == EffectiveVisibility.Internal
        }
        return f.hasModifier(KtTokens.INTERNAL_KEYWORD)
    }

    private fun propertyAccessors(
        decl: KtDeclaration,
        propertyName: String?,
        mutable: Boolean,
        onlyJvmStatic: Boolean
    ): List<KtLightMethod> {
        if (decl.hasModifier(KtTokens.CONST_KEYWORD) || propertyName == null) return emptyList()
        if (decl.hasModifier(KtTokens.PRIVATE_KEYWORD) && (decl !is KtProperty || decl.accessors.isEmpty())) return emptyList()

        val result = arrayListOf<KtLightMethod>()

        val ktGetter = (decl as? KtProperty)?.getter
        val ktSetter = (decl as? KtProperty)?.setter

        if (!onlyJvmStatic || isJvmStatic(decl) || ktGetter != null && isJvmStatic(ktGetter)) {
            val getterName = if (isAnnotationType) propertyName else mangleIfNeeded(decl, JvmAbi.getterName(propertyName))
            val getterType: PsiType by lazyPub { methodReturnType(decl) }
            val getterPrototype = lightMethod(getterName, listOfNotNull(decl, ktGetter), onlyJvmStatic)
                .setMethodReturnType({ getterType })
            val getterWrapper = KtUltraLightMethod(getterPrototype, decl, support!!, this)
            addReceiverParameter(decl, getterWrapper)
            result.add(getterWrapper)
        }

        if (mutable && (!onlyJvmStatic || isJvmStatic(decl) || ktSetter != null && isJvmStatic(ktSetter))) {
            val setterName = mangleIfNeeded(decl, JvmAbi.setterName(propertyName))
            val setterPrototype = lightMethod(setterName, listOfNotNull(decl, ktSetter), onlyJvmStatic)
                .setMethodReturnType(PsiType.VOID)
            val setterWrapper = KtUltraLightMethod(setterPrototype, decl, support!!, this)
            addReceiverParameter(decl, setterWrapper)
            setterPrototype.addParameter(KtUltraLightParameter(propertyName, decl, support!!, setterWrapper, null))
            result.add(setterWrapper)
        }
        return result
    }

    private fun isFinal(decl: KtDeclaration): Boolean {
        if (decl.hasModifier(KtTokens.FINAL_KEYWORD)) return true
        return decl !is KtPropertyAccessor &&
                !decl.hasModifier(KtTokens.OPEN_KEYWORD) && !decl.hasModifier(KtTokens.OVERRIDE_KEYWORD) && !decl.hasModifier(KtTokens.ABSTRACT_KEYWORD)
    }

    override fun getInitializers(): Array<PsiClassInitializer> = emptyArray()

    override fun getContainingClass(): PsiClass? =
        if (support == null) super.getContainingClass() else classOrObject.containingClass()?.let(::KtUltraLightClass)

    override fun getParent(): PsiElement? = if (support == null) super.getParent() else containingClass ?: containingFile

    override fun getScope(): PsiElement? = if (support == null) super.getScope() else parent
    override fun copy(): KtLightClassImpl = KtUltraLightClass(classOrObject.copy() as KtClassOrObject)
}

private class KtUltraLightField(
    private val kt: KtNamedDeclaration,
    name: String,
    private val containingClass: KtUltraLightClass,
    private val support: UltraLightSupport,
    val modifiers: Set<String>
) : LightFieldBuilder(name, PsiType.NULL, kt), KtLightField {
    private val modList = object : KtLightSimpleModifierList(this, modifiers) {
        override fun hasModifierProperty(name: String): Boolean = when (name) {
            PsiModifier.VOLATILE -> support.findAnnotation(kt, VOLATILE_ANNOTATION_FQ_NAME) != null
            PsiModifier.TRANSIENT -> support.findAnnotation(kt, TRANSIENT_ANNOTATION_FQ_NAME) != null
            else -> super.hasModifierProperty(name)
        }
    }

    override fun getModifierList(): PsiModifierList = modList
    override fun hasModifierProperty(name: String): Boolean =
        modifierList.hasModifierProperty(name) //can be removed after IDEA platform does the same

    private val _type: PsiType by lazyPub {
        fun nonExistent() = JavaPsiFacade.getElementFactory(project).createTypeFromText("error.NonExistentClass", kt)
        when {
            kt is KtProperty && kt.hasDelegate() -> nonExistent()
            kt is KtObjectDeclaration ->
                KtLightClassForSourceDeclaration.createUltraLight(kt)?.let { JavaPsiFacade.getElementFactory(project).createType(it) }
                    ?: nonExistent()
            else -> kt.getKotlinType()?.let { it.asPsiType(kt, support, TypeMappingMode.getOptimalModeForValueParameter(it)) } ?: PsiType.NULL
        }
    }

    override fun getType(): PsiType = _type

    override fun getParent() = containingClass
    override fun getContainingClass() = containingClass
    override fun getContainingFile(): PsiFile? = containingClass.containingFile

    override fun computeConstantValue(): Any? =
        if (kt.hasModifier(KtTokens.CONST_KEYWORD))
            (kt.resolve() as? VariableDescriptor)?.compileTimeInitializer?.value
        else null

    override fun computeConstantValue(visitedVars: MutableSet<PsiVariable>?): Any? = computeConstantValue()

    override val kotlinOrigin = kt
    override val clsDelegate: PsiField
        get() = throw IllegalStateException("Cls delegate shouldn't be loaded for ultra-light PSI!")
    override val lightMemberOrigin = LightMemberOriginForDeclaration(kt, JvmDeclarationOriginKind.OTHER)

    override fun setName(@NonNls name: String): PsiElement {
        (kotlinOrigin as? KtNamedDeclaration)?.setName(name)
        return this
    }

    override fun setInitializer(initializer: PsiExpression?) = cannotModify()

}

internal class KtUltraLightMethod(
    internal val delegate: LightMethodBuilder,
    originalElement: KtDeclaration,
    private val support: UltraLightSupport,
    containingClass: KtUltraLightClass
) : KtLightMethodImpl({ delegate }, LightMemberOriginForDeclaration(originalElement, JvmDeclarationOriginKind.OTHER), containingClass) {

    override fun getReturnTypeElement(): PsiTypeElement? = null
    override fun getReturnType(): PsiType? = clsDelegate.returnType
    override fun getParameterList(): PsiParameterList = clsDelegate.parameterList

    // should be in super
    override fun isVarArgs() = PsiImplUtil.isVarArgs(this)

    override fun buildTypeParameterList(): PsiTypeParameterList {
        val origin = kotlinOrigin
        return if (origin is KtFunction || origin is KtProperty)
            buildTypeParameterList(origin as KtTypeParameterListOwner, this, support)
        else LightTypeParameterListBuilder(manager, language)
    }

    private val _throwsList: PsiReferenceList by lazyPub {
        val list = LightReferenceListBuilder(manager, language, PsiReferenceList.Role.THROWS_LIST)
        (kotlinOrigin?.resolve() as? FunctionDescriptor)?.let {
            for (ex in FunctionCodegen.getThrownExceptions(it)) {
                list.addReference(ex.fqNameSafe.asString())
            }
        }
        list
    }

    override fun getThrowsList(): PsiReferenceList = _throwsList
}

internal class KtUltraLightParameter(
    name: String,
    override val kotlinOrigin: KtDeclaration,
    private val support: UltraLightSupport,
    method: KtLightMethod,
    val receiver: KtTypeReference?
) : org.jetbrains.kotlin.asJava.elements.LightParameter(
    name,
    PsiType.NULL,
    method,
    method.language,
    kotlinOrigin is KtParameter && kotlinOrigin.isVarArg
),
    KtLightDeclaration<KtDeclaration, PsiParameter> {

    override val clsDelegate: PsiParameter
        get() = throw IllegalStateException("Cls delegate shouldn't be loaded for ultra-light PSI!")

    private val lightModifierList by lazyPub {
        object : KtLightSimpleModifierList(this, emptySet()) {
            override fun computeAnnotations(): List<KtLightAbstractAnnotation> {
                return super.computeAnnotations().filter { !it.fqNameMatches(JVM_STATIC_ANNOTATION_FQ_NAME.asString()) }
            }
        }
    }

    override fun getModifierList(): PsiModifierList = lightModifierList

    override fun getNavigationElement(): PsiElement = kotlinOrigin

    internal val kotlinType: KotlinType? by lazyPub {
        when {
            receiver != null -> (kotlinOrigin.resolve() as? CallableMemberDescriptor)?.extensionReceiverParameter?.type
            else -> kotlinOrigin.getKotlinType()
        }
    }
    private val _type: PsiType by lazyPub {
        kotlinType?.let { it.asPsiType(kotlinOrigin, support, TypeMappingMode.getOptimalModeForValueParameter(it)) } ?: PsiType.NULL
    }

    override fun getType(): PsiType = _type

    override fun setName(@NonNls name: String): PsiElement {
        (kotlinOrigin as? KtVariableDeclaration)?.setName(name)
        return this
    }

    override fun getContainingFile(): PsiFile = method.containingFile
    override fun getParent(): PsiElement = method.parameterList

    override fun equals(other: Any?): Boolean = other is KtUltraLightParameter && other.kotlinOrigin == this.kotlinOrigin
    override fun hashCode(): Int = kotlinOrigin.hashCode()

}

interface UltraLightSupport {
    val moduleName: String
    fun findAnnotation(kt: KtAnnotated, fqName: FqName): AnnotationDescriptor?
}