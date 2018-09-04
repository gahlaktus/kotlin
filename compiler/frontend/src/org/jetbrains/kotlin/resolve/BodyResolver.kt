/*
 * Copyright 2010-2017 JetBrains s.r.o.
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

package org.jetbrains.kotlin.resolve

import com.google.common.collect.Maps
import com.intellij.openapi.project.Project
import com.intellij.util.containers.Queue
import kotlin.collections.*
import org.jetbrains.kotlin.builtins.*
import org.jetbrains.kotlin.builtins.KotlinBuiltIns
import org.jetbrains.kotlin.config.LanguageFeature
import org.jetbrains.kotlin.config.LanguageVersionSettings
import org.jetbrains.kotlin.descriptors.*
import org.jetbrains.kotlin.descriptors.impl.SyntheticFieldDescriptor
import org.jetbrains.kotlin.diagnostics.Errors
import org.jetbrains.kotlin.lexer.KtTokens
import org.jetbrains.kotlin.psi.*
import org.jetbrains.kotlin.psi.psiUtil.*
import org.jetbrains.kotlin.resolve.calls.CallResolver
import org.jetbrains.kotlin.resolve.calls.model.ResolvedCall
import org.jetbrains.kotlin.resolve.calls.smartcasts.DataFlowInfo
import org.jetbrains.kotlin.resolve.calls.util.CallMaker
import org.jetbrains.kotlin.resolve.lazy.ForceResolveUtil
import org.jetbrains.kotlin.resolve.scopes.*
import org.jetbrains.kotlin.types.*
import org.jetbrains.kotlin.types.expressions.ExpressionTypingServices
import org.jetbrains.kotlin.types.expressions.PreliminaryDeclarationVisitor
import org.jetbrains.kotlin.types.expressions.ValueParameterResolver
import org.jetbrains.kotlin.types.expressions.typeInfoFactory.*
import org.jetbrains.kotlin.util.ReenteringLazyValueComputationException

import org.jetbrains.kotlin.config.LanguageFeature.TopLevelSealedInheritance
import org.jetbrains.kotlin.diagnostics.Errors.*
import org.jetbrains.kotlin.resolve.BindingContext.*
import org.jetbrains.kotlin.resolve.descriptorUtil.isEffectivelyExternal
import org.jetbrains.kotlin.types.TypeUtils.NO_EXPECTED_TYPE
import java.util.HashSet

class BodyResolver(
    private val project: Project,
    private val annotationResolver: AnnotationResolver,
    private val bodyResolveCache: BodyResolveCache,
    private val callResolver: CallResolver,
    private val controlFlowAnalyzer: ControlFlowAnalyzer,
    private val declarationsChecker: DeclarationsChecker,
    private val delegatedPropertyResolver: DelegatedPropertyResolver,
    private val expressionTypingServices: ExpressionTypingServices,
    private val analyzerExtensions: AnalyzerExtensions,
    trace: BindingTrace,
    private val valueParameterResolver: ValueParameterResolver,
    private val annotationChecker: AnnotationChecker,
    private val builtIns: KotlinBuiltIns,
    private val overloadChecker: OverloadChecker,
    private val languageVersionSettings: LanguageVersionSettings
) {
    private val trace = ObservableBindingTrace(trace)

    private fun resolveBehaviorDeclarationBodies(c: BodiesResolveContext) {
        resolveSuperTypeEntryLists(c)

        resolvePropertyDeclarationBodies(c)

        resolveAnonymousInitializers(c)
        resolvePrimaryConstructorParameters(c)
        resolveSecondaryConstructors(c)

        resolveFunctionBodies(c)

        if (!c.topDownAnalysisMode.isLocalDeclarations) {
            computeDeferredTypes()
        }
    }

    private fun resolveSecondaryConstructors(c: BodiesResolveContext) {
        for ((key, value) in c.secondaryConstructors) {
            val declaringScope = c.getDeclaringScope(key) ?: error("Declaring scope should be registered before body resolve")
            resolveSecondaryConstructorBody(c.outerDataFlowInfo, trace, key, value, declaringScope)
        }
        if (c.secondaryConstructors.isEmpty()) return
        val visitedConstructors = HashSet<ConstructorDescriptor>()
        for ((_, value) in c.secondaryConstructors) {
            checkCyclicConstructorDelegationCall(value, visitedConstructors)
        }
    }

    fun resolveSecondaryConstructorBody(
        outerDataFlowInfo: DataFlowInfo,
        trace: BindingTrace,
        constructor: KtSecondaryConstructor,
        descriptor: ClassConstructorDescriptor,
        declaringScope: LexicalScope
    ) {
        ForceResolveUtil.forceResolveAllContents(descriptor.annotations)

        resolveFunctionBody(outerDataFlowInfo, trace, constructor, descriptor, declaringScope,
                            { headerInnerScope ->
                                resolveSecondaryConstructorDelegationCall(
                                    outerDataFlowInfo, trace, headerInnerScope, constructor, descriptor
                                )
                            },
                            { scope ->
                                LexicalScopeImpl(
                                    scope, descriptor, scope.isOwnerDescriptorAccessibleByLabel, scope.implicitReceiver,
                                    LexicalScopeKind.CONSTRUCTOR_HEADER
                                )
                            })
    }

    private fun resolveSecondaryConstructorDelegationCall(
        outerDataFlowInfo: DataFlowInfo,
        trace: BindingTrace,
        scope: LexicalScope,
        constructor: KtSecondaryConstructor,
        descriptor: ClassConstructorDescriptor
    ): DataFlowInfo? {
        if (descriptor.isExpect || descriptor.isEffectivelyExternal()) {
            // For expected and external classes, we do not resolve constructor delegation calls because they are prohibited
            return DataFlowInfo.EMPTY
        }

        val results = callResolver.resolveConstructorDelegationCall(
            trace, scope, outerDataFlowInfo,
            descriptor, constructor.getDelegationCall()
        )

        if (results != null && results.isSingleResult) {
            val resolvedCall = results.resultingCall
            recordConstructorDelegationCall(trace, descriptor, resolvedCall)
            return resolvedCall.dataFlowInfoForArguments.resultInfo
        }
        return null
    }

    private fun checkCyclicConstructorDelegationCall(
        constructorDescriptor: ConstructorDescriptor,
        visitedConstructors: MutableSet<ConstructorDescriptor>
    ) {
        if (visitedConstructors.contains(constructorDescriptor)) return

        // if visit constructor that is already in current chain
        // such constructor is on cycle
        val visitedInCurrentChain = HashSet<ConstructorDescriptor>()
        var currentConstructorDescriptor = constructorDescriptor
        while (true) {
            visitedInCurrentChain.add(currentConstructorDescriptor)
            val delegatedConstructorDescriptor = getDelegatedConstructor(currentConstructorDescriptor) ?: break

            // if next delegation call is super or primary constructor or already visited
            if (constructorDescriptor.containingDeclaration != delegatedConstructorDescriptor.containingDeclaration ||
                delegatedConstructorDescriptor.isPrimary ||
                visitedConstructors.contains(delegatedConstructorDescriptor)
            ) {
                break
            }

            if (visitedInCurrentChain.contains(delegatedConstructorDescriptor)) {
                reportEachConstructorOnCycle(delegatedConstructorDescriptor)
                break
            }
            currentConstructorDescriptor = delegatedConstructorDescriptor
        }
        visitedConstructors.addAll(visitedInCurrentChain)
    }

    private fun reportEachConstructorOnCycle(startConstructor: ConstructorDescriptor) {
        var currentConstructor: ConstructorDescriptor? = startConstructor
        do {
            val constructorToReport = DescriptorToSourceUtils.descriptorToDeclaration(currentConstructor!!)
            if (constructorToReport != null) {
                val call = (constructorToReport as KtSecondaryConstructor).getDelegationCall()
                assert(call.calleeExpression != null) { "Callee expression of delegation call should not be null on cycle as there should be explicit 'this' calls" }
                trace.report(CYCLIC_CONSTRUCTOR_DELEGATION_CALL.on(call.calleeExpression!!))
            }

            currentConstructor = getDelegatedConstructor(currentConstructor)
            assert(currentConstructor != null) { "Delegated constructor should not be null in cycle" }
        } while (startConstructor !== currentConstructor)
    }

    private fun getDelegatedConstructor(constructor: ConstructorDescriptor): ConstructorDescriptor? {
        val call = trace.get(CONSTRUCTOR_RESOLVED_DELEGATION_CALL, constructor)
        return if (call == null || !call.status.isSuccess) null else call.resultingDescriptor.original
    }

    fun resolveBodies(c: BodiesResolveContext) {
        resolveBehaviorDeclarationBodies(c)
        controlFlowAnalyzer.process(c)
        declarationsChecker.process(c)
        analyzerExtensions.process(c)
    }

    private fun resolveSuperTypeEntryLists(c: BodiesResolveContext) {
        // TODO : Make sure the same thing is not initialized twice
        for ((classOrObject, descriptor) in c.declaredClasses) {

            resolveSuperTypeEntryList(
                c.outerDataFlowInfo, classOrObject, descriptor,
                descriptor.unsubstitutedPrimaryConstructor,
                descriptor.scopeForConstructorHeaderResolution,
                descriptor.scopeForMemberDeclarationResolution
            )
        }
    }

    fun resolveSuperTypeEntryList(
        outerDataFlowInfo: DataFlowInfo,
        ktClass: KtClassOrObject,
        descriptor: ClassDescriptor,
        primaryConstructor: ConstructorDescriptor?,
        scopeForConstructorResolution: LexicalScope,
        scopeForMemberResolution: LexicalScope
    ) {
        val scopeForConstructor = if (primaryConstructor == null)
            null
        else
            FunctionDescriptorUtil.getFunctionInnerScope(scopeForConstructorResolution, primaryConstructor, trace, overloadChecker)
        if (primaryConstructor == null) {
            checkRedeclarationsInClassHeaderWithoutPrimaryConstructor(descriptor, scopeForConstructorResolution)
        }
        val typeInferrer = expressionTypingServices // TODO : flow

        val supertypes = Maps.newLinkedHashMap<KtTypeReference, KotlinType>()
        val primaryConstructorDelegationCall = arrayOfNulls<ResolvedCall<*>>(1)
        val visitor = object : KtVisitorVoid() {
            private fun recordSupertype(typeReference: KtTypeReference?, supertype: KotlinType?) {
                if (supertype == null) return
                supertypes[typeReference] = supertype
            }

            override fun visitDelegatedSuperTypeEntry(specifier: KtDelegatedSuperTypeEntry) {
                if (descriptor.kind == ClassKind.INTERFACE) {
                    trace.report(DELEGATION_IN_INTERFACE.on(specifier))
                }
                val supertype = trace.bindingContext.get(BindingContext.TYPE, specifier.typeReference)
                recordSupertype(specifier.typeReference, supertype)
                if (supertype != null) {
                    val declarationDescriptor = supertype.constructor.declarationDescriptor
                    if (declarationDescriptor is ClassDescriptor) {
                        val classDescriptor = declarationDescriptor as ClassDescriptor?
                        if (classDescriptor!!.kind != ClassKind.INTERFACE) {
                            trace.report(DELEGATION_NOT_TO_INTERFACE.on(specifier.typeReference!!))
                        }
                    }
                }
                val delegateExpression = specifier.delegateExpression
                if (delegateExpression != null) {
                    val scope = scopeForConstructor ?: scopeForMemberResolution
                    val expectedType = supertype ?: NO_EXPECTED_TYPE
                    typeInferrer.getType(scope, delegateExpression, expectedType, outerDataFlowInfo, trace)
                }

                if (descriptor.isExpect) {
                    trace.report(IMPLEMENTATION_BY_DELEGATION_IN_EXPECT_CLASS.on(specifier))
                } else if (primaryConstructor == null) {
                    trace.report(UNSUPPORTED.on(specifier, "Delegation without primary constructor is not supported"))
                }
            }

            override fun visitSuperTypeCallEntry(call: KtSuperTypeCallEntry) {
                val valueArgumentList = call.valueArgumentList
                val elementToMark = valueArgumentList ?: call
                if (descriptor.kind == ClassKind.INTERFACE) {
                    trace.report(SUPERTYPE_INITIALIZED_IN_INTERFACE.on(elementToMark))
                }
                if (descriptor.isExpect) {
                    trace.report(SUPERTYPE_INITIALIZED_IN_EXPECTED_CLASS.on(elementToMark))
                }
                val typeReference = call.typeReference ?: return
                if (primaryConstructor == null) {
                    if (descriptor.kind != ClassKind.INTERFACE) {
                        trace.report(SUPERTYPE_INITIALIZED_WITHOUT_PRIMARY_CONSTRUCTOR.on(call))
                    }
                    recordSupertype(typeReference, trace.bindingContext.get(BindingContext.TYPE, typeReference))
                    return
                }
                val results = callResolver.resolveFunctionCall(
                    trace, scopeForConstructor!!,
                    CallMaker.makeConstructorCallWithoutTypeArguments(call), NO_EXPECTED_TYPE, outerDataFlowInfo, false
                )
                if (results.isSingleResult) {
                    val supertype = results.resultingDescriptor.returnType
                    recordSupertype(typeReference, supertype)
                    val classDescriptor = TypeUtils.getClassDescriptor(supertype!!)
                    if (classDescriptor != null) {
                        // allow only one delegating constructor
                        if (primaryConstructorDelegationCall[0] == null) {
                            primaryConstructorDelegationCall[0] = results.resultingCall
                        } else {
                            primaryConstructorDelegationCall[0] = null
                        }
                    }
                    // Recording type info for callee to use later in JetObjectLiteralExpression
                    trace.record(PROCESSED, call.calleeExpression, true)
                    trace.record(
                        EXPRESSION_TYPE_INFO, call.calleeExpression,
                        noTypeInfo(results.resultingCall.dataFlowInfoForArguments.resultInfo)
                    )
                } else {
                    recordSupertype(typeReference, trace.bindingContext.get(BindingContext.TYPE, typeReference))
                }
            }

            override fun visitSuperTypeEntry(specifier: KtSuperTypeEntry) {
                val typeReference = specifier.typeReference
                val supertype = trace.bindingContext.get(BindingContext.TYPE, typeReference)
                recordSupertype(typeReference, supertype)
                if (supertype == null) return
                val superClass = TypeUtils.getClassDescriptor(supertype) ?: return
                if (superClass.kind.isSingleton) {
                    // A "singleton in supertype" diagnostic will be reported later
                    return
                }
                if (descriptor.kind != ClassKind.INTERFACE &&
                    descriptor.unsubstitutedPrimaryConstructor != null &&
                    superClass.kind != ClassKind.INTERFACE &&
                    !descriptor.isExpect && !descriptor.isEffectivelyExternal() &&
                    !ErrorUtils.isError(superClass)
                ) {
                    trace.report(SUPERTYPE_NOT_INITIALIZED.on(specifier))
                }
            }

            override fun visitKtElement(element: KtElement) {
                throw UnsupportedOperationException(element.text + " : " + element)
            }
        }

        if (ktClass is KtEnumEntry && DescriptorUtils.isEnumEntry(descriptor) && ktClass.getSuperTypeListEntries().isEmpty()) {
            assert(scopeForConstructor != null) { "Scope for enum class constructor should be non-null: $descriptor" }
            resolveConstructorCallForEnumEntryWithoutInitializer(
                ktClass, descriptor,
                scopeForConstructor!!, outerDataFlowInfo, primaryConstructorDelegationCall
            )
        }

        for (delegationSpecifier in ktClass.superTypeListEntries) {
            delegationSpecifier.accept(visitor)
        }

        if (DescriptorUtils.isAnnotationClass(descriptor) && ktClass.getSuperTypeList() != null) {
            trace.report(SUPERTYPES_FOR_ANNOTATION_CLASS.on(ktClass.getSuperTypeList()!!))
        }

        if (primaryConstructorDelegationCall[0] != null && primaryConstructor != null) {
            @Suppress("UNCHECKED_CAST")
            recordConstructorDelegationCall(
                trace,
                primaryConstructor,
                primaryConstructorDelegationCall[0] as ResolvedCall<ConstructorDescriptor>
            )
        }

        checkSupertypeList(descriptor, supertypes, ktClass)
    }

    private fun checkRedeclarationsInClassHeaderWithoutPrimaryConstructor(
        descriptor: ClassDescriptor, scopeForConstructorResolution: LexicalScope
    ) {
        // Initializing a scope will report errors if any.
        LexicalScopeImpl(
            scopeForConstructorResolution, descriptor, true, null, LexicalScopeKind.CLASS_HEADER,
            TraceBasedLocalRedeclarationChecker(trace, overloadChecker)
        ) {
            // If a class has no primary constructor, it still can have type parameters declared in header.
            for (typeParameter in descriptor.declaredTypeParameters) {
                addClassifierDescriptor(typeParameter)
            }
        }
    }

    private fun resolveConstructorCallForEnumEntryWithoutInitializer(
        ktEnumEntry: KtEnumEntry,
        enumEntryDescriptor: ClassDescriptor,
        scopeForConstructor: LexicalScope,
        outerDataFlowInfo: DataFlowInfo,
        primaryConstructorDelegationCall: Array<ResolvedCall<*>?>
    ) {
        assert(enumEntryDescriptor.kind == ClassKind.ENUM_ENTRY) { "Enum entry expected: $enumEntryDescriptor" }
        val enumClassDescriptor = enumEntryDescriptor.containingDeclaration as ClassDescriptor
        if (enumClassDescriptor.kind != ClassKind.ENUM_CLASS) return
        if (enumClassDescriptor.isExpect) return

        val applicableConstructors = getConstructorForEmptyArgumentsList(enumClassDescriptor)
        if (applicableConstructors.size != 1) {
            trace.report(ENUM_ENTRY_SHOULD_BE_INITIALIZED.on(ktEnumEntry))
            return
        }

        val ktInitializerList = KtPsiFactory(project, false).createEnumEntryInitializerList()
        val ktCallEntry = ktInitializerList.initializers[0] as KtSuperTypeCallEntry
        val call = CallMaker.makeConstructorCallWithoutTypeArguments(ktCallEntry)
        trace.record(BindingContext.TYPE, ktCallEntry.typeReference, enumClassDescriptor.defaultType)
        trace.record(BindingContext.CALL, ktEnumEntry, call)
        val results = callResolver.resolveFunctionCall(trace, scopeForConstructor, call, NO_EXPECTED_TYPE, outerDataFlowInfo, false)
        if (primaryConstructorDelegationCall[0] == null) {
            primaryConstructorDelegationCall[0] = results.resultingCall
        }
    }

    private fun getConstructorForEmptyArgumentsList(descriptor: ClassDescriptor): List<ClassConstructorDescriptor> {
        return descriptor.constructors.filter { constructor -> constructor.valueParameters.all { parameter -> parameter.declaresDefaultValue() || parameter.varargElementType != null } }
    }

    // Returns a set of enum or sealed types of which supertypeOwner is an entry or a member
    private fun getAllowedFinalSupertypes(
        descriptor: ClassDescriptor,
        supertypes: Map<KtTypeReference, KotlinType>,
        ktClassOrObject: KtClassOrObject
    ): Set<TypeConstructor> {
        return if (ktClassOrObject is KtEnumEntry) {
            setOf((descriptor.containingDeclaration as ClassDescriptor).typeConstructor)
        } else if (languageVersionSettings.supportsFeature(TopLevelSealedInheritance) && DescriptorUtils.isTopLevelDeclaration(descriptor)) {
            var parentEnumOrSealed = emptySet<TypeConstructor>()
            // TODO: improve diagnostic when top level sealed inheritance is disabled
            for (supertype in supertypes.values) {
                val classifierDescriptor = supertype.constructor.declarationDescriptor
                if (DescriptorUtils.isSealedClass(classifierDescriptor) && DescriptorUtils.isTopLevelDeclaration(classifierDescriptor)) {
                    parentEnumOrSealed = setOf(classifierDescriptor!!.typeConstructor)
                }
            }
            parentEnumOrSealed
        } else {
            var currentDescriptor = descriptor
            val parentEnumOrSealed = mutableSetOf<TypeConstructor>()
            while (currentDescriptor.containingDeclaration is ClassDescriptor) {
                currentDescriptor = currentDescriptor.containingDeclaration as ClassDescriptor
                if (DescriptorUtils.isSealedClass(currentDescriptor)) {
                    parentEnumOrSealed.add(currentDescriptor.typeConstructor)
                }
            }
            parentEnumOrSealed
        }
    }

    private fun recordConstructorDelegationCall(
        trace: BindingTrace,
        constructor: ConstructorDescriptor,
        call: ResolvedCall<ConstructorDescriptor>
    ) {
        trace.record(CONSTRUCTOR_RESOLVED_DELEGATION_CALL, constructor, call)
    }

    private fun checkSupertypeList(
        supertypeOwner: ClassDescriptor,
        supertypes: Map<KtTypeReference, KotlinType>,
        ktClassOrObject: KtClassOrObject
    ) {
        val allowedFinalSupertypes = getAllowedFinalSupertypes(supertypeOwner, supertypes, ktClassOrObject)
        val typeConstructors = HashSet<TypeConstructor>()
        var classAppeared = false
        for ((typeReference, supertype) in supertypes) {

            val typeElement = typeReference.typeElement
            if (typeElement is KtFunctionType) {
                for (parameter in typeElement.parameters) {
                    val nameIdentifier = parameter.nameIdentifier

                    if (nameIdentifier != null) {
                        trace.report(Errors.UNSUPPORTED.on(nameIdentifier, "named parameter in function type in supertype position"))
                    }
                }
            }

            var addSupertype = true

            val classDescriptor = TypeUtils.getClassDescriptor(supertype)
            if (classDescriptor != null) {
                if (ErrorUtils.isError(classDescriptor)) continue

                if (supertype.isExtensionFunctionType) {
                    trace.report(SUPERTYPE_IS_EXTENSION_FUNCTION_TYPE.on(typeReference))
                } else if (supertype.isSuspendFunctionType) {
                    trace.report(SUPERTYPE_IS_SUSPEND_FUNCTION_TYPE.on(typeReference))
                }

                if (classDescriptor.kind != ClassKind.INTERFACE) {
                    if (supertypeOwner.kind == ClassKind.ENUM_CLASS) {
                        trace.report(CLASS_IN_SUPERTYPE_FOR_ENUM.on(typeReference))
                        addSupertype = false
                    } else if (supertypeOwner.kind == ClassKind.INTERFACE &&
                        !classAppeared && !supertype.isDynamic() /* avoid duplicate diagnostics */) {
                        trace.report(INTERFACE_WITH_SUPERCLASS.on(typeReference))
                        addSupertype = false
                    } else if (ktClassOrObject.hasModifier(KtTokens.DATA_KEYWORD) && !languageVersionSettings.supportsFeature(
                            LanguageFeature.DataClassInheritance
                        )
                    ) {
                        trace.report(DATA_CLASS_CANNOT_HAVE_CLASS_SUPERTYPES.on(typeReference))
                        addSupertype = false
                    } else if (DescriptorUtils.isSubclass(classDescriptor, builtIns.throwable)) {
                        if (!supertypeOwner.declaredTypeParameters.isEmpty()) {
                            trace.report(GENERIC_THROWABLE_SUBCLASS.on(ktClassOrObject.typeParameterList!!))
                            addSupertype = false
                        } else if (!supertypeOwner.typeConstructor.parameters.isEmpty()) {
                            if (languageVersionSettings
                                    .supportsFeature(LanguageFeature.ProhibitInnerClassesOfGenericClassExtendingThrowable)
                            ) {
                                trace.report(INNER_CLASS_OF_GENERIC_THROWABLE_SUBCLASS.on(ktClassOrObject))
                                addSupertype = false
                            } else {
                                trace.report(INNER_CLASS_OF_GENERIC_THROWABLE_SUBCLASS_WARNING.on(ktClassOrObject))
                            }
                        }
                    }

                    if (classAppeared) {
                        trace.report(MANY_CLASSES_IN_SUPERTYPE_LIST.on(typeReference))
                    } else {
                        classAppeared = true
                    }
                }
            } else {
                trace.report(SUPERTYPE_NOT_A_CLASS_OR_INTERFACE.on(typeReference))
            }

            val constructor = supertype.constructor
            if (addSupertype && !typeConstructors.add(constructor)) {
                trace.report(SUPERTYPE_APPEARS_TWICE.on(typeReference))
            }

            if (classDescriptor == null) return
            if (classDescriptor.kind.isSingleton) {
                if (!DescriptorUtils.isEnumEntry(classDescriptor)) {
                    trace.report(SINGLETON_IN_SUPERTYPE.on(typeReference))
                }
            } else if (!allowedFinalSupertypes.contains(constructor)) {
                if (DescriptorUtils.isSealedClass(classDescriptor)) {
                    var containingDescriptor: DeclarationDescriptor? = supertypeOwner.containingDeclaration
                    while (containingDescriptor != null && containingDescriptor !== classDescriptor) {
                        containingDescriptor = containingDescriptor.containingDeclaration
                    }
                    if (containingDescriptor == null) {
                        trace.report(SEALED_SUPERTYPE.on(typeReference))
                    } else {
                        trace.report(SEALED_SUPERTYPE_IN_LOCAL_CLASS.on(typeReference))
                    }
                } else if (classDescriptor.isFinalOrEnum) {
                    trace.report(FINAL_SUPERTYPE.on(typeReference))
                } else if (KotlinBuiltIns.isEnum(classDescriptor)) {
                    trace.report(CLASS_CANNOT_BE_EXTENDED_DIRECTLY.on(typeReference, classDescriptor))
                }
            }
        }
    }

    private fun resolveAnonymousInitializers(c: BodiesResolveContext) {
        for ((initializer, descriptor) in c.anonymousInitializers) {
            resolveAnonymousInitializer(c.outerDataFlowInfo, initializer, descriptor)
        }
    }

    fun resolveAnonymousInitializer(
        outerDataFlowInfo: DataFlowInfo,
        anonymousInitializer: KtAnonymousInitializer,
        classDescriptor: ClassDescriptorWithResolutionScopes
    ) {
        val scopeForInitializers = classDescriptor.scopeForInitializerResolution
        val body = anonymousInitializer.body
        if (body != null) {
            PreliminaryDeclarationVisitor.createForDeclaration(
                anonymousInitializer.parent.parent as KtDeclaration, trace, languageVersionSettings
            )
            expressionTypingServices.getTypeInfo(
                scopeForInitializers, body, NO_EXPECTED_TYPE, outerDataFlowInfo, trace, /*isStatement = */true
            )
        }
        processModifiersOnInitializer(anonymousInitializer, scopeForInitializers)
        if (classDescriptor.constructors.isEmpty()) {
            trace.report(ANONYMOUS_INITIALIZER_IN_INTERFACE.on(anonymousInitializer))
        }
        if (classDescriptor.isExpect) {
            trace.report(EXPECTED_DECLARATION_WITH_BODY.on(anonymousInitializer))
        }
    }

    private fun processModifiersOnInitializer(owner: KtModifierListOwner, scope: LexicalScope) {
        annotationChecker.check(owner, trace, null)
        ModifierCheckerCore.check(owner, trace, null, languageVersionSettings)
        val modifierList = owner.modifierList ?: return

        annotationResolver.resolveAnnotationsWithArguments(scope, modifierList, trace)
    }

    private fun resolvePrimaryConstructorParameters(c: BodiesResolveContext) {
        for ((klass, classDescriptor) in c.declaredClasses) {
            val unsubstitutedPrimaryConstructor = classDescriptor.unsubstitutedPrimaryConstructor
            if (unsubstitutedPrimaryConstructor != null) {
                ForceResolveUtil.forceResolveAllContents(unsubstitutedPrimaryConstructor.annotations)

                val parameterScope = getPrimaryConstructorParametersScope(
                    classDescriptor.scopeForConstructorHeaderResolution,
                    unsubstitutedPrimaryConstructor
                )
                valueParameterResolver.resolveValueParameters(
                    klass.primaryConstructorParameters,
                    unsubstitutedPrimaryConstructor.valueParameters,
                    parameterScope, c.outerDataFlowInfo, trace
                )
                // Annotations on value parameter and constructor parameter could be splitted
                resolveConstructorPropertyDescriptors(klass)
            }
        }
    }

    private fun resolveConstructorPropertyDescriptors(ktClassOrObject: KtClassOrObject) {
        for (parameter in ktClassOrObject.primaryConstructorParameters) {
            val descriptor = trace.bindingContext.get(BindingContext.PRIMARY_CONSTRUCTOR_PARAMETER, parameter)
            if (descriptor != null) {
                ForceResolveUtil.forceResolveAllContents(descriptor.annotations)

                if (languageVersionSettings.supportsFeature(LanguageFeature.ProhibitErroneousExpressionsInAnnotationsWithUseSiteTargets)) {
                    val getterDescriptor = descriptor.getter
                    if (getterDescriptor != null) {
                        ForceResolveUtil.forceResolveAllContents(getterDescriptor.annotations)
                    }

                    val setterDescriptor = descriptor.setter
                    if (setterDescriptor != null) {
                        ForceResolveUtil.forceResolveAllContents(setterDescriptor.annotations)
                    }
                }
            }
        }
    }

    private fun getPrimaryConstructorParametersScope(
        originalScope: LexicalScope,
        unsubstitutedPrimaryConstructor: ConstructorDescriptor
    ): LexicalScope {
        return LexicalScopeImpl(
            originalScope, unsubstitutedPrimaryConstructor, false, null,
            LexicalScopeKind.DEFAULT_VALUE, LocalRedeclarationChecker.DO_NOTHING
        ) {
            for (valueParameter in unsubstitutedPrimaryConstructor.valueParameters) {
                addVariableDescriptor(valueParameter)
            }
        }
    }

    fun resolveProperty(
        c: BodiesResolveContext,
        property: KtProperty,
        propertyDescriptor: PropertyDescriptor
    ) {
        computeDeferredType(propertyDescriptor.returnType)

        PreliminaryDeclarationVisitor.createForDeclaration(property, trace, languageVersionSettings)
        val initializer = property.initializer
        val propertyHeaderScope = ScopeUtils.makeScopeForPropertyHeader(getScopeForProperty(c, property), propertyDescriptor)

        if (initializer != null) {
            resolvePropertyInitializer(c.outerDataFlowInfo, property, propertyDescriptor, initializer, propertyHeaderScope)
        }

        val delegateExpression = property.delegateExpression
        if (delegateExpression != null) {
            assert(initializer == null) { "Initializer should be null for delegated property : " + property.text }
            resolvePropertyDelegate(c.outerDataFlowInfo, property, propertyDescriptor, delegateExpression, propertyHeaderScope)
        }

        resolvePropertyAccessors(c, property, propertyDescriptor)

        ForceResolveUtil.forceResolveAllContents(propertyDescriptor.annotations)
    }

    private fun resolvePropertyDeclarationBodies(c: BodiesResolveContext) {

        // Member properties
        val processed = HashSet<KtProperty>()
        for ((key, _) in c.declaredClasses) {
            if (key !is KtClass) continue

            for (property in key.getProperties()) {
                val propertyDescriptor = c.properties[property]!!

                resolveProperty(c, property, propertyDescriptor)
                processed.add(property)
            }
        }

        // Top-level properties & properties of objects
        for ((property, propertyDescriptor) in c.properties) {
            if (processed.contains(property)) continue

            resolveProperty(c, property, propertyDescriptor)
        }
    }

    private fun makeScopeForPropertyAccessor(
        c: BodiesResolveContext, accessor: KtPropertyAccessor, descriptor: PropertyDescriptor
    ): LexicalScope {
        val accessorDeclaringScope = c.getDeclaringScope(accessor) ?: error("Scope for accessor " + accessor.text + " should exists")
        val headerScope = ScopeUtils.makeScopeForPropertyHeader(accessorDeclaringScope, descriptor)
        return LexicalScopeImpl(
            headerScope, descriptor, true, descriptor.extensionReceiverParameter,
            LexicalScopeKind.PROPERTY_ACCESSOR_BODY
        )
    }

    private fun resolvePropertyAccessors(
        c: BodiesResolveContext,
        property: KtProperty,
        propertyDescriptor: PropertyDescriptor
    ) {
        val fieldAccessTrackingTrace = createFieldTrackingTrace(propertyDescriptor)

        val getter = property.getter
        val getterDescriptor = propertyDescriptor.getter

        val forceResolveAnnotations =
            languageVersionSettings.supportsFeature(LanguageFeature.ProhibitErroneousExpressionsInAnnotationsWithUseSiteTargets)

        if (getterDescriptor != null) {
            if (getter != null) {
                val accessorScope = makeScopeForPropertyAccessor(c, getter, propertyDescriptor)
                resolveFunctionBody(c.outerDataFlowInfo, fieldAccessTrackingTrace, getter, getterDescriptor, accessorScope)
            }

            if (getter != null || forceResolveAnnotations) {
                ForceResolveUtil.forceResolveAllContents(getterDescriptor.annotations)
            }
        }

        val setter = property.setter
        val setterDescriptor = propertyDescriptor.setter

        if (setterDescriptor != null) {
            if (setter != null) {
                val accessorScope = makeScopeForPropertyAccessor(c, setter, propertyDescriptor)
                resolveFunctionBody(c.outerDataFlowInfo, fieldAccessTrackingTrace, setter, setterDescriptor, accessorScope)
            }

            if (setter != null || forceResolveAnnotations) {
                ForceResolveUtil.forceResolveAllContents(setterDescriptor.annotations)
            }
        }
    }

    private fun createFieldTrackingTrace(propertyDescriptor: PropertyDescriptor): ObservableBindingTrace {
        return ObservableBindingTrace(trace).addHandler(
            BindingContext.REFERENCE_TARGET,
            { _, expression, descriptor ->
                if (expression is KtSimpleNameExpression && descriptor is SyntheticFieldDescriptor) {
                    trace.record(
                        BindingContext.BACKING_FIELD_REQUIRED,
                        propertyDescriptor
                    )
                }
            }
        )
    }

    private fun resolvePropertyDelegate(
        outerDataFlowInfo: DataFlowInfo,
        property: KtProperty,
        propertyDescriptor: PropertyDescriptor,
        delegateExpression: KtExpression,
        propertyHeaderScope: LexicalScope
    ) {
        delegatedPropertyResolver.resolvePropertyDelegate(
            outerDataFlowInfo,
            property,
            propertyDescriptor,
            delegateExpression,
            propertyHeaderScope,
            trace
        )
    }

    private fun resolvePropertyInitializer(
        outerDataFlowInfo: DataFlowInfo,
        property: KtProperty,
        propertyDescriptor: PropertyDescriptor,
        initializer: KtExpression,
        propertyHeader: LexicalScope
    ) {
        val propertyDeclarationInnerScope = ScopeUtils.makeScopeForPropertyInitializer(propertyHeader, propertyDescriptor)
        val expectedTypeForInitializer = if (property.typeReference != null) propertyDescriptor.type else NO_EXPECTED_TYPE
        if (propertyDescriptor.compileTimeInitializer == null) {
            expressionTypingServices.getType(
                propertyDeclarationInnerScope, initializer, expectedTypeForInitializer,
                outerDataFlowInfo, trace
            )
        }
    }

    private fun getScopeForProperty(c: BodiesResolveContext, property: KtProperty): LexicalScope {
        return c.getDeclaringScope(property) ?: error("Scope for property " + property.text + " should exists")
    }

    private fun resolveFunctionBodies(c: BodiesResolveContext) {
        for ((declaration, value) in c.functions) {

            val scope = c.getDeclaringScope(declaration) ?: error("Scope is null: " + declaration.getElementTextWithContext())

            if (!c.topDownAnalysisMode.isLocalDeclarations && bodyResolveCache !is BodyResolveCache.ThrowException &&
                expressionTypingServices.statementFilter !== StatementFilter.NONE
            ) {
                bodyResolveCache.resolveFunctionBody(declaration).addOwnDataTo(trace, true)
            } else {
                resolveFunctionBody(c.outerDataFlowInfo, trace, declaration, value, scope)
            }
        }
    }

    fun resolveFunctionBody(
        outerDataFlowInfo: DataFlowInfo,
        trace: BindingTrace,
        function: KtDeclarationWithBody,
        functionDescriptor: FunctionDescriptor,
        declaringScope: LexicalScope
    ) {
        computeDeferredType(functionDescriptor.returnType)

        resolveFunctionBody(outerDataFlowInfo, trace, function, functionDescriptor, declaringScope, null, null)

        assert(functionDescriptor.returnType != null)
    }

    private fun resolveFunctionBody(
        outerDataFlowInfo: DataFlowInfo,
        trace: BindingTrace,
        function: KtDeclarationWithBody,
        functionDescriptor: FunctionDescriptor,
        scope: LexicalScope,
        beforeBlockBody: Function1<LexicalScope, DataFlowInfo?>?,
        // Creates wrapper scope for header resolution if necessary (see resolveSecondaryConstructorBody)
        headerScopeFactory: Function1<LexicalScope, LexicalScope>?
    ) {
        PreliminaryDeclarationVisitor.createForDeclaration(function, trace, languageVersionSettings)
        var innerScope = FunctionDescriptorUtil.getFunctionInnerScope(scope, functionDescriptor, trace, overloadChecker)
        val valueParameters = function.valueParameters
        val valueParameterDescriptors = functionDescriptor.valueParameters

        val headerScope = headerScopeFactory?.invoke(innerScope) ?: innerScope
        valueParameterResolver.resolveValueParameters(
            valueParameters, valueParameterDescriptors, headerScope, outerDataFlowInfo, trace
        )

        // Synthetic "field" creation
        if (functionDescriptor is PropertyAccessorDescriptor && functionDescriptor.getExtensionReceiverParameter() == null) {
            val property = function.parent as KtProperty
            val fieldDescriptor = SyntheticFieldDescriptor(functionDescriptor, property)
            innerScope = LexicalScopeImpl(
                innerScope, functionDescriptor, true, null,
                LexicalScopeKind.PROPERTY_ACCESSOR_BODY,
                LocalRedeclarationChecker.DO_NOTHING
            ) {
                addVariableDescriptor(fieldDescriptor)
            }
            // Check parameter name shadowing
            for (parameter in function.valueParameters) {
                if (SyntheticFieldDescriptor.NAME == parameter.nameAsName) {
                    trace.report(Errors.ACCESSOR_PARAMETER_NAME_SHADOWING.on(parameter))
                }
            }
        }

        var dataFlowInfo: DataFlowInfo? = null

        if (beforeBlockBody != null) {
            dataFlowInfo = beforeBlockBody.invoke(headerScope)
        }

        if (function.hasBody()) {
            expressionTypingServices.checkFunctionReturnType(
                innerScope, function, functionDescriptor, dataFlowInfo ?: outerDataFlowInfo, null, trace
            )
        }

        assert(functionDescriptor.returnType != null)
    }

    fun resolveConstructorParameterDefaultValues(
        outerDataFlowInfo: DataFlowInfo,
        trace: BindingTrace,
        constructor: KtPrimaryConstructor,
        constructorDescriptor: ConstructorDescriptor,
        declaringScope: LexicalScope
    ) {
        val valueParameters = constructor.valueParameters
        val valueParameterDescriptors = constructorDescriptor.valueParameters

        val scope = getPrimaryConstructorParametersScope(declaringScope, constructorDescriptor)

        valueParameterResolver.resolveValueParameters(valueParameters, valueParameterDescriptors, scope, outerDataFlowInfo, trace)
    }

    private fun computeDeferredType(type: KotlinType?) {
        // handle type inference loop: function or property body contains a reference to itself
        // fun f() = { f() }
        // val x = x
        // type resolution must be started before body resolution
        if (type is DeferredType) {
            val deferredType = type as DeferredType?
            if (!deferredType!!.isComputed()) {
                deferredType.delegate
            }
        }
    }

    private fun computeDeferredTypes() {
        val deferredTypes = trace.getKeys(DEFERRED_TYPE)
        if (deferredTypes.isEmpty()) {
            return
        }
        // +1 is a work around against new Queue(0).addLast(...) bug // stepan.koltsov@ 2011-11-21
        val queue = Queue<DeferredType>(deferredTypes.size + 1)
        trace.addHandler(DEFERRED_TYPE, { _, key, _ -> queue.addLast(key.data) })
        for (deferredType in deferredTypes) {
            queue.addLast(deferredType.data)
        }
        while (!queue.isEmpty) {
            val deferredType = queue.pullFirst()
            if (!deferredType.isComputed()) {
                try {
                    deferredType.delegate // to compute
                } catch (e: ReenteringLazyValueComputationException) {
                    // A problem should be reported while computing the type
                }

            }
        }
    }
}
