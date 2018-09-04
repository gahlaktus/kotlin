/*
 * Copyright 2010-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license
 * that can be found in the license/LICENSE.txt file.
 */

package org.jetbrains.kotlin.util

import org.jetbrains.kotlin.descriptors.CallableMemberDescriptor
import org.jetbrains.kotlin.descriptors.Modality
import org.jetbrains.kotlin.resolve.DescriptorUtils
import org.jetbrains.kotlin.resolve.OverridingUtil
import org.jetbrains.kotlin.resolve.calls.callResolverUtil.isOrOverridesSynthesized
/**
 * Given a fake override, returns an overridden non-abstract function from an interface which is the actual implementation of this function
 * that should be called when the given fake override is called.
 */
fun findImplementationFromInterface(descriptor: CallableMemberDescriptor): CallableMemberDescriptor? {
    val overridden = OverridingUtil.getOverriddenDeclarations(descriptor)
    val filtered = OverridingUtil.filterOutOverridden(overridden)

    val result = filtered.firstOrNull { it.modality != Modality.ABSTRACT } ?: return null

    if (DescriptorUtils.isClassOrEnumClass(result.containingDeclaration)) return null

    return result
}