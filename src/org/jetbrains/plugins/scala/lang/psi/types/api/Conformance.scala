package org.jetbrains.plugins.scala.lang.psi.types.api

import java.util.concurrent.ConcurrentMap

import com.intellij.openapi.progress.ProgressManager
import com.intellij.openapi.util.Computable
import com.intellij.psi.PsiClass
import com.intellij.util.containers.ContainerUtil
import org.jetbrains.plugins.scala.actions.debug_types.{CCondition, DTHandler}
import org.jetbrains.plugins.scala.actions.DebugTypesAction
import org.jetbrains.plugins.scala.caches.RecursionManager
import org.jetbrains.plugins.scala.lang.psi.types._
import org.jetbrains.plugins.scala.macroAnnotations.uninstrumented



/**
  * @author adkozlov
  */
trait Conformance extends TypeSystemOwner {
  type Data = (ScType, ScType, Boolean)
  type Result = (Boolean, ScUndefinedSubstitutor)

  private val guard = RecursionManager.RecursionGuard[Data, Result](s"${typeSystem.name}.conformance.guard")

  private val cache: ConcurrentMap[(ScType, ScType, Boolean), (Boolean, ScUndefinedSubstitutor)] =
    ContainerUtil.createConcurrentWeakMap[(ScType, ScType, Boolean), (Boolean, ScUndefinedSubstitutor)]()

  /**
    * Checks, whether the following assignment is correct:
    * val x: l = (y: r)
    */
  @uninstrumented("handler")
  final def conformsInner(left: ScType, right: ScType,
                          visited: Set[PsiClass] = Set.empty,
                          substitutor: ScUndefinedSubstitutor = ScUndefinedSubstitutor(),
                          checkWeak: Boolean = false, handler: Option[DTHandler.Conformance] = None): Result = {
    ProgressManager.checkCanceled()

    if (left.equiv(Any) || right.equiv(Nothing)) {
      handler.foreach { h =>
        if (left equiv Any) h + CCondition.ToAny(right)
        else h + CCondition.FromNothing(left)
      }
      return (true, substitutor)
    }

    val key = (left, right, checkWeak)

    val tuple = cache.get(key)
    if (tuple != null && handler.isEmpty) {
      if (substitutor.isEmpty) return tuple
      return tuple.copy(_2 = substitutor + tuple._2)
    }
    if (guard.currentStackContains(key)) {
      return (false, ScUndefinedSubstitutor())
    }

    val res = guard.doPreventingRecursion(key, computable(left, right, visited, checkWeak, handler))
    if (res == null) return (false, ScUndefinedSubstitutor())
    cache.put(key, res)

    if (substitutor.isEmpty) return res
    res.copy(_2 = substitutor + res._2)
  }

  final def clearCache(): Unit = cache.clear()

  @uninstrumented("handler")
  protected def computable(left: ScType, right: ScType,
                           visited: Set[PsiClass],
                           checkWeak: Boolean, handler: Option[DTHandler.Conformance]): Computable[(Boolean, ScUndefinedSubstitutor)]
}
