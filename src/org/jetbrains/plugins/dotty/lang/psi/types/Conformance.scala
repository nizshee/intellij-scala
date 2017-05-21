package org.jetbrains.plugins.dotty.lang.psi.types

import com.intellij.openapi.util.Computable
import com.intellij.psi.PsiClass
import org.jetbrains.plugins.scala.actions.DebugTypesAction
import org.jetbrains.plugins.scala.actions.debug_types.DTHandler
import org.jetbrains.plugins.scala.lang.psi.types._
import org.jetbrains.plugins.scala.macroAnnotations.uninstrumented

/**
  * @author adkozlov
  */
object Conformance extends api.Conformance {
  override implicit lazy val typeSystem = DottyTypeSystem

  @uninstrumented("handler")
  override protected def computable(left: ScType, right: ScType, visited: Set[PsiClass], checkWeak: Boolean,
                                    handler: Option[DTHandler.Conformance]) = new Computable[(Boolean, ScUndefinedSubstitutor)] {
    override def compute(): (Boolean, ScUndefinedSubstitutor) = (false, ScUndefinedSubstitutor())
  }

  private def isSubType(left: ScType, right: ScType) = right match {
    case DottyNoType => false
    case _ => if (left eq right) true else firstTry(left, right)
  }

  private def firstTry(left: ScType, right: ScType): Boolean = false
}
