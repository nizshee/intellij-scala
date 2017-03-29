package org.jetbrains.plugins.scala.actions

import org.jetbrains.plugins.scala.lang.psi.types.ScType


sealed abstract class ConformanceCondition(left: ScType, right: ScType)

object ConformanceCondition {
  case class Equiv(left: ScType, right: ScType) extends ConformanceCondition(left, right)

}
