package org.jetbrains.plugins.scala.actions

import org.jetbrains.plugins.scala.actions.ConformanceCondition._
import org.jetbrains.plugins.scala.actions.Relation.{Conformance, Equivalence}
import org.jetbrains.plugins.scala.lang.psi.types.ScalaTypeSystem
import org.jetbrains.plugins.scala.lang.psi.types.api.TypeSystem


object DebugConformanceAdapter {

  implicit val typeSystem: TypeSystem = ScalaTypeSystem

  def adaptConditions(condition: ConformanceCondition): Seq[ConformanceCondition] = condition match {
    case Transitive(l, m, _, _, mr) if l.equiv(m) => mr.conditions
    case Transitive(_, m, r, lm, _) if m.equiv(r) => lm.conditions
    case _ => Seq(condition)
  }

  def apply(r: Relation.Conformance): Relation.Conformance = {
    val nConditions = r.conditions.flatMap(adaptConditions).map {
      case Same(equiv, relation) => Same(equiv, apply(relation))
      case Projection(conforms) => Projection(apply(conforms))
      case Transitive(left, middle, right, lm, mr) =>
        Transitive(left, middle, right, apply(lm), apply(mr))
      case Parametrize(left, right, equals, sameLength, conform) =>
        Parametrize(left, right, equals, sameLength, conform.map {
          case Contrvariant(param, relation) => Contrvariant(param, apply(relation))
          case Covariant(param, relation) => Covariant(param, apply(relation))
          case i => i
        })
      case ExistentialRight(left, right, conformance) =>
        ExistentialRight(left, right, apply(conformance))
      case CompoundLeft(left, right, signatures, aliases, relations) =>
        CompoundLeft(left, right, signatures, aliases, relations.map(apply))
      case CompoundRight(left, right, relations) => CompoundRight(left, right, relations.map(apply))
      case c => c
    }
    r.copy(conditions = nConditions)
  }
}
