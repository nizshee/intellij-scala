package org.jetbrains.plugins.scala.actions

import org.jetbrains.plugins.scala.lang.psi.types.api.{ParameterizedType, UndefinedType}
import org.jetbrains.plugins.scala.lang.psi.types.nonvalue.ScMethodType
import org.jetbrains.plugins.scala.lang.psi.types.{ScAbstractType, ScType}


sealed trait ConformanceCondition {
  def satisfy: Boolean
  var _msg: String = ""
  def +(msg: String): Unit = _msg = msg
  def msg: String = _msg
}

object ConformanceCondition {

  trait Variance {
    def satisfy: Boolean
  }

  case class Invariant(param: String, relation: Relation.Equivalence) extends Variance {
    override def satisfy: Boolean = relation.satisfy
  }
  case class Covariant(param: String, relation: Relation.Conformance) extends Variance {
    override def satisfy: Boolean = relation.satisfy
  }
  case class Contrvariant(param: String, relation: Relation.Conformance) extends Variance {
    override def satisfy: Boolean = relation.satisfy
  }


  case class Same(equiv: Relation.Equivalence, relation: Relation.Conformance) extends ConformanceCondition {
    override def satisfy: Boolean = equiv.satisfy && relation.satisfy
  }

  case class Projection(conforms: Relation.Conformance) extends ConformanceCondition {
    override def satisfy: Boolean = conforms.satisfy
  }

  case class PolymorphicArgument(left: ScAbstractType, right: ScType, satisfy: Boolean) extends ConformanceCondition

  case class Transitive(left: ScType, middle: ScType, right: ScType, lm: Relation.Conformance, mr: Relation.Conformance) extends ConformanceCondition {
    override def satisfy: Boolean = lm.satisfy && mr.satisfy
  }

  case class TypeUpper(upper: ScType, `type`: ScType, satisfy: Boolean) extends ConformanceCondition

  case class TypeLower(`type`: ScType, lower: ScType, satisfy: Boolean) extends ConformanceCondition

  case class Equivalent(equivalence: Relation.Equivalence) extends ConformanceCondition {
    override def satisfy: Boolean = equivalence.satisfy
  }

  case class Parametrize(left: ParameterizedType, right: ParameterizedType, equals: Option[Relation.Equivalence], sameLength: Boolean,conform: Seq[Variance]) extends ConformanceCondition {
    override def satisfy: Boolean = left.typeArguments.size == right.typeArguments.size && right.typeArguments.size == conform.size &&
      equals.exists(_.satisfy) && conform.forall(_.satisfy)
  }

  case class ToAny(right: ScType) extends ConformanceCondition {
    override def satisfy: Boolean = true
  }

  case class FromNothing(left: ScType) extends ConformanceCondition {
    override def satisfy: Boolean = true
  }

  case class FromNull(left: ScType, anyRef: Boolean, notNull: Boolean) extends ConformanceCondition {
    override def satisfy: Boolean = anyRef && !notNull
  }

  case class BaseClass(left: ScType, right: ScType, satisfy: Boolean) extends ConformanceCondition

  case class Method(left: ScMethodType, right: ScMethodType, sameLen: Boolean, ret: Option[Relation.Conformance],
                    args: Seq[Invariant]) extends ConformanceCondition {
    override def satisfy: Boolean = sameLen && ret.exists(_.satisfy) && args.forall(_.satisfy)
  }

  case class Undefined(left: ScType, right: UndefinedType, cond: ScType) extends ConformanceCondition {
    override def satisfy: Boolean = true
  }

  case class UndefinedLower(left: UndefinedType, right: UndefinedType) extends ConformanceCondition {
    override def satisfy: Boolean = ???
  }

}

sealed trait Relation {
  def satisfy: Boolean
}

object Relation {
  case class Equivalence(left: ScType, right: ScType, satisfy: Boolean) extends Relation

  case class Conformance(left: ScType, right: ScType, conditions: Seq[ConformanceCondition]) extends Relation {
    def satisfy: Boolean = conditions.exists(_.satisfy)
  }
}

sealed trait AsSpecificAsCondition {
  def satisfy: Boolean
}

object AsSpecificAsCondition {
  case class Method(left: ScType, right: ScType, satisfy: Boolean) extends AsSpecificAsCondition
  case class Polymorphic(satisfy: Boolean) extends AsSpecificAsCondition
  case class Other(left: ScType, right: ScType, satisfy: Boolean) extends AsSpecificAsCondition
}
