package org.jetbrains.plugins.scala.actions

import com.intellij.psi.PsiNamedElement
import org.jetbrains.plugins.scala.actions.DCHandler.Substitutor
import org.jetbrains.plugins.scala.lang.psi.types.api.{ParameterizedType, UndefinedType}
import org.jetbrains.plugins.scala.lang.psi.types.nonvalue.ScMethodType
import org.jetbrains.plugins.scala.lang.psi.types.{ScAbstractType, ScCompoundType, ScExistentialArgument, ScExistentialType, ScType, Signature, TypeAliasSignature}


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

  case class Invariant(param: String, relation: Relation.Equivalence, restriction: Boolean = false) extends Variance {
    override def satisfy: Boolean = relation.satisfy
  }
  case class Covariant(param: String, relation: Relation.Conformance) extends Variance {
    override def satisfy: Boolean = relation.satisfy
  }
  case class Contrvariant(param: String, relation: Relation.Conformance) extends Variance {
    override def satisfy: Boolean = relation.satisfy
  }


  case class Projection(conforms: Relation.Conformance) extends ConformanceCondition {
    override def satisfy: Boolean = conforms.satisfy
  }

  case class AbstractLeft(left: ScAbstractType, right: ScType, upper: ScType, uConditions: Seq[ConformanceCondition],
                          lower: ScType, lConfitions: Seq[ConformanceCondition]) extends ConformanceCondition {
    override def satisfy: Boolean = uConditions.exists(_.satisfy) && lConfitions.exists(_.satisfy)
  }

  case class AbstractRight(left: ScType, right: ScAbstractType, upper: ScType, uConditions: Seq[ConformanceCondition],
                          lower: ScType, lConfitions: Seq[ConformanceCondition]) extends ConformanceCondition {
    override def satisfy: Boolean = uConditions.exists(_.satisfy) && lConfitions.exists(_.satisfy)
  }

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

  case class Todo(reason: String, satisfy: Boolean) extends ConformanceCondition

  case class Method(left: ScMethodType, right: ScMethodType, sameLen: Boolean, ret: Option[Relation.Conformance],
                    args: Seq[Invariant]) extends ConformanceCondition {
    override def satisfy: Boolean = sameLen && ret.exists(_.satisfy) && args.forall(_.satisfy)
  }

  case class Polymorphic(il: ScType, ir: ScType, sameLength: Boolean,
                         args: Seq[(Relation.Conformance, Relation.Conformance)], i: Option[Relation.Conformance]) extends ConformanceCondition {
    override def satisfy: Boolean = sameLength && args.forall(p => p._1.satisfy && p._2.satisfy) && i.exists(_.satisfy)
  }

  case class Undefined(left: ScType, right: UndefinedType, cond: ScType) extends ConformanceCondition {
    override def satisfy: Boolean = true
  }

  case class CompoundRight(left: ScType, right: ScCompoundType, relations: Seq[Relation.Conformance]) extends ConformanceCondition {
    override def satisfy: Boolean = relations.exists(_.satisfy)
  }

  case class CompoundLeft(left: ScCompoundType, right: ScType,
                          signatures: Map[(Signature, ScType), PsiNamedElement],
                          aliases: Map[(String, TypeAliasSignature), PsiNamedElement],
                          relations: Seq[Relation.Conformance]) extends ConformanceCondition {
    override def satisfy: Boolean = relations.forall(_.satisfy) &&
      left.signatureMap.forall(signatures.get(_).nonEmpty) &&
      left.typesMap.forall(aliases.get(_).nonEmpty)
  }

  case class ExistentialRight(left: ScType, right: ScExistentialType, conformance: Relation.Conformance) extends ConformanceCondition {
    override def satisfy: Boolean = conformance.satisfy
  }

  case class ExistentialLeft(left: ScExistentialType, right: ScType, conformance: Relation.Conformance,
                             restrictions: Seq[Seq[Substitutor#Restriction]]) extends ConformanceCondition {
    override def satisfy: Boolean = restrictions.isEmpty || restrictions.exists(_.forall(_.`type`.nonEmpty))
  }

}

sealed trait Relation {
  def satisfy: Boolean
}

object Relation {
  case class Equivalence(left: ScType, right: ScType, satisfy: Boolean, restriction: Boolean = false) extends Relation

  case class Conformance(left: ScType, right: ScType, conditions: Seq[ConformanceCondition]) extends Relation {
    def satisfy: Boolean = conditions.exists(_.satisfy)
  }
}

sealed trait AsSpecificAsCondition {
  def satisfy: Boolean
}

object AsSpecificAsCondition {
  case class Method(left: ScType, right: ScType, args: DCHandler.Args, restrictions: Seq[Seq[Substitutor#Restriction]]) extends AsSpecificAsCondition {
    override def satisfy: Boolean = args.forall(_.satisfy)
  }
  case class Polymorphic(satisfy: Boolean) extends AsSpecificAsCondition
  case class Other(satisfy: Boolean) extends AsSpecificAsCondition
  case class Conforms(left: ScType, right: ScType, conditions: Seq[ConformanceCondition]) extends AsSpecificAsCondition {
    override def satisfy: Boolean = conditions.exists(_.satisfy)
  }
  case class Explanation(text: String, satisfy: Boolean) extends AsSpecificAsCondition
}
