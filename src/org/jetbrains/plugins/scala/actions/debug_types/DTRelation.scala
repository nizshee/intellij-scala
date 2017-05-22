package org.jetbrains.plugins.scala.actions.debug_types

import com.intellij.psi.PsiNamedElement
import org.jetbrains.plugins.scala.actions.debug_types.DTHandler.Substitutor
import org.jetbrains.plugins.scala.lang.psi.types.api.{Any, Nothing, ParameterizedType, TypeSystem}
import org.jetbrains.plugins.scala.lang.psi.types.nonvalue.ScMethodType
import org.jetbrains.plugins.scala.lang.psi.types.{ScAbstractType, ScCompoundType, ScExistentialType, ScType, ScalaTypeSystem, Signature, TypeAliasSignature}


case class RelationContext(restrictions: Seq[DTHandler.Substitutor#Restriction], ignoreRestrictions: Boolean = false)

sealed trait CCondition {
  def satisfy(ctx: RelationContext): Boolean
  var _msg: String = ""
  def +(msg: String): Unit = _msg = msg
  def msg: String = _msg
}

object CCondition {


  trait Variance {
    def satisfy(ctx: RelationContext): Boolean
  }

  case class Invariant(param: String, relation: Relation.Equivalence) extends Variance {
    override def satisfy(ctx: RelationContext): Boolean = relation.satisfy(ctx)
  }

  case class Covariant(param: String, relation: Relation.Conformance) extends Variance {
    override def satisfy(ctx: RelationContext): Boolean = relation.satisfy(ctx)
  }

  case class Contrvariant(param: String, relation: Relation.Conformance) extends Variance {
    override def satisfy(ctx: RelationContext): Boolean = relation.satisfy(ctx)
  }


  case class Projection(conforms: Relation.Conformance) extends CCondition {
    override def satisfy(ctx: RelationContext): Boolean = conforms.satisfy(ctx)
  }

  case class UndefinedLeft(left: ScAbstractType, right: ScType, uConditions: Seq[CCondition],
                           lConfitions: Seq[CCondition]) extends CCondition {
    override def satisfy(ctx: RelationContext): Boolean = uConditions.exists(_.satisfy(ctx))
  }

  case class UndefinedRight(left: ScType, right: ScAbstractType, uConditions: Seq[CCondition],
                            lConfitions: Seq[CCondition]) extends CCondition {
    override def satisfy(ctx: RelationContext): Boolean = lConfitions.exists(_.satisfy(ctx))
  }

  case class Transitive(left: ScType, middle: ScType, right: ScType, lm: Relation.Conformance, mr: Relation.Conformance) extends CCondition {
    override def satisfy(ctx: RelationContext): Boolean = lm.satisfy(ctx) && mr.satisfy(ctx)
  }

  case class TypeUpper(upper: ScType, `type`: ScType, satisfy: Boolean) extends CCondition {
    override def satisfy(ctx: RelationContext): Boolean = satisfy
  }

  case class TypeLower(`type`: ScType, lower: ScType, satisfy: Boolean) extends CCondition {
    override def satisfy(ctx: RelationContext): Boolean = satisfy
  }

  case class Equivalent(equivalence: Relation.Equivalence) extends CCondition {
    override def satisfy(ctx: RelationContext): Boolean = equivalence.satisfy(ctx)
  }

  case class Parametrize(left: ParameterizedType, right: ParameterizedType, equals: Option[Relation.Equivalence], sameLength: Boolean,conform: Seq[Variance]) extends CCondition {
    override def satisfy(ctx: RelationContext): Boolean = left.typeArguments.size == right.typeArguments.size && right.typeArguments.size == conform.size &&
      equals.exists(_.satisfy(ctx)) && conform.forall(_.satisfy(ctx))
  }

  case class ToAny(right: ScType) extends CCondition {
    override def satisfy(ctx: RelationContext): Boolean = true
  }

  case class FromNothing(left: ScType) extends CCondition {
    override def satisfy(ctx: RelationContext): Boolean = true
  }

  case class FromNull(left: ScType, anyRef: Boolean, notNull: Boolean) extends CCondition {
    override def satisfy(ctx: RelationContext): Boolean = anyRef && !notNull
  }

  case class BaseType(left: ScType, right: ScType, satisfy: Boolean) extends CCondition {
    override def satisfy(ctx: RelationContext): Boolean = satisfy
  }

  case class Todo(reason: String, satisfy: Boolean) extends CCondition {
    override def satisfy(ctx: RelationContext): Boolean = satisfy
  }

  case class Method(left: ScMethodType, right: ScMethodType, sameLen: Boolean, ret: Option[Relation.Conformance],
                    args: Seq[Invariant]) extends CCondition {
    override def satisfy(ctx: RelationContext): Boolean = sameLen && ret.exists(_.satisfy(ctx)) && args.forall(_.satisfy(ctx))
  }

  case class Polymorphic(il: ScType, ir: ScType, sameLength: Boolean,
                         args: Seq[(Relation.Conformance, Relation.Conformance)], i: Option[Relation.Conformance]) extends CCondition {
    override def satisfy(ctx: RelationContext): Boolean = sameLength && args.forall(p => p._1.satisfy(ctx) && p._2.satisfy(ctx)) &&
      i.exists(_.satisfy(ctx))
  }

  case class RestrictionLeft(name: (String, Long), right: ScType) extends CCondition {
    override def satisfy(ctx: RelationContext): Boolean = ctx.ignoreRestrictions ||
      ctx.restrictions.find(_.name == name).exists(_.upperFor(right))

  }

  case class RestrictionRight(name: (String, Long), left: ScType) extends CCondition {
    override def satisfy(ctx: RelationContext): Boolean = ctx.ignoreRestrictions ||
      ctx.restrictions.find(_.name == name).exists(_.lowerFor(left))
  }

  case class CompoundRight(left: ScType, right: ScCompoundType, relations: Seq[Relation.Conformance]) extends CCondition {
    override def satisfy(ctx: RelationContext): Boolean = relations.exists(_.satisfy(ctx))
  }

  case class CompoundLeft(left: ScCompoundType, right: ScType,
                          signatures: Map[(Signature, ScType), PsiNamedElement],
                          aliases: Map[(String, TypeAliasSignature), PsiNamedElement],
                          relations: Seq[Relation.Conformance]) extends CCondition {
    override def satisfy(ctx: RelationContext): Boolean = relations.forall(_.satisfy(ctx)) &&
      left.signatureMap.forall(signatures.get(_).nonEmpty) &&
      left.typesMap.forall(aliases.get(_).nonEmpty)
  }

  case class ExistentialRight(left: ScType, right: ScExistentialType, conformance: Relation.Conformance) extends CCondition {
    override def satisfy(ctx: RelationContext): Boolean = conformance.satisfy(ctx)
  }

  case class ExistentialLeft(left: ScExistentialType, right: ScType, conformance: Relation.Conformance,
                             restrictions: Seq[Seq[Substitutor#Restriction]]) extends CCondition {
    override def satisfy(ctx: RelationContext): Boolean = restrictions.isEmpty || restrictions.exists(_.forall(_.satisfy))
  }
}

sealed trait ECondition {
  def satisfy(ctx: RelationContext): Boolean
}

object ECondition {
  case class Simple(satisfy: Boolean) extends ECondition {
    override def satisfy(ctx: RelationContext): Boolean = satisfy
  }

  case class Special(left: Option[Relation.Conformance], right: Option[Relation.Conformance]) extends ECondition {
    override def satisfy(ctx: RelationContext): Boolean = left.forall(_.satisfy(ctx)) && right.forall(_.satisfy(ctx))
  }
}

sealed trait Relation {
  def satisfy(ctx: RelationContext): Boolean
}

object Relation {
  case class Equivalence(left: ScType, right: ScType, condition: ECondition) extends Relation {
    override def satisfy(ctx: RelationContext): Boolean = condition.satisfy(ctx)
  }

  case class Conformance(left: ScType, right: ScType, conditions: Seq[CCondition]) extends Relation {
    def satisfy(ctx: RelationContext): Boolean = conditions.exists(_.satisfy(ctx))
  }
}

sealed trait AsSpecificAsCondition {
  def satisfy: Boolean
}

object AsSpecificAsCondition {
  case class Method(left: ScType, right: ScType, args: DTHandler.Args, restrictions: Seq[Seq[Substitutor#Restriction]]) extends AsSpecificAsCondition {
    override def satisfy: Boolean = {
      val r = restrictions.find(_.forall(_.satisfy)).getOrElse(Seq())
      args.forall(_.satisfy(RelationContext(r)))
    }
  }

  case class Polymorphic(satisfy: Boolean) extends AsSpecificAsCondition

  case class Other(satisfy: Boolean) extends AsSpecificAsCondition

  case class Conforms(left: ScType, right: ScType, conditions: Seq[CCondition]) extends AsSpecificAsCondition {
    override def satisfy: Boolean = conditions.exists(_.satisfy(RelationContext(Seq(), ignoreRestrictions = true)))
  }

  case class Explanation(text: String, satisfy: Boolean) extends AsSpecificAsCondition
}

case object Derived
