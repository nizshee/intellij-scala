package org.jetbrains.plugins.scala.actions.debug_types

import java.util

import com.intellij.ide.projectView.impl.nodes.AbstractPsiBasedNode
import com.intellij.ide.projectView.{PresentationData, ViewSettings}
import com.intellij.ide.util.treeView.{AbstractTreeNode, AbstractTreeStructure, NodeDescriptor}
import com.intellij.openapi.editor.colors.CodeInsightColors
import com.intellij.openapi.project.Project
import com.intellij.psi.{PsiElement, PsiNamedElement}
import CCondition._
import ECondition.{Simple, Special}
import org.jetbrains.plugins.scala.actions._



class DCTreeStructureConformance(values: Seq[DCTreeStructureConformance.Value])(implicit project: Project) extends AbstractTreeStructure {

  import DCTreeStructureConformance._

  private class RootNode extends AbstractTreeNode[Any](project, ()) {
    override def getChildren: util.Collection[_ <: AbstractTreeNode[_]] = {
      val list = new util.ArrayList[AbstractTreeNode[_]]()
      values.foreach { value => list.add(new RelationNode(RelationValue(value.relation))) }
      list
    }

    override def update(presentation: PresentationData): Unit = {}
  }

  override def getParentElement(o: scala.Any): AnyRef = null

  override def getRootElement: AnyRef = new RootNode

  override def getChildElements(o: scala.Any): Array[AnyRef] = o match {
    case _: RootNode => values.map(v => new RelationNode(RelationValue(v.relation))).toArray
    case n: RelationNode =>
      val childrenImpl = n.getChildren
      childrenImpl.toArray(new Array[AnyRef](childrenImpl.size))
    case n: CConditionNode =>
      val childrenImpl = n.getChildren
      childrenImpl.toArray(new Array[AnyRef](childrenImpl.size))
    case _ => Array.empty
  }

  override def createDescriptor(o: scala.Any, nodeDescriptor: NodeDescriptor[_]): NodeDescriptor[_] = o.asInstanceOf[NodeDescriptor[_]]

  override def hasSomethingToCommit: Boolean = false

  override def commit(): Unit = {}
}


object DCTreeStructureConformance {
  case class Value(relation: Relation, prefix: String = "")

  case class RelationValue(v: Relation, prefix: String = "")
  case class CConditionValue(v: CCondition, prefix: String = "")
  case class ElementValue(name: String, namedElement: Option[PsiNamedElement])

  class RelationNode(relation: RelationValue)(implicit project: Project) extends AbstractTreeNode[RelationValue](project, relation) {

    override def getChildren: util.Collection[_ <: AbstractTreeNode[_]] = {
      val list = new util.ArrayList[AbstractTreeNode[_]]()
      relation.v match {
        case r: Relation.Conformance =>
          DTAdapter(r).conditions.foreach { condition =>
            list.add(new CConditionNode(CConditionValue(condition)))
          }
        case r: Relation.Equivalence =>
          list.add(new EConditionNode(EConditionValue(r.condition)))
      }
      list
    }

    override def update(presentationData: PresentationData): Unit = {
      relation.v match {
        case r: Relation.Equivalence =>
          presentationData.setPresentableText((if (relation.prefix.nonEmpty) relation.prefix + ": " else "") +
            s"${r.right} =: ${r.left}")
        case r: Relation.Conformance =>
          presentationData.setPresentableText((if (relation.prefix.nonEmpty) relation.prefix + ": " else "") +
            s"${r.right} <: ${r.left}")
      }
      if (!relation.v.satisfy)
        presentationData.setAttributesKey(CodeInsightColors.WRONG_REFERENCES_ATTRIBUTES)
    }
  }

  case class EConditionValue(condition: ECondition)
  class EConditionNode(value: EConditionValue)(implicit project: Project) extends AbstractTreeNode[EConditionValue](project, value) {
    override def getChildren: util.Collection[_ <: AbstractTreeNode[_]] = {
      val list = new util.ArrayList[AbstractTreeNode[_]]()
      value.condition match {
        case _: Simple =>
        case Special(left, right) =>
          left.foreach(c => list.add(new RelationNode(RelationValue(c))))
          right.foreach(c => list.add(new RelationNode(RelationValue(c))))
      }
      list
    }

    override def update(presentationData: PresentationData): Unit = {
      val text = value.condition match {
        case Simple(_) => "equivalent"
        case Special(_, _) => "special case of equivalence"
      }
      presentationData.setPresentableText(text)
      presentationData.setTooltip(getTip(value.condition))
      if (!value.condition.satisfy)
        presentationData.setAttributesKey(CodeInsightColors.WRONG_REFERENCES_ATTRIBUTES)
    }

    private def getTip(condition: ECondition) = condition match {
      case _: Simple => ""
      case _: Special => "plugin: Special case of equivalence for undefined types."
    }
  }

  class CConditionNode(condition: CConditionValue)(implicit project: Project) extends AbstractTreeNode[CConditionValue](project, condition) {
    override def getChildren: util.Collection[_ <: AbstractTreeNode[_]] = {
      val list = new util.ArrayList[AbstractTreeNode[_]]()
      condition.v match {
        case c: CCondition.Equivalent =>
          list.add(new RelationNode(RelationValue(c.equivalence)))
        case c: CCondition.Parametrize =>
          c.equals.foreach(c => list.add(new RelationNode(RelationValue(c))))
          c.conform.foreach {
            case CCondition.Invariant(param, e) =>
              list.add(new RelationNode(RelationValue(e, s"invariant $param")))
            case CCondition.Covariant(param, e) =>
              list.add(new RelationNode(RelationValue(e, s"covariant $param")))
            case CCondition.Contrvariant(param, e) =>
              list.add(new RelationNode(RelationValue(e, s"contrvariant $param")))
          }
        case c: CCondition.Transitive =>
          list.add(new RelationNode(RelationValue(c.lm)))
          list.add(new RelationNode(RelationValue(c.mr)))
        case c: CCondition.Projection =>
          list.add(new RelationNode(RelationValue(c.conforms)))
        case c: CCondition.Method =>
          c.ret.foreach(c => list.add(new RelationNode(RelationValue(c, "ret"))))
          c.args.foreach(c => list.add(new RelationNode(RelationValue(c.relation, "arg"))))
        case c: CCondition.CompoundRight =>
          c.relations.foreach(c => list.add(new RelationNode(RelationValue(c))))
        case c: CCondition.CompoundLeft =>
          c.relations.foreach(c => list.add(new RelationNode(RelationValue(c))))
          c.left.signatureMap.foreach { case (sign, ty) =>
            val name = s"exists ${sign.name}: $ty" // TODO? function signatures
            list.add(new ElementNode(ElementValue(name, c.signatures.get(sign -> ty))))
          }
          c.left.typesMap.foreach { case (n, sign) =>
            val params = if (sign.typeParams.nonEmpty) s"[${sign.typeParams.mkString(", ")}]" else ""
            val name = s"exists type ${sign.name}$params <: ${sign.upperBound} >: ${sign.lowerBound}"
            list.add(new ElementNode(ElementValue(name, c.aliases.get(n -> sign))))
          }
        case c: CCondition.ExistentialRight =>
          list.add(new RelationNode(RelationValue(c.conformance)))
        case c: CCondition.UndefinedRight =>
          c.lConfitions.foreach(v => list.add(new CConditionNode(CConditionValue(v))))
        case c: CCondition.UndefinedLeft =>
          c.uConditions.foreach(v => list.add(new CConditionNode(CConditionValue(v))))
        case c: BaseType =>
        case c: ExistentialLeft =>
        case c: FromNothing =>
        case c: FromNull =>
        case c: Polymorphic =>
        case c: RestrictionRight =>
        case c: RestrictionLeft =>
        case c: ToAny =>
        case c: Todo =>
        case c: TypeLower =>
        case c: TypeUpper =>
      }
      list
    }

    override def update(presentationData: PresentationData): Unit = {
      val data = condition.v match {
        case c: CCondition.Equivalent =>
          s"${c.equivalence.right} conforms to ${c.equivalence.left} if they are equivalent"
        case c: CCondition.BaseType =>
          s"${c.right} is subclass of ${c.left}"
        case c: CCondition.FromNothing =>
          s"Nothing is always confroms to ${c.left}"
        case c: CCondition.ToAny =>
          s"${c.right} is always confroms to Any"
        case c: CCondition.Parametrize =>
          s"conformance for parametrized types" + (if (!c.sameLength) " [different arguments count]" else "")
        case c: CCondition.Transitive =>
          s"transitive ${c.right} <: ${c.middle} <: ${c.left}"
        case c: CCondition.Projection =>
          s"conforms as projections if ${c.conforms.right} <: ${c.conforms.left}"
        case c: CCondition.TypeUpper =>
          s"${c.upper} is upper bound for ${c.`type`}"
        case c: CCondition.TypeLower =>
          s"${c.lower} is lower bound for ${c.`type`}"
        case c: CCondition.UndefinedLeft =>
          s"${c.right} should conform to upper bound of undefined ${c.left} <: ${c.upper}"
        case c: CCondition.UndefinedRight =>
          s"lower bound of undefined ${c.lower} <: ${c.right} should conform to ${c.left}"
        case c: CCondition.FromNull =>
          s"${c.left} is conforms to AnyRef"
        case c: CCondition.RestrictionLeft =>
          s"[restriction] ${c.right} <: ${c.name._1}"
        case c: CCondition.RestrictionRight =>
          s"[restriction] ${c.name._1} <: ${c.left}"
        case c: CCondition.CompoundRight =>
          s"if conforms at least one"
        case c: CCondition.CompoundLeft =>
          s"if conforms all"
        case c: CCondition.ExistentialRight =>
          s"if skolemization conforms"
        case c: CCondition.ExistentialLeft =>
          s"if ${c.right} conforms to any type instance"
        case c: CCondition.Method =>
          s"same arguments and return types conform" + (if (!c.sameLen) " [different arguments count]" else "")
        case c: CCondition.Polymorphic =>
          ""
        case c: CCondition.Todo =>
          s"todo: ${c.reason}"
      }
      val msg = condition.v.msg
      presentationData.setTooltip(getTip(condition.v))
      presentationData.setPresentableText(s"$data" + (if (msg.nonEmpty) "//" else "") + msg)
      if (!condition.v.satisfy)
        presentationData.setAttributesKey(CodeInsightColors.WRONG_REFERENCES_ATTRIBUTES)
    }

    private val conforms: String = "<plaintext><:</plaintext>"
    private val equiv: String = "<plaintext>=:</plaintext>"

    private def getTip(condition: CCondition): String = condition match {
      case _: Projection =>
        """A type projection T#t conforms to U#t if T conforms to U."""
      case _: Transitive =>
        s"""The conformance relation ($conforms) is the smallest transitive relation that satisfies the conditions."""
      case _: TypeUpper =>
        """A type variable or abstract type t conforms to its upper bound and its lower bound conforms to t."""
      case _: TypeLower =>
        """A type variable or abstract type t conforms to its upper bound and its lower bound conforms to t."""
      case _: Equivalent =>
        s"""Conformance includes equivalence. If T $equiv U then T $conforms U."""
      case _: ToAny =>
        s"""For every value type T, scala.Nothing $conforms T $conforms scala.Any."""
      case _: FromNothing =>
        s"""For every value type T, scala.Nothing $conforms T $conforms scala.Any."""
      case _: FromNull =>
        """For every class type T such that T <: scala.AnyRef one has scala.Null <: T."""
      case _: BaseType =>
        """A class type or parameterized type conforms to any of its base-types."""
      case _: RestrictionLeft =>
        """plugin: Uses to collect restrictions for some abstract types."""
      case _: RestrictionRight =>
        """plugin: Uses to collect restrictions for some abstract types."""
      case _: CompoundRight =>
        """A compound type T1 with … with Tn {R} conforms to each of its component types Ti."""
      case _: CompoundLeft =>
        s"""If T $conforms Ui for all i and for every binding d of a type or value x in R
           |there exists a member binding of x in T which subsumes d,
           |then T conforms to the compound type U1 with … with Un {R}.""".stripMargin
      case _: ExistentialRight =>
        """The existential type T forSome {Q} conforms to U if its skolemization conforms to U."""
      case _: ExistentialLeft =>
        """The type T conforms to the existential type U forSome {Q} if T conforms to one of the type instances of U forSome {Q}."""
      case _: Parametrize =>
        s"""A parameterized type T[T1 , … , Tn] conforms to T[U1 , … , Un] if the following three conditions hold for all i:
          |
          |1. If the i'th type parameter of T is declared covariant, then Ti $conforms Ui.
          |2. If the i'th type parameter of T is declared contravariant, then Ui $conforms Ti.
          |3. If the i'th type parameter of T is declared neither covariant nor contravariant, then Ui $equiv Ti.""".stripMargin
      case _: UndefinedLeft =>
        s"""undefined $conforms T  and T $conforms undefined
           |
           |plugin: Added information about context of application like upper and lower types.""".stripMargin
      case _: UndefinedRight =>
        s"""undefined $conforms T  and T $conforms undefined
           |
           |plugin: Added information about context of application like upper and lower types.""".stripMargin
      case _: Method =>
        s"""If Ti $equiv Ti′ for all i and U conforms to U′ then the method type (p1:T1,…,pn:Tn)U conforms to (p1′:T1′,…,pn′:Tn′)U′."""
      case _: Polymorphic =>
        s"""The polymorphic type [L1 $conforms a1 $conforms U1,…,Ln $conforms an $conforms Un] conforms
           |to the polymorphic type [L1′ $conforms a1 $conforms U1′,…,Ln′ $conforms an $conforms Un′]T′ if,
           |assuming L1′ $conforms a1 $conforms U1′,…,Ln′ $conforms an $conforms Un′ one has T $conforms T′ and Li $conforms Li′ and Ui′ $conforms Ui for all i.""".stripMargin
      case _: Todo =>
      """Not implemented yet."""

    }
  }

  class ElementNode(value: ElementValue)(implicit project: Project) extends AbstractTreeNode[ElementValue](project, value) {

    override def getChildren: util.Collection[AbstractTreeNode[_]] = {
      val list = new util.ArrayList[AbstractTreeNode[_]]()
      value.namedElement.foreach(a => list.add(new ActualElementNode(a)))
      list
    }

    override def update(presentationData: PresentationData): Unit = {
      presentationData.setPresentableText(value.name)
      if (value.namedElement.isEmpty)
        presentationData.setAttributesKey(CodeInsightColors.WRONG_REFERENCES_ATTRIBUTES)
    }
  }

  class ActualElementNode(namedElement: PsiNamedElement)(implicit project: Project) extends AbstractPsiBasedNode[PsiNamedElement](project, namedElement, ViewSettings.DEFAULT) {
    override def extractPsiFromValue(): PsiElement = namedElement

    override def getChildrenImpl: util.Collection[AbstractTreeNode[_]] = new util.ArrayList[AbstractTreeNode[_]]()

    override def updateImpl(presentationData: PresentationData): Unit = {
      presentationData.setPresentableText(namedElement.toString)
    }
  }


}
