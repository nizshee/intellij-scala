package org.jetbrains.plugins.scala.actions

import java.util

import com.intellij.ide.projectView.{PresentationData, ViewSettings}
import com.intellij.ide.projectView.impl.nodes.AbstractPsiBasedNode
import com.intellij.ide.util.treeView.{AbstractTreeNode, AbstractTreeStructure, NodeDescriptor}
import com.intellij.openapi.editor.colors.CodeInsightColors
import com.intellij.openapi.project.Project
import com.intellij.psi.{PsiElement, PsiNamedElement}
import org.jetbrains.plugins.scala.actions.CCondition._
import org.jetbrains.plugins.scala.actions.ECondition.{Simple, Special}



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
          DebugConformanceAdapter(r).conditions.foreach { condition =>
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
          list.add(new RelationNode(RelationValue(left)))
          list.add(new RelationNode(RelationValue(right)))
      }
      list
    }

    override def update(presentationData: PresentationData): Unit = {
      val text = value.condition match {
        case Simple(_, restriction) if restriction => "equivalent [restriction]"
        case Simple(_, _) => "equivalent"
        case Special(_, _) => "if both"
      }
      presentationData.setPresentableText(text)
      if (!value.condition.satisfy)
        presentationData.setAttributesKey(CodeInsightColors.WRONG_REFERENCES_ATTRIBUTES)
    }

    private def getTip(condition: ECondition) = condition match {
      case _: Simple => ""
      case _: Special => "special case for undefined types"
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
        case c: BaseClass =>
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
        case c: CCondition.BaseClass =>
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
        case c: CCondition.Method =>
          s"same arguments and return types conform" + (if (!c.sameLen) " [different arguments count]" else "")
        case c: CCondition.TypeUpper =>
          s"${c.upper} is upper bound for ${c.`type`}"
        case c: CCondition.TypeLower =>
          s"${c.lower} is lower bound for ${c.`type`}"
        case c: CCondition.UndefinedLeft =>
          s"${c.right} should conform to upper bound of undefined ${c.left}"
        case c: CCondition.UndefinedRight =>
          s"lower bound of undefined ${c.right} should conform to ${c.left}"
        case c: CCondition.FromNull =>
          s"${c.left} is conforms to AnyRef"
        case c: CCondition.RestrictionLeft =>
          s"restriction ${c.right} <: ${c.name._1}"
        case c: CCondition.RestrictionRight =>
          s"restriction ${c.name._1} <: ${c.left}"
        case c: CCondition.CompoundRight =>
          s"if conforms at least one"
        case c: CCondition.CompoundLeft =>
          s"if conforms all"
        case c: CCondition.ExistentialRight =>
          s"if skolemization conforms"
        case c: CCondition.Todo =>
          s"todo: ${c.reason}"
        case c: CCondition.ExistentialLeft => ???
        case c: CCondition.Polymorphic => ???
      }
      val msg = condition.v.msg
      presentationData.setTooltip(getTip(condition.v))
      presentationData.setPresentableText(s"$data" + (if (msg.nonEmpty) "//" else "") + msg)
      if (!condition.v.satisfy)
        presentationData.setAttributesKey(CodeInsightColors.WRONG_REFERENCES_ATTRIBUTES)
    }

    private val conforms: String = "<plaintext><:</plaintext>"
    private val equiv: String = "<plaintext>=:</plaintext>"
    private val conformance: String = "\n" +
      """<a href="url">https://www.scala-lang.org/files/archive/spec/2.11/03-types.html#conformance</a>"""

    private def getTip(condition: CCondition): String = condition match {
      case _: Projection =>
        """A type projection T#t conforms to U#t if T conforms to U.""" + conformance
      case _: Transitive =>
        s"""The conformance relation ($conforms) is the smallest transitive relation that satisfies the conditions.""" +
          conformance
      case _: TypeUpper =>
        """A type variable or abstract type t conforms to its upper bound and its lower bound conforms to t.""" + conformance
      case _: TypeLower =>
        """A type variable or abstract type t conforms to its upper bound and its lower bound conforms to t.""" + conformance
      case _: Equivalent =>
        s"""Conformance includes equivalence. If T $equiv U then T $conforms U.""" + conformance
      case _: ToAny =>
        s"""For every value type T, scala.Nothing $conforms T $conforms scala.Any.""" + conformance
      case _: FromNothing =>
        s"""For every value type T, scala.Nothing $conforms T $conforms scala.Any.""" + conformance
      case _: FromNull =>
        """"""
      case _: BaseClass =>
        """"""
      case _: Method =>
        """"""
      case _: RestrictionLeft =>
        """"""
      case _: CompoundRight =>
        """"""
      case _: CompoundLeft =>
        """"""
      case _: ExistentialRight =>
        """"""
      case _: Parametrize =>
        s"""A parameterized type T[T1 , … , Tn] conforms to T[U1 , … , Un] if the following three conditions hold for all i:
          |
          |1. If the i'th type parameter of T is declared covariant, then Ti $conforms Ui.
          |2. If the i'th type parameter of T is declared contravariant, then Ui $conforms Ti.
          |3. If the i'th type parameter of T is declared neither covariant nor contravariant, then Ui $equiv Ti.""".stripMargin + conformance
      case _: Todo =>
        """Not implemented yet."""
      case _: UndefinedLeft =>
        """"""
      case _: ExistentialLeft =>
        """"""
      case _: Polymorphic =>
        """"""
      case _: UndefinedRight =>
        """"""

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
