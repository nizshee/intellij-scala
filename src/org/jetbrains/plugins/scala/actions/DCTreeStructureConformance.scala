package org.jetbrains.plugins.scala.actions

import java.util

import com.intellij.ide.projectView.{PresentationData, ViewSettings}
import com.intellij.ide.projectView.impl.nodes.AbstractPsiBasedNode
import com.intellij.ide.util.treeView.{AbstractTreeNode, AbstractTreeStructure, NodeDescriptor}
import com.intellij.openapi.editor.colors.CodeInsightColors
import com.intellij.openapi.project.Project
import com.intellij.psi.{PsiElement, PsiNamedElement}
import org.jetbrains.plugins.scala.actions.ConformanceCondition._



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
    case n: ConditionNode =>
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
  case class ConditionValue(v: ConformanceCondition, prefix: String = "")
  case class ElementValue(name: String, namedElement: Option[PsiNamedElement])

  class RelationNode(relation: RelationValue)(implicit project: Project) extends AbstractTreeNode[RelationValue](project, relation) {

    override def getChildren: util.Collection[_ <: AbstractTreeNode[_]] = {
      val list = new util.ArrayList[AbstractTreeNode[_]]()
      relation.v match {
        case r: Relation.Conformance =>
          DebugConformanceAdapter(r).conditions.foreach { condition =>
            list.add(new ConditionNode(ConditionValue(condition)))
          }
        case _ =>

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

  class ConditionNode(condition: ConditionValue)(implicit project: Project) extends AbstractTreeNode[ConditionValue](project, condition) {
    override def getChildren: util.Collection[_ <: AbstractTreeNode[_]] = {
      val list = new util.ArrayList[AbstractTreeNode[_]]()
      condition.v match {
        case c: ConformanceCondition.Equivalent =>
          list.add(new RelationNode(RelationValue(c.equivalence)))
        case c: ConformanceCondition.Parametrize =>
          c.equals.foreach(c => list.add(new RelationNode(RelationValue(c))))
          c.conform.foreach {
            case ConformanceCondition.Invariant(param, e, restriction) =>
              list.add(new RelationNode(RelationValue(e, s"invariant $param" + (if (restriction) "[restriction]" else ""))))
            case ConformanceCondition.Covariant(param, e) =>
              list.add(new RelationNode(RelationValue(e, s"covariant $param")))
            case ConformanceCondition.Contrvariant(param, e) =>
              list.add(new RelationNode(RelationValue(e, s"contrvariant $param")))
          }
        case c: ConformanceCondition.Transitive =>
          list.add(new RelationNode(RelationValue(c.lm)))
          list.add(new RelationNode(RelationValue(c.mr)))
        case c: ConformanceCondition.Projection =>
          list.add(new RelationNode(RelationValue(c.conforms)))
        case c: ConformanceCondition.Method =>
          c.ret.foreach(c => list.add(new RelationNode(RelationValue(c, "ret"))))
          c.args.foreach(c => list.add(new RelationNode(RelationValue(c.relation, "arg"))))
        case c: ConformanceCondition.CompoundRight =>
          c.relations.foreach(c => list.add(new RelationNode(RelationValue(c))))
        case c: ConformanceCondition.CompoundLeft =>
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
        case c: ConformanceCondition.ExistentialRight =>
          list.add(new RelationNode(RelationValue(c.conformance)))
        case _ =>
      }
      list
    }

    override def update(presentationData: PresentationData): Unit = {
      val data = condition.v match {
        case c: ConformanceCondition.Equivalent =>
          s"${c.equivalence.right} conforms to ${c.equivalence.left} if they are equivalent"
        case c: ConformanceCondition.BaseClass =>
          s"${c.right} is subclass of ${c.left}"
        case c: ConformanceCondition.FromNothing =>
          s"Nothing is always confroms to ${c.left}"
        case c: ConformanceCondition.ToAny =>
          s"${c.right} is always confroms to Any"
        case c: ConformanceCondition.Parametrize =>
          s"conformance for parametrized types" + (if (!c.sameLength) " [different arguments count]" else "")
        case c: ConformanceCondition.Transitive =>
          s"transitive ${c.right} <: ${c.middle} <: ${c.left}"
        case c: ConformanceCondition.Projection =>
          s"conforms as projections if ${c.conforms.right} <: ${c.conforms.left}"
        case c: ConformanceCondition.Method =>
          s"same arguments and return types conform" + (if (!c.sameLen) " [different arguments count]" else "")
        case c: ConformanceCondition.TypeUpper =>
          s"${c.upper} is upper bound for ${c.`type`}"
        case c: ConformanceCondition.TypeLower =>
          s"${c.lower} is lower bound for ${c.`type`}"
        case c: ConformanceCondition.AbstractLeft =>
          s"abstract ${c.left.lower} <: ${c.left} <: ${c.left.upper} satisfies ${c.right}"
        case c: ConformanceCondition.FromNull =>
          s"${c.left} is conforms to AnyRef"
        case c: ConformanceCondition.Undefined =>
          s"${c.right} <: ${c.left} [restriction]"
        case c: ConformanceCondition.CompoundRight =>
          s"if conforms at least one"
        case c: ConformanceCondition.CompoundLeft =>
          s"if conforms all"
        case c: ConformanceCondition.ExistentialRight =>
          s"if skolemization conforms"
        case c: ConformanceCondition.Todo =>
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
    private val conformance: String = "\n" +
      """<a href="url">https://www.scala-lang.org/files/archive/spec/2.11/03-types.html#conformance</a>"""

    private def getTip(condition: ConformanceCondition): String = condition match {
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
      case _: Undefined =>
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
      case _: AbstractLeft =>
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
