package org.jetbrains.plugins.scala.actions

import java.util

import com.intellij.ide.projectView.PresentationData
import com.intellij.ide.util.treeView.{AbstractTreeNode, AbstractTreeStructure, NodeDescriptor}
import com.intellij.openapi.project.Project


case class Value(relation: Relation, prefix: String = "")

case class RelationValue(v: Relation, prefix: String = "")
case class ConditionValue(v: ConformanceCondition, prefix: String = "")

class DebugConformanceTreeStructure(project: Project, values: Seq[Value]) extends AbstractTreeStructure {

  private class RelationNode(relation: RelationValue) extends AbstractTreeNode[RelationValue](project, relation) {

    override def getChildren: util.Collection[_ <: AbstractTreeNode[_]] = {
      val list = new util.ArrayList[AbstractTreeNode[_]]()
      relation.v match {
        case r: Relation.Conformance =>
          r.conditions.foreach { condition =>
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
            s"${r.left} =: ${r.right} (${r.satisfy})")
        case r: Relation.Conformance =>
          presentationData.setPresentableText((if (relation.prefix.nonEmpty) relation.prefix + ": " else "") +
            s"${r.left} >: ${r.right} (${r.satisfy})")
      }
    }

  }

  private class ConditionNode(condition: ConditionValue) extends AbstractTreeNode[ConditionValue](project, condition) {
    override def getChildren: util.Collection[_ <: AbstractTreeNode[_]] = {
      val list = new util.ArrayList[AbstractTreeNode[_]]()
      condition.v match {
        case c: ConformanceCondition.Equivalent =>
          list.add(new RelationNode(RelationValue(c.equivalence)))
        case c: ConformanceCondition.Parametrize =>
          c.equals.foreach(c => list.add(new RelationNode(RelationValue(c))))
          c.conform.foreach {
            case ConformanceCondition.Invariant(param, e) =>
              list.add(new RelationNode(RelationValue(e, s"invariant $param")))
            case ConformanceCondition.Covariant(param, e) =>
              list.add(new RelationNode(RelationValue(e, s"covariant $param")))
            case ConformanceCondition.Contrvariant(param, e) =>
              list.add(new RelationNode(RelationValue(e, s"contrvariant $param")))
          }
        case c: ConformanceCondition.Transitive =>
          list.add(new RelationNode(RelationValue(c.lm)))
          list.add(new RelationNode(RelationValue(c.mr)))
        case c: ConformanceCondition.Same =>
          list.add(new RelationNode(RelationValue(c.relation)))
        case c: ConformanceCondition.Projection =>
          list.add(new RelationNode(RelationValue(c.conforms)))
        case c: ConformanceCondition.Method =>
          c.ret.foreach(c => list.add(new RelationNode(RelationValue(c, "ret"))))
          c.args.foreach(c => list.add(new RelationNode(RelationValue(c.relation, "arg"))))
        case _ =>
      }
      list
    }

    override def update(presentationData: PresentationData): Unit = {
      val data = condition.v match {
        case c: ConformanceCondition.Equivalent =>
          s"${c.equivalence.right} conformance to ${c.equivalence.left} if they are equivalent"
        case c: ConformanceCondition.BaseClass =>
          s"${c.right} is subclass of ${c.left}"
        case c: ConformanceCondition.FromNothing =>
          s"Nothing is always confroms to ${c.left}"
        case c: ConformanceCondition.ToAny =>
          s"${c.right} is always confroms to Any"
        case c: ConformanceCondition.Parametrize =>
          s"conformance for parametrized types" + (if (!c.sameLength) " [different length]" else "")
        case c: ConformanceCondition.Transitive =>
          s"transitive ${c.left} >: ${c.middle} >: ${c.right}"
        case c: ConformanceCondition.Projection =>
          s"conforms as projections if ${c.conforms.left} >: ${c.conforms.right}"
        case c: ConformanceCondition.Method =>
          s"same arguments and return types conform" + (if (!c.sameLen) " [different length]" else "")
        case c: ConformanceCondition.TypeUpper =>
          s"${c.upper} is upper bound for ${c.`type`}"
        case c: ConformanceCondition.TypeLower =>
          s"${c.lower} is lower bound for ${c.`type`}"
        case c: ConformanceCondition.PolymorphicArgument =>
          s"abstract ${c.left} >: ${c.left.upper} <: ${c.left.lower} satisfies ${c.right}"
        case c: ConformanceCondition.FromNull =>
          s"${c.left} is ${if (c.anyRef) "" else "not "}conforms to AnyRef"
        case _ =>
      }
      val msg = condition.v.msg
      presentationData.setPresentableText(s"$data (${condition.v.satisfy})" + (if (msg.nonEmpty) "//" else "") + msg)

    }
  }

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
