package org.jetbrains.plugins.scala.actions

import java.util

import com.intellij.ide.projectView.PresentationData
import com.intellij.ide.util.treeView.AbstractTreeNode
import com.intellij.openapi.editor.colors.CodeInsightColors
import com.intellij.openapi.project.Project
import org.jetbrains.plugins.scala.actions
import org.jetbrains.plugins.scala.actions.AsSpecificAsCondition._
import org.jetbrains.plugins.scala.actions.DCTreeStructureConformance.{RelationNode, RelationValue}
import org.jetbrains.plugins.scala.actions.DCTreeStructureSubstitutor.{SubstitutorNode, SubstitutorValue}


object DCTreeStructureCompatibility {
  case class CompatibilityValue(arguments: Seq[DCHandler.Compatibility#Arg], ret: Option[DCHandler.Resolver#Ret])
  case class MostSpecificValue(asSpecificAsCondition: AsSpecificAsCondition)

  class CompatibilityNode(value: CompatibilityValue)(implicit project: Project) extends AbstractTreeNode[CompatibilityValue](project, value) {
    private val args = value.arguments.map(a =>
      new DCTreeStructureConformance.RelationNode(
        DCTreeStructureConformance.RelationValue(
          Relation.Conformance(a.expectedType, a.actualType, a.conditions),
          a.name
        )
      )
    )

    private val ret = value.ret.map(r =>
      new DCTreeStructureConformance.RelationNode(
        DCTreeStructureConformance.RelationValue(
          Relation.Conformance(r.expextedType, r.actualType, r.conditions),
          "return"
        )
      )
    )

    override def getChildren: util.Collection[_ <: AbstractTreeNode[_]] = {
      val list = new util.ArrayList[AbstractTreeNode[_]]()
      args.foreach(list.add)
      ret.foreach(list.add)
      list
    }

    override def update(presentationData: PresentationData): Unit = {
      presentationData.setPresentableText("application")
      if (!value.arguments.forall(_.satisfy) || value.ret.exists(_.conditions.forall(!_.satisfy)))
        presentationData.setAttributesKey(CodeInsightColors.WRONG_REFERENCES_ATTRIBUTES)
    }
  }

  class MostSpecificNode(value: MostSpecificValue)(implicit project: Project) extends AbstractTreeNode[MostSpecificValue](project, value) {
    override def getChildren: util.Collection[_ <: AbstractTreeNode[_]] = {
      val list = new util.ArrayList[AbstractTreeNode[_]]()
      value.asSpecificAsCondition match {
        case Method(_, _, args, restrictions) =>
          list.add(new CompatibilityNode(CompatibilityValue(args, None)))
          list.add(new SubstitutorNode(SubstitutorValue(restrictions)))
        case Conforms(left, right, conditions) =>
          list.add(new RelationNode(RelationValue(Relation.Conformance(left, right, conditions))))
        case _ =>
      }
      list
    }

    override def update(presentationData: PresentationData): Unit = {
      val text = value.asSpecificAsCondition match {
        case Method(left, right, _, _) =>
          s"method $left as specific as $right"
        case Polymorphic(_) =>
          "todo"
        case Other(_) =>
          s"not polymorphic or method always as specific as polymorphic or method"
        case Explanation(txt, _) => txt
        case Conforms(_, _, _) =>
          s"if not method type then conformance"
      }
      presentationData.setPresentableText(text)
      if (!value.asSpecificAsCondition.satisfy)
        presentationData.setAttributesKey(CodeInsightColors.WRONG_REFERENCES_ATTRIBUTES)
    }
  }
}
