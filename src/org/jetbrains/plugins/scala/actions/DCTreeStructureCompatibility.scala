package org.jetbrains.plugins.scala.actions

import java.util

import com.intellij.ide.projectView.PresentationData
import com.intellij.ide.util.treeView.AbstractTreeNode
import com.intellij.openapi.editor.colors.CodeInsightColors
import com.intellij.openapi.project.Project


object DCTreeStructureCompatibility {
  case class CompatibilityValue(arguments: Seq[DCHandler.Compatibility#Arg])

  class CompatibilityNode(project: Project, value: CompatibilityValue) extends AbstractTreeNode[CompatibilityValue](project, value) {
    private val args = value.arguments.map(a =>
      new DCTreeStructureConformance.RelationNode(
        project,
        DCTreeStructureConformance.RelationValue(
          Relation.Conformance(
            a.expectedType,
            a.expectedType,
            a.conditions
          )
        )
      )
    )

    override def getChildren: util.Collection[_ <: AbstractTreeNode[_]] = {
      val list = new util.ArrayList[AbstractTreeNode[_]]()
      args.foreach(list.add)
      list
    }

    override def update(presentationData: PresentationData): Unit = {
      presentationData.setPresentableText("application")
      if (!value.arguments.exists(_.satisfy))
        presentationData.setAttributesKey(CodeInsightColors.WRONG_REFERENCES_ATTRIBUTES)
    }
  }
}
