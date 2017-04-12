package org.jetbrains.plugins.scala.actions

import java.util

import com.intellij.ide.projectView.PresentationData
import com.intellij.ide.util.treeView.AbstractTreeNode
import com.intellij.openapi.editor.colors.CodeInsightColors
import com.intellij.openapi.project.Project
import org.jetbrains.plugins.scala.actions.DCTreeStructureSubstitutor.{SubstitutorNode, SubstitutorValue}
import org.jetbrains.plugins.scala.lang.psi.types.{ScUndefinedSubstitutor, ScalaTypeSystem}


object DCTreeStructureCompatibility {
  case class CompatibilityValue(arguments: Seq[DCHandler.Compatibility#Arg])

  class CompatibilityNode(value: CompatibilityValue)(implicit project: Project) extends AbstractTreeNode[CompatibilityValue](project, value) {
    private val args = value.arguments.map(a =>
      new DCTreeStructureConformance.RelationNode(
        DCTreeStructureConformance.RelationValue(
          Relation.Conformance(a.expectedType, a.actualType, a.conditions),
          a.name
        )
      )
    )

    private val subst = {
      val undefinedSubst = value.arguments.foldLeft(ScUndefinedSubstitutor()(ScalaTypeSystem))(_ + _.undefinedSubstitutor) // TODO? actual system
      val handler = new DCHandler.Substitutor("", false) // TODO? mv somwhere near other handlers
      undefinedSubst.getSubstitutorWithBounds(notNonable = true, handler = Some(handler))
      Some(handler.restictions).filter(_.nonEmpty).map(rs => new SubstitutorNode(SubstitutorValue(rs)))
    }

    override def getChildren: util.Collection[_ <: AbstractTreeNode[_]] = {
      val list = new util.ArrayList[AbstractTreeNode[_]]()
      args.foreach(list.add)
      subst.foreach(list.add)
      list
    }

    override def update(presentationData: PresentationData): Unit = {
      presentationData.setPresentableText("application")
      if (!value.arguments.exists(_.satisfy))
        presentationData.setAttributesKey(CodeInsightColors.WRONG_REFERENCES_ATTRIBUTES)
    }
  }
}
