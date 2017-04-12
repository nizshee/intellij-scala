package org.jetbrains.plugins.scala.actions

import java.util

import com.intellij.ide.projectView.PresentationData
import com.intellij.ide.util.treeView.AbstractTreeNode
import com.intellij.openapi.project.Project

/**
  * Created by user on 4/12/17.
  */
object DCTreeStructureSubstitutor {
  case class SubstitutorValue(restrictions: Seq[DCHandler.Substitutor#Restriction])
  case class RestrictionValue(restriction: DCHandler.Substitutor#Restriction)

  class SubstitutorNode(value: SubstitutorValue)(implicit project: Project) extends AbstractTreeNode[SubstitutorValue](project, value) {
    private val restrictions = value.restrictions.map(r => new RestrictionNode(project, RestrictionValue(r)))

    override def getChildren: util.Collection[_ <: AbstractTreeNode[_]] = {
      val list = new util.ArrayList[AbstractTreeNode[_]]()
      restrictions.foreach(list.add)
      list
    }

    override def update(presentationData: PresentationData): Unit = {
      presentationData.setPresentableText("restrictions")
    }
  }

  class RestrictionNode(project: Project, value: RestrictionValue) extends AbstractTreeNode[RestrictionValue](project, value) {
    override def getChildren: util.Collection[_ <: AbstractTreeNode[_]] = {
      val list = new util.ArrayList[AbstractTreeNode[_]]()
      list
    }

    override def update(presentationData: PresentationData): Unit = {
      presentationData.setPresentableText(value.restriction.name)
    }
  }

}
