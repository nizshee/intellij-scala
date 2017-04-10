package org.jetbrains.plugins.scala.actions

import java.util

import com.intellij.ide.projectView.PresentationData
import com.intellij.ide.util.treeView.{AbstractTreeNode, AbstractTreeStructure, NodeDescriptor}
import com.intellij.openapi.project.Project

/**
  * Created by user on 4/10/17.
  */
class DCTreeStructureResolver(project: Project, values: Seq[DCTreeStructureResolver.Value]) extends AbstractTreeStructure {
  import DCTreeStructureResolver._

  private class RootNode extends AbstractTreeNode[Any](project, ()) {
    override def getChildren: util.Collection[_ <: AbstractTreeNode[_]] = {
      val list = new util.ArrayList[AbstractTreeNode[_]]()
      values.foreach { value => list.add(new CandidateNode(project, CandidateValue(value.candidate))) }
      list
    }

    override def update(presentationData: PresentationData): Unit = {}
  }

  override def getParentElement(o: scala.Any): AnyRef = null

  override def getRootElement: AnyRef = new RootNode

  override def getChildElements(o: scala.Any): Array[AnyRef] = o match {
    case _: RootNode => values.map(v =>  new CandidateNode(project, CandidateValue(v.candidate))).toArray
    case n: CandidateNode =>
      val children = n.getChildren
      children.toArray(new Array[AnyRef](children.size))
    case _ => Array.empty
  }

  override def createDescriptor(o: scala.Any, nodeDescriptor: NodeDescriptor[_]): NodeDescriptor[_] = o.asInstanceOf[NodeDescriptor[_]]

  override def hasSomethingToCommit: Boolean = false

  override def commit(): Unit = {}
}

object DCTreeStructureResolver {
  case class Value(candidate: DCHandler.Resolver#Candidate, prefix: String = "")
  case class CandidateValue(candidate: DCHandler.Resolver#Candidate)


  class CandidateNode(project: Project, candidate: CandidateValue) extends AbstractTreeNode[CandidateValue](project, candidate) {
    override def getChildren: util.Collection[_ <: AbstractTreeNode[_]] = {
      val list = new util.ArrayList[AbstractTreeNode[_]]()
      list
    }

    override def update(presentationData: PresentationData): Unit = {
      val el = candidate.candidate.rr.getActualElement
      val text = el.getNode.getText
      presentationData.setPresentableText(text)
    }
  }
}
