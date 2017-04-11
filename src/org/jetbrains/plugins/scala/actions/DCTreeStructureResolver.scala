package org.jetbrains.plugins.scala.actions

import java.util

import com.intellij.ide.projectView.PresentationData
import com.intellij.ide.util.treeView.{AbstractTreeNode, AbstractTreeStructure, NodeDescriptor}
import com.intellij.openapi.editor.colors.CodeInsightColors
import com.intellij.openapi.project.Project
import com.intellij.psi.PsiNamedElement

/**
  * Created by user on 4/10/17.
  */
class DCTreeStructureResolver(project: Project, values: Seq[DCTreeStructureResolver.Value]) extends AbstractTreeStructure {
  import DCTreeStructureResolver._

  private class RootNode extends AbstractTreeNode[Any](project, ()) {
    override def getChildren: util.Collection[_ <: AbstractTreeNode[_]] = {
      val list = new util.ArrayList[AbstractTreeNode[_]]()
      values.foreach { value => list.add(new CandidateNode(project, CandidateValue(value.el, value.candidate))) }
      list
    }

    override def update(presentationData: PresentationData): Unit = {}
  }

  override def getParentElement(o: scala.Any): AnyRef = null

  override def getRootElement: AnyRef = new RootNode

  override def getChildElements(o: scala.Any): Array[AnyRef] = o match {
    case _: RootNode => values.map(v =>  new CandidateNode(project, CandidateValue(v.el, v.candidate))).toArray
    case n: CandidateNode =>
      val children = n.getChildren
      children.toArray(new Array[AnyRef](children.size))
    case n: ProblemNode =>
      val children = n.getChildren
      children.toArray(new Array[AnyRef](children.size))
    case _ => Array.empty
  }

  override def createDescriptor(o: scala.Any, nodeDescriptor: NodeDescriptor[_]): NodeDescriptor[_] = o.asInstanceOf[NodeDescriptor[_]]

  override def hasSomethingToCommit: Boolean = false

  override def commit(): Unit = {}
}

object DCTreeStructureResolver {
  case class Value(el: PsiNamedElement, candidate: DCHandler.Resolver#Candidate, prefix: String = "")
  case class CandidateValue(el: PsiNamedElement, candidate: DCHandler.Resolver#Candidate)
  case class ProblemValue(problem: String)

  class CandidateNode(project: Project, candidate: CandidateValue) extends AbstractTreeNode[CandidateValue](project, candidate) {
    private val problems = candidate.candidate.rr.iterator.flatMap { rr =>
      rr.problems.map { p =>
        new ProblemNode(project, ProblemValue(p.toString))
      }
    }

    override def getChildren: util.Collection[_ <: AbstractTreeNode[_]] = {
      val list = new util.ArrayList[AbstractTreeNode[_]]()
      problems.foreach(list.add)
      list
    }

    override def update(presentationData: PresentationData): Unit = {
      val text = candidate.el.getNode.getText
      presentationData.setPresentableText(text)
      if (problems.nonEmpty) presentationData.setAttributesKey(CodeInsightColors.ERRORS_ATTRIBUTES)
    }
  }

  class ProblemNode(project: Project, problem: ProblemValue) extends AbstractTreeNode[ProblemValue](project, problem) {
    override def getChildren: util.Collection[_ <: AbstractTreeNode[_]] = {
      new util.ArrayList[AbstractTreeNode[_]]()
    }

    override def update(presentationData: PresentationData): Unit = {
      presentationData.setPresentableText(problem.problem)
      presentationData.setAttributesKey(CodeInsightColors.ERRORS_ATTRIBUTES)
    }
  }
}
