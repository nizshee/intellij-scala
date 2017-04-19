package org.jetbrains.plugins.scala.actions

import java.util

import com.intellij.ide.projectView.PresentationData
import com.intellij.ide.util.treeView.{AbstractTreeNode, AbstractTreeStructure, NodeDescriptor}
import com.intellij.openapi.editor.colors.CodeInsightColors
import com.intellij.openapi.project.Project
import com.intellij.psi.PsiNamedElement
import org.jetbrains.plugins.scala.actions.DCTreeStructureCompatibility.{CompatibilityNode, CompatibilityValue, MostSpecificNode, MostSpecificValue}
import org.jetbrains.plugins.scala.actions.DCTreeStructureConformance.{ConditionNode, RelationNode}
import org.jetbrains.plugins.scala.actions.DCTreeStructureSubstitutor.{SubstitutorNode, SubstitutorValue, TypeVariableNode}

/**
  * Created by user on 4/10/17.
  */
class DCTreeStructureResolver(values: Seq[DCTreeStructureResolver.Value])(implicit project: Project) extends AbstractTreeStructure {
  import DCTreeStructureResolver._

  private class RootNode extends AbstractTreeNode[Any](project, ()) {
    override def getChildren: util.Collection[_ <: AbstractTreeNode[_]] = {
      val list = new util.ArrayList[AbstractTreeNode[_]]()
      values.foreach { value => list.add(new CandidateNode(CandidateValue(value.el, value.candidate))) }
      list
    }

    override def update(presentationData: PresentationData): Unit = {}
  }

  override def getParentElement(o: scala.Any): AnyRef = null

  override def getRootElement: AnyRef = new RootNode

  override def getChildElements(o: scala.Any): Array[AnyRef] = o match {
    case _: RootNode => values.map(v =>  new CandidateNode(CandidateValue(v.el, v.candidate))).toArray
    case n: CandidateNode =>
      val children = n.getChildren
      children.toArray(new Array[AnyRef](children.size))
//    case n: ProblemNode =>
//      val children = n.getChildren
//      children.toArray(new Array[AnyRef](children.size))
    case n: WeightNode =>
      val children = n.getChildren
      children.toArray(new Array[AnyRef](children.size))
    case n: WeightSubNode =>
      val children = n.getChildren
      children.toArray(new Array[AnyRef](children.size))
    case n: CompatibilityNode =>
      val children = n.getChildren
      children.toArray(new Array[AnyRef](children.size))
    case n: RelationNode =>
      val children = n.getChildren
      children.toArray(new Array[AnyRef](children.size))
    case n: ConditionNode =>
      val children = n.getChildren
      children.toArray(new Array[AnyRef](children.size))
    case n: SubstitutorNode =>
      val children = n.getChildren
      children.toArray(new Array[AnyRef](children.size))
    case n: TypeVariableNode =>
      val children = n.getChildren
      children.toArray(new Array[AnyRef](children.size))
    case n: MostSpecificNode =>
      val children = n.getChildren
      children.toArray(new Array[AnyRef](children.size))
    case _ => Array.empty
  }

  override def createDescriptor(o: scala.Any, nodeDescriptor: NodeDescriptor[_]): NodeDescriptor[_] = o.asInstanceOf[NodeDescriptor[_]]

  override def hasSomethingToCommit: Boolean = false

  override def commit(): Unit = {}
}

object DCTreeStructureResolver {
//  @inline private def el2String(el: PsiNamedElement): String = MostSpecificUtil(el, 0)(ScalaTypeSystem).getType(el, implicitCase = false).toString
  @inline private def el2String(el: PsiNamedElement): String = el.getNode.getText

  case class Value(el: PsiNamedElement, candidate: DCHandler.Resolver#Candidate, prefix: String = "")
  case class CandidateValue(el: PsiNamedElement, candidate: DCHandler.Resolver#Candidate)
//  case class ProblemValue(problem: String)
  case class WeightsValue(weights: Map[PsiNamedElement, DCHandler.Resolver#Weight])
  case class WeightValue(el: PsiNamedElement, weight: DCHandler.Resolver#Weight)

  class CandidateNode(value: CandidateValue)(implicit project: Project) extends AbstractTreeNode[CandidateValue](project, value) {
//    private val problems = value.candidate.rr.iterator.flatMap { rr =>
//      rr.problems.map { p =>
//        new ProblemNode(project, ProblemValue(p.toString))
//      }
//    }.toSeq

    private val greaterWeight = value.candidate.weights.values.forall(w => w.v > w.opposite)
    private val restictionsHaveSolution = value.candidate.restrictions.forall(_.`type`.nonEmpty)
    private val conditionsExists = value.candidate.args.forall(_.conditions.exists(_.satisfy))
    private val weights = Some(value.candidate.weights).filter(_.nonEmpty).map(w => new WeightNode(WeightsValue(w)))
    private val compatibility = Some(value.candidate.args).filter(_.nonEmpty).map(a => new CompatibilityNode(CompatibilityValue(a)))
    private val restrictions = Some(value.candidate.restrictions).filter(_.nonEmpty).map(r => new SubstitutorNode(SubstitutorValue(r)))


    override def getChildren: util.Collection[_ <: AbstractTreeNode[_]] = {
      val list = new util.ArrayList[AbstractTreeNode[_]]()
      compatibility.foreach(list.add)
      restrictions.foreach(list.add)
      weights.foreach(list.add)
      list
    }

    override def update(presentationData: PresentationData): Unit = {
      val text = el2String(value.el)
      presentationData.setPresentableText(text)
      if (!greaterWeight || !conditionsExists || !restictionsHaveSolution)
        presentationData.setAttributesKey(CodeInsightColors.WRONG_REFERENCES_ATTRIBUTES)
    }
  }

//  class ProblemNode(project: Project, problem: ProblemValue) extends AbstractTreeNode[ProblemValue](project, problem) {
//    override def getChildren: util.Collection[_ <: AbstractTreeNode[_]] = new util.ArrayList[AbstractTreeNode[_]]()
//
//    override def update(presentationData: PresentationData): Unit = {
//      presentationData.setPresentableText(problem.problem)
//      presentationData.setAttributesKey(CodeInsightColors.ERRORS_ATTRIBUTES)
//      presentationData.setAttributesKey(CodeInsightColors.WRONG_REFERENCES_ATTRIBUTES)
//    }
//  }

  class WeightNode(weight: WeightsValue)(implicit project: Project) extends AbstractTreeNode[WeightsValue](project, weight) {
    override def getChildren: util.Collection[_ <: AbstractTreeNode[_]] = {
      val list = new util.ArrayList[AbstractTreeNode[_]]()
      weight.weights.foreach { case (el, w) =>
        list.add(new WeightSubNode(WeightValue(el, w)))
      }
      list
    }

    override def update(presentationData: PresentationData): Unit = {
      val enough = weight.weights.values.forall(w => w.v > w.opposite)
      presentationData.setPresentableText("relative weights")
      if (!enough)
        presentationData.setAttributesKey(CodeInsightColors.WRONG_REFERENCES_ATTRIBUTES)
    }
  }

  class WeightSubNode(value: WeightValue)(implicit project: Project) extends AbstractTreeNode[WeightValue](project, value) {
    private val asSpecificAs = value.weight.asSpecificAs.map(s => new MostSpecificNode(MostSpecificValue(s)))

    override def getChildren: util.Collection[_ <: AbstractTreeNode[_]] = {
      val list = new util.ArrayList[AbstractTreeNode[_]]()
      asSpecificAs.foreach(list.add)
      list
    }

    override def update(presentationData: PresentationData): Unit = {
      presentationData.setPresentableText(s"${value.weight.v} (${value.weight.opposite}) ${el2String(value.el)}")
      if (value.weight.v <= value.weight.opposite)
        presentationData.setAttributesKey(CodeInsightColors.WRONG_REFERENCES_ATTRIBUTES)
    }
  }
}
