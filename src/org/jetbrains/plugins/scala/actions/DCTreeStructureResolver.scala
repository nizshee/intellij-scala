package org.jetbrains.plugins.scala.actions

import java.util

import com.intellij.ide.projectView.{PresentationData, ViewSettings}
import com.intellij.ide.projectView.impl.nodes.AbstractPsiBasedNode
import com.intellij.ide.util.treeView.{AbstractTreeNode, AbstractTreeStructure, NodeDescriptor}
import com.intellij.openapi.editor.colors.CodeInsightColors
import com.intellij.openapi.project.Project
import com.intellij.psi.util.PsiTreeUtil
import com.intellij.psi.{PsiElement, PsiField, PsiMethod, PsiNamedElement}
import org.jetbrains.plugins.scala.actions.DCTreeStructureCompatibility.{CompatibilityNode, CompatibilityValue, MostSpecificNode, MostSpecificValue}
import org.jetbrains.plugins.scala.actions.DCTreeStructureConformance.{ConditionNode, RelationNode}
import org.jetbrains.plugins.scala.actions.DCTreeStructureSubstitutor.{SubstitutorNode, SubstitutorValue, TypeVariableNode}
import org.jetbrains.plugins.scala.lang.psi.api.base.ScPrimaryConstructor
import org.jetbrains.plugins.scala.lang.psi.api.base.patterns.ScReferencePattern
import org.jetbrains.plugins.scala.lang.psi.api.statements.{ScFun, ScFunction, ScPatternDefinition, ScVariableDefinition}
import org.jetbrains.plugins.scala.lang.psi.api.toplevel.ScTypedDefinition
import org.jetbrains.plugins.scala.lang.psi.types.api.Nothing

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
//  @inline private def el2String(el: PsiNamedElement): String = el.getNode.getText

  @inline private def el2String(el: PsiNamedElement): String = el match {
    case fun: ScFun => fun.methodType.toString
    case f: ScFunction => "???1"
      val name = f.name
      val ty = f.getType().getOrNothing
      s"$name: $ty"
    case p: ScPrimaryConstructor => "???2"
    case m: PsiMethod => "???3"
    case refPatt: ScReferencePattern => refPatt.getParent.getParent match { // TODO temroary
      case pd: ScPatternDefinition if PsiTreeUtil.isContextAncestor(pd, el, true) =>
        val name = pd.declaredNames.headOption.getOrElse("unknown")
        val ty = pd.getType().getOrNothing
        s"$name.apply: $ty"
      case vd: ScVariableDefinition if PsiTreeUtil.isContextAncestor(vd, el, true) =>
        val name = vd.declaredNames.headOption.getOrElse("unknown")
        val ty = vd.getType().getOrNothing
        s"$name.apply: $ty"
      case _ => "unknown"
    }
    case typed: ScTypedDefinition => "???5"
    case f: PsiField => "???6"
    case _ => "unknown"
  }

  case class Value(el: PsiNamedElement, candidate: DCHandler.Resolver#Candidate, prefix: String = "")
  case class CandidateValue(el: PsiNamedElement, candidate: DCHandler.Resolver#Candidate)
//  case class ProblemValue(problem: String)
  case class WeightsValue(weights: Map[PsiNamedElement, DCHandler.Resolver#Weight])
  case class WeightValue(el: PsiNamedElement, weight: DCHandler.Resolver#Weight)

//  class CandidateNode(value: CandidateValue)(implicit project: Project) extends AbstractTreeNode[CandidateValue](project, value) {
////    private val problems = value.candidate.rr.iterator.flatMap { rr =>
////      rr.problems.map { p =>
////        new ProblemNode(project, ProblemValue(p.toString))
////      }
////    }.toSeq
//
//    private val greaterWeight = value.candidate.weights.values.forall(w => w.v > w.opposite)
//    private val restictionsHaveSolution = value.candidate.restrictions.forall(_.`type`.nonEmpty)
//    private val conditionsExists = value.candidate.args.forall(_.conditions.exists(_.satisfy))
//    private val weights = Some(value.candidate.weights).filter(_.nonEmpty).map(w => new WeightNode(WeightsValue(w)))
//    private val compatibility = Some(value.candidate.args).filter(_.nonEmpty).map(a => new CompatibilityNode(CompatibilityValue(a)))
//    private val restrictions = Some(value.candidate.restrictions).filter(_.nonEmpty).map(r => new SubstitutorNode(SubstitutorValue(r)))
//
//
//    override def getChildren: util.Collection[_ <: AbstractTreeNode[_]] = {
//      val list = new util.ArrayList[AbstractTreeNode[_]]()
//      compatibility.foreach(list.add)
//      restrictions.foreach(list.add)
//      weights.foreach(list.add)
//      list
//    }
//
//    override def update(presentationData: PresentationData): Unit = {
//      val text = el2String(value.el)
//      presentationData.setPresentableText(text)
//      if (!greaterWeight || !conditionsExists || !restictionsHaveSolution)
//        presentationData.setAttributesKey(CodeInsightColors.WRONG_REFERENCES_ATTRIBUTES)
//    }
//  }

  class CandidateNode(value: CandidateValue)(implicit project: Project) extends AbstractPsiBasedNode[CandidateValue](project, value, ViewSettings.DEFAULT) {
    private val greaterWeight = value.candidate.weights.values.forall(w => w.v > w.opposite)
    private val restictionsHaveSolution = value.candidate.restrictions.forall(_.`type`.nonEmpty)
    private val conditionsExists = value.candidate.args.forall(_.conditions.exists(_.satisfy))
    private val weights = Some(value.candidate.weights).filter(_.nonEmpty).map(w => new WeightNode(WeightsValue(w)))
    private val compatibility = Some(value.candidate.args).filter(_.nonEmpty).map(a => new CompatibilityNode(CompatibilityValue(a)))
    private val restrictions = Some(value.candidate.restrictions).filter(_.nonEmpty).map(r => new SubstitutorNode(SubstitutorValue(r)))

    override def getChildrenImpl: util.Collection[AbstractTreeNode[_]] = {
      val list = new util.ArrayList[AbstractTreeNode[_]]()
      compatibility.foreach(list.add)
      restrictions.foreach(list.add)
      weights.foreach(list.add)
      list
    }

    override def updateImpl(presentationData: PresentationData): Unit = {
      val text = el2String(value.el)
      presentationData.setPresentableText(text)
      if (!greaterWeight || !conditionsExists || !restictionsHaveSolution)
        presentationData.setAttributesKey(CodeInsightColors.WRONG_REFERENCES_ATTRIBUTES)
    }

    override def extractPsiFromValue(): PsiElement = value.el
  }


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
