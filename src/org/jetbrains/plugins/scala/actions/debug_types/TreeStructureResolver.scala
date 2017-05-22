package org.jetbrains.plugins.scala.actions.debug_types

import java.util

import com.intellij.ide.projectView.impl.nodes.AbstractPsiBasedNode
import com.intellij.ide.projectView.{PresentationData, ViewSettings}
import com.intellij.ide.util.treeView.{AbstractTreeNode, AbstractTreeStructure, NodeDescriptor}
import com.intellij.openapi.editor.colors.CodeInsightColors
import com.intellij.openapi.project.Project
import com.intellij.psi.util.PsiTreeUtil
import com.intellij.psi.{PsiElement, PsiField, PsiMethod, PsiNamedElement}
import TreeStructureSubstitutor.{SubstitutorNode, SubstitutorValue, TypeVariableNode}
import org.jetbrains.plugins.scala.actions.debug_types.TreeStructureCompatibility.{CompatibilityNode, CompatibilityValue, MostSpecificNode, MostSpecificValue}
import org.jetbrains.plugins.scala.actions.debug_types.TreeStructureConformance._
import org.jetbrains.plugins.scala.lang.psi.api.base.ScPrimaryConstructor
import org.jetbrains.plugins.scala.lang.psi.api.base.patterns.ScReferencePattern
import org.jetbrains.plugins.scala.lang.psi.api.statements.{ScFun, ScFunction, ScPatternDefinition, ScVariableDefinition}
import org.jetbrains.plugins.scala.lang.psi.api.toplevel.ScTypedDefinition
import org.jetbrains.plugins.scala.lang.psi.types._

/**
  * Created by user on 4/10/17.
  */
class TreeStructureResolver(values: Seq[TreeStructureResolver.Value])(implicit project: Project) extends AbstractTreeStructure {
  import TreeStructureResolver._

  private class RootNode extends AbstractTreeNode[Any](project, ()) {
    override def getChildren: util.Collection[_ <: AbstractTreeNode[_]] = {
      val list = new util.ArrayList[AbstractTreeNode[_]]()
      values.foreach { value => list.add(new CandidateNode(CandidateValue(value.el, value.candidate, value.ret))) }
      list
    }

    override def update(presentationData: PresentationData): Unit = {}
  }

  override def getParentElement(o: scala.Any): AnyRef = null

  override def getRootElement: AnyRef = new RootNode

  override def getChildElements(o: scala.Any): Array[AnyRef] = o match {
    case _: RootNode => values.map(v =>  new CandidateNode(CandidateValue(v.el, v.candidate, v.ret))).toArray
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
    case n: TextNode =>
      val children = n.getChildren
      children.toArray(new Array[AnyRef](children.size))
    case n: ElementNode =>
      val children = n.getChildren
      children.toArray(new Array[AnyRef](children.size))
    case n: ActualElementNode =>
      val children = n.getChildren
      children.toArray(new Array[AnyRef](children.size))
    case n: CConditionNode =>
      val children = n.getChildren
      children.toArray(new Array[AnyRef](children.size))
    case n: EConditionNode =>
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

object TreeStructureResolver {
//  @inline private def el2String(el: PsiNamedElement): String = MostSpecificUtil(el, 0)(ScalaTypeSystem).getType(el, implicitCase = false).toString
//  @inline private def el2String(el: PsiNamedElement): String = el.getNode.getText

  @inline private def el2String(el: PsiNamedElement): String = el match {
    case fun: ScFun => fun.methodType.toString
    case f: ScFunction =>
      val name = f.name
      val ty = f.getType().getOrNothing
      (if (f.typeParameters.nonEmpty) s"[${f.typeParameters.map(_.name).mkString(", ")}] " else "") + s"$name: $ty"
    case p: ScPrimaryConstructor => s"${p.getName}: ${p.polymorphicType}"
    case m: PsiMethod =>
      val name = m.getName
      val tParams = if (m.getTypeParameterList.getTypeParameters.nonEmpty)
        "[" + m.getTypeParameterList.getTypeParameters.map(_.getName).mkString(", ") + "] " else ""
      val r = m.getReturnType
      val params = "(" + m.getParameterList.getParameters.map(p => s"${p.getName}: ${p.getType}").mkString(", ") + ")"
      s"$tParams$name: $params => $r"
    case refPatt: ScReferencePattern => refPatt.getParent.getParent match {
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
    case typed: ScTypedDefinition => s"${typed.name}: ${typed.getType().getOrNothing}"
    case f: PsiField => s"${f.getName}: ${f.getType}"
    case _ => "unknown"
  }

  case class Value(el: PsiNamedElement, candidate: DTHandler.Resolver#Candidate, ret: Option[DTHandler.Resolver#Ret], prefix: String = "")
  case class CandidateValue(el: PsiNamedElement, candidate: DTHandler.Resolver#Candidate, ret: Option[DTHandler.Resolver#Ret])
  case class WeightValue(el: PsiNamedElement, weight: DTHandler.Resolver#Weight)
  case class WeightsValue(weights: Map[PsiNamedElement, DTHandler.Resolver#Weight])

  class CandidateNode(value: CandidateValue)(implicit project: Project) extends AbstractPsiBasedNode[CandidateValue](project, value, ViewSettings.DEFAULT) {
    private val rc = RelationContext(value.candidate.restrictions.find(_.forall(_.satisfy)).getOrElse(Seq()))
    private val greaterWeight = value.candidate.weights.values.forall(_.wins)
    private val restictionsHaveSolution = value.candidate.restrictions.exists(_.forall(_.`type`.nonEmpty)) || value.candidate.restrictions.isEmpty
    private val conditionsExists = value.candidate.args.forall(_.conditions.exists(_.satisfy(rc)))
    private val problems = value.candidate.rr.iterator.flatMap(_.problems).toSeq.filterNot {
      case ExpectedTypeMismatch => true
      case _: TypeMismatch => true
      case WrongTypeParameterInferred => true
      case _ => false
    }

    override def getChildrenImpl: util.Collection[AbstractTreeNode[_]] = {
      val list = new util.ArrayList[AbstractTreeNode[_]]()
      if (problems.nonEmpty) {
        val texts = problems.map {
          case DoesNotTakeParameters() => "Function does not take parameters"
          case ExcessArgument(_) => "Too many arguments for method"
          case MalformedDefinition() => "Method has malformed definition"
          case ExpansionForNonRepeatedParameter(_) => "Expansion for non-repeated parameter"
          case PositionalAfterNamedArgument(_) => "Positional after named argument"
          case ParameterSpecifiedMultipleTimes(_) => "Parameter specified multiple times"
          case MissedValueParameter(p) =>
            "Unspecified value parameter: " + p.name + ": " + p.paramType.presentableText
          case _ => "Applicable problem"
        }
        texts.foreach(text => list.add(new TextNode(TextValue(text, satisfy = false))))
      }
      else {
        if (value.candidate.args.nonEmpty || value.ret.nonEmpty) {
          val rc = RelationContext(value.candidate.restrictions.find(_.forall(_.satisfy)).getOrElse(Seq()))
          list.add(new CompatibilityNode(CompatibilityValue(value.candidate.args, value.ret, rc)))
        }
        if (value.candidate.restrictions.exists(_.nonEmpty))
          list.add(new SubstitutorNode(SubstitutorValue(value.candidate.restrictions)))
        if (value.candidate.defaultInterfere)
          list.add(new TextNode(TextValue("uses default argument", satisfy = false)))
        if (value.candidate.wrongNameArguments.nonEmpty)
          list.add(new TextNode(TextValue(s"wrong named arguments: ${value.candidate.wrongNameArguments.mkString(", ")}", satisfy = false)))
        if (value.candidate.weights.nonEmpty)
          list.add(new WeightNode(WeightsValue(value.candidate.weights)))
      }
      list
    }

    override def updateImpl(presentationData: PresentationData): Unit = {
      val text = el2String(value.el)
      presentationData.setPresentableText(text)
      if (!greaterWeight || !conditionsExists || !restictionsHaveSolution || problems.nonEmpty ||
        value.candidate.defaultInterfere || value.candidate.wrongNameArguments.nonEmpty)
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
      val enough = weight.weights.values.forall(_.wins)
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
      value.weight.derived.foreach(_ => list.add(new TextNode(TextValue("derived", satisfy = true))))
      list
    }

    override def update(presentationData: PresentationData): Unit = {
      presentationData.setPresentableText(s"${value.weight.v} (${value.weight.opposite}) ${el2String(value.el)}")
      if (value.weight.v <= value.weight.opposite)
        presentationData.setAttributesKey(CodeInsightColors.WRONG_REFERENCES_ATTRIBUTES)
    }
  }

  case class TextValue(text: String, satisfy: Boolean)
  class TextNode(value: TextValue)(implicit project: Project) extends AbstractTreeNode[TextValue](project, value) {

    override def getChildren: util.Collection[_ <: AbstractTreeNode[_]] = new util.ArrayList[AbstractTreeNode[_]]()

    override def update(presentationData: PresentationData): Unit = {
      presentationData.setPresentableText(value.text)
      if (!value.satisfy) presentationData.setAttributesKey(CodeInsightColors.WRONG_REFERENCES_ATTRIBUTES)
    }
  }
}
