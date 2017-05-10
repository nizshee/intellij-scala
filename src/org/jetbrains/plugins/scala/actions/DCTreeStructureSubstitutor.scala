package org.jetbrains.plugins.scala.actions

import java.util

import com.intellij.ide.projectView.PresentationData
import com.intellij.ide.util.treeView.AbstractTreeNode
import com.intellij.openapi.editor.colors.CodeInsightColors
import com.intellij.openapi.project.Project
import org.jetbrains.plugins.scala.lang.psi.types.ScType
import org.jetbrains.plugins.scala.lang.psi.types.api.UndefinedType

import scala.util.{Left, Right}

/**
  * Created by user on 4/12/17.
  */
object DCTreeStructureSubstitutor {
  case class SubstitutorValue(restrictions: Seq[Seq[DCHandler.Substitutor#Restriction]])
  case class TypeVariableValue(restriction: DCHandler.Substitutor#Restriction)
  case class RestrictionValue(v: Either[ScType, ScType])

  class SubstitutorNode(value: SubstitutorValue)(implicit project: Project) extends AbstractTreeNode[SubstitutorValue](project, value) {
    private val restrictions = {
      if (value.restrictions.size == 1) value.restrictions.head.map(r => new TypeVariableNode(TypeVariableValue(r)))
      else value.restrictions.map(r => new SubstitutorNode(SubstitutorValue(Seq(r))))
    }

    override def getChildren: util.Collection[_ <: AbstractTreeNode[_]] = {
      val list = new util.ArrayList[AbstractTreeNode[_]]()
      restrictions.foreach(list.add)
      list
    }

    override def update(presentationData: PresentationData): Unit = {
      if (value.restrictions.size == 1) presentationData.setPresentableText("restrictions")
      else presentationData.setPresentableText("variants")

      if (value.restrictions.size == 1 && value.restrictions.head.exists(_.`type`.isEmpty))
        presentationData.setAttributesKey(CodeInsightColors.WRONG_REFERENCES_ATTRIBUTES)
      else if (value.restrictions.forall(_.exists(_.`type`.isEmpty)))
        presentationData.setAttributesKey(CodeInsightColors.WRONG_REFERENCES_ATTRIBUTES)
    }
  }

  class TypeVariableNode(value: TypeVariableValue)(implicit project: Project) extends AbstractTreeNode[TypeVariableValue](project, value) {
    private val restrictions =
      value.restriction.uppers.map(r => new RestrictionNode(RestrictionValue(Left(r)))) ++
      value.restriction.lowers.map(r => new RestrictionNode(RestrictionValue(Right(r))))

    override def getChildren: util.Collection[_ <: AbstractTreeNode[_]] = {
      val list = new util.ArrayList[AbstractTreeNode[_]]()
      restrictions.foreach(list.add)
      list
    }

    override def update(presentationData: PresentationData): Unit = {
      presentationData.setPresentableText(value.restriction.name._1 +
        value.restriction.`type`.map(t => s" := $t").getOrElse(""))
      if (value.restriction.`type`.isEmpty)
        presentationData.setAttributesKey(CodeInsightColors.WRONG_REFERENCES_ATTRIBUTES)
    }
  }

  class RestrictionNode(value: RestrictionValue)(implicit project: Project) extends AbstractTreeNode[RestrictionValue](project, value) {
    override def getChildren: util.Collection[_ <: AbstractTreeNode[_]] = {
      val list = new util.ArrayList[AbstractTreeNode[_]]()
      list
    }

    override def update(presentationData: PresentationData): Unit = {
      value.v match {
        case Left(a) =>
          presentationData.setPresentableText(s">: $a")
        case Right(b) =>
          presentationData.setPresentableText(s"<: $b")
      }
    }
  }

}
