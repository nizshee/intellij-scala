package org.jetbrains.plugins.scala.actions

import java.awt.{BorderLayout, Dimension}
import java.util
import javax.swing.JPanel
import javax.swing.tree.{DefaultMutableTreeNode, DefaultTreeModel}

import com.intellij.ide.projectView.PresentationData
import com.intellij.ide.util.treeView.{AbstractTreeBuilder, AbstractTreeNode, AbstractTreeStructure, NodeDescriptor}
import com.intellij.openapi.actionSystem.{AnAction, AnActionEvent, CommonDataKeys}
import com.intellij.openapi.editor.Editor
import com.intellij.openapi.project.Project
import com.intellij.openapi.ui.popup.{JBPopup, JBPopupFactory}
import com.intellij.openapi.util.Disposer
import com.intellij.psi.util.PsiUtilBase
import com.intellij.psi.{PsiElement, PsiNamedElement, PsiWhiteSpace}
import com.intellij.ui.ScrollPaneFactory
import com.intellij.ui.treeStructure.Tree
import org.jetbrains.plugins.scala.lang.psi.api.ScalaFile
import org.jetbrains.plugins.scala.lang.psi.api.base.{ScFieldId, ScLiteral}
import org.jetbrains.plugins.scala.lang.psi.api.base.patterns.ScBindingPattern
import org.jetbrains.plugins.scala.lang.psi.api.expr.{ScExpression, ScMethodCall}
import org.jetbrains.plugins.scala.lang.psi.api.statements.params.ScParameter
import org.jetbrains.plugins.scala.lang.psi.types.api.designator.{ScDesignatorType, ScProjectionType, ScThisType}
import org.jetbrains.plugins.scala.lang.psi.types.api.{JavaArrayType, ParameterizedType, StdType, TypeParameterType, TypeSystem, UndefinedType}
import org.jetbrains.plugins.scala.lang.psi.types.nonvalue.{ScMethodType, ScTypePolymorphicType}
import org.jetbrains.plugins.scala.lang.psi.types.result.{Failure, Success}
import org.jetbrains.plugins.scala.lang.psi.types.{Conformance, ScType}
import org.jetbrains.plugins.scala.lang.refactoring.util.ScalaRefactoringUtil


object DebugConformanceAction {

  class Handler(nesting: Int = 0) {

    private val offset = nesting * 1
    private val delimeter = if (offset < 1) "" else "|" * (offset - 1) + "|"

    private var _conditions: Seq[ConformanceCondition] = Seq()
    private var _variances: Seq[ConformanceCondition.Variance] = Seq()

    def +(condition: ConformanceCondition): ConformanceCondition = {
      _conditions :+= condition
      condition
    }

    def +(variance: ConformanceCondition.Variance): Unit = _variances :+= variance

    def conditions: Seq[ConformanceCondition] = _conditions

    def relations: Seq[ConformanceCondition.Variance] = _variances

    def log(any: Any): Unit = println(delimeter + any)

    def logn(any: Any): Unit = {
      println(delimeter + any)
      println(delimeter)
    }

    def logt(left: ScType, right: ScType): Unit = {
      println(delimeter + s"left: ${left.presentableText}")
      println(delimeter + s"right: ${right.presentableText}")
    }

    def logtn(left: ScType, right: ScType): Unit = {
      println(delimeter + s"left: ${left.presentableText}")
      println(delimeter + s"right: ${right.presentableText}")
      println(delimeter)
    }

    def visit(any: Any): Unit = {
      println(delimeter + "visit " + any)
      println(delimeter)
    }

    def rvisit(any: Any): Unit = {
      println(delimeter + "right visit " + any)
      println(delimeter)
    }


    def inner: Handler =  new Handler(nesting + 1)

  }

  class CHandler {

  }

}

/**
  * Created by user on 3/20/17.
  */
class DebugConformanceAction extends AnAction("Debug conformance action") {

  private def showHint(hint: String)(implicit editor: Editor) = ScalaActionUtil.showHint(editor, hint)

  private def showPopup(values: Seq[Value])(implicit editor: Editor) = {
    val project = editor.getProject
    val tree = new Tree()

    val structure = new DebugConformanceTreeStructure(project, values)

    val builder = new AbstractTreeBuilder(tree, new DefaultTreeModel(new DefaultMutableTreeNode), structure, null) {
      override def isSmartExpand: Boolean = false
    }

    val jTree = builder.getTree
    jTree.setRootVisible(false)

    val minSize = jTree.getPreferredSize

    val scrollPane = ScrollPaneFactory.createScrollPane(jTree, true)

    val panel = new JPanel(new BorderLayout())

    panel.add(scrollPane, BorderLayout.CENTER)

    val popup: JBPopup = JBPopupFactory.getInstance().createComponentPopupBuilder(panel, jTree).
      setRequestFocus(true).
      setResizable(true).
      setTitle("Debug Conformance:").
      setMinSize(new Dimension(minSize.width + 500, minSize.height)).
      createPopup

    Disposer.register(popup, builder)

    popup.showInBestPositionFor(editor)
  }

  override def update(e: AnActionEvent) {
    ScalaActionUtil.enableAndShowIfInScalaFile(e)
  }

  override def actionPerformed(e: AnActionEvent): Unit = {
    val context = e.getDataContext
    val project = CommonDataKeys.PROJECT.getData(context)
    implicit val editor = CommonDataKeys.EDITOR.getData(context)
    if (project == null || editor == null) return
    val file = PsiUtilBase.getPsiFileInEditor(editor, project)
    if (!file.isInstanceOf[ScalaFile]) return

    if (editor.getSelectionModel.hasSelection) {
      val selectionStart = editor.getSelectionModel.getSelectionStart
      val selectionEnd = editor.getSelectionModel.getSelectionEnd
      val opt = ScalaRefactoringUtil.getExpression(project, editor, file, selectionStart, selectionEnd)


      val elements = ScalaRefactoringUtil.selectedElements(editor, file.asInstanceOf[ScalaFile], trimComments = false)

      elements.foreach {
        case m: ScMethodCall => println(m.getType())
        case _ =>
      }
      println(elements)
//      elements.foreach {
//        case e: ScNewTemplateDefinition =>
//          processScExpr(e)
//        case p: ScPatternDefinition => p match {
//          case ScPatternDefinition.expr(e) =>
//            processScExpr(e)
//          case _ =>
//            println("1")
//        }
//        case _ =>
//          println("2", e)
//      }

      opt match {
        case Some((expr, _)) => processScExpr(expr)
        case _ => showHint("No expression found.")
      }
    } else {
      println("TODO")
      val offset = editor.getCaretModel.getOffset
      val element: PsiElement = file.findElementAt(offset) match {
        case w: PsiWhiteSpace if w.getTextRange.getStartOffset == offset &&
          w.getText.contains("\n") => file.findElementAt(offset - 1)
        case p => p
      }
      println(e)
      element match {
        case e: PsiNamedElement => println(e)
      }
    }
  }


  private def processScExpr(e: ScExpression)(implicit editor: Editor): Unit = {
    implicit val typeSystem: TypeSystem = e.typeSystem

    val leftOption = e.expectedType()
    val rightTypeResult = e.getNonValueType().map(_.inferValueType)
    val handler = new DebugConformanceAction.Handler()
    leftOption match {
      case Some(left) => // TODO get fresh type variable if expected not found
        rightTypeResult match {
          case Success(right, _) =>
            handler.log("Action fired on:")
            handler.logtn(left, right)
            val inner = handler.inner
            val (canConform, subst) = Conformance.conformsInner(left, right, handler = Some(inner))
            val conformance = Relation.Conformance(left, right, inner.conditions)
            val values = Seq(Value(if (true) DebugConformanceAdapter(conformance) else conformance))
            showPopup(values)
            println(inner.conditions)
            if (canConform) {
              handler.logn("can conform")
            }
            else handler.logn("can't conform")
          case Failure(cause, _) => showHint(s"Can't derive type: $cause")
        }
      case None => showHint("No expected type found.")
    }


  }
}
