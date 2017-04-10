package org.jetbrains.plugins.scala.actions

import java.awt.{BorderLayout, Dimension}
import javax.swing.JPanel
import javax.swing.tree.{DefaultMutableTreeNode, DefaultTreeModel}

import com.intellij.ide.util.treeView.{AbstractTreeBuilder, AbstractTreeStructure}
import com.intellij.openapi.actionSystem.{AnAction, AnActionEvent, CommonDataKeys}
import com.intellij.openapi.editor.Editor
import com.intellij.openapi.ui.popup.{JBPopup, JBPopupFactory}
import com.intellij.openapi.util.Disposer
import com.intellij.psi.search.GlobalSearchScope
import com.intellij.psi.util.PsiUtilBase
import com.intellij.psi.{PsiElement, PsiNamedElement, PsiWhiteSpace}
import com.intellij.ui.ScrollPaneFactory
import com.intellij.ui.treeStructure.Tree
import org.jetbrains.plugins.scala.lang.psi.api.ScalaFile
import org.jetbrains.plugins.scala.lang.psi.api.base.ScReferenceElement
import org.jetbrains.plugins.scala.lang.psi.api.expr.{ScExpression, ScMethodCall, ScReferenceExpression}
import org.jetbrains.plugins.scala.lang.psi.types.api.TypeSystem
import org.jetbrains.plugins.scala.lang.psi.types.result.{Failure, Success}
import org.jetbrains.plugins.scala.lang.psi.types.{Compatibility, Conformance, ScType, ScUndefinedSubstitutor}
import org.jetbrains.plugins.scala.lang.refactoring.util.ScalaRefactoringUtil
import org.jetbrains.plugins.scala.lang.resolve.processor.MethodResolveProcessor
import org.jetbrains.plugins.scala.lang.resolve.{ReferenceExpressionResolver, ScalaResolveResult}


object DebugConformanceAction {



}

/**
  * Created by user on 3/20/17.
  */
class DebugConformanceAction extends AnAction("Debug conformance action") {

  private def showHint(hint: String)(implicit editor: Editor) = ScalaActionUtil.showHint(editor, hint)

  private def showPopup(treeStructure: AbstractTreeStructure)(implicit editor: Editor) = {
    val tree = new Tree()

    val builder = new AbstractTreeBuilder(tree, new DefaultTreeModel(new DefaultMutableTreeNode), treeStructure, null) {
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
      println(elements)

      // TODO need to handle arguments somehow, not only functions
      elements.foreach { // TODO how to handle dsl style like a + b
        case e: ScReferenceExpression =>
          processReferenceExpression(e)
        case e: ScExpression =>
          e.getContext.getContext match {
            case m: ScMethodCall =>
              m.deepestInvokedExpr match {
                case r: ScReferenceElement =>
                  val rrOption = r.bind()
                  rrOption.flatMap(_.innerResolveResult).orElse(rrOption) match {
                    case Some(rr) => processScResolveRes(m.args.exprs, rr, m.getResolveScope)
                    case _ =>
                  }
              }
            case c => println(s"not method - $c")
          }
          println(e)
        case m: ScMethodCall =>
          m.deepestInvokedExpr match {
            case r: ScReferenceElement =>
              val rrOption = r.bind()
              rrOption.flatMap(_.innerResolveResult).orElse(rrOption) match {
                case Some(rr) => processScResolveRes(m.args.exprs, rr, m.getResolveScope)
                case _ =>
              }
            case _ =>
          }
        case _ =>
      }

//      opt match {
//        case Some((expr, _)) => processScExpr(expr)
//        case _ => showHint("No expression found.")
//      }
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

  private def processReferenceExpression(reference: ScReferenceExpression)(implicit editor: Editor) = {
    val handler = new DCHandler.Resolver
    ReferenceExpressionResolver.resolve(reference, shapesOnly = false, incomplete = true,  handler = Some(handler))

    val values = handler.candidates.map(c => DCTreeStructureResolver.Value(c))
    showPopup(new DCTreeStructureResolver(editor.getProject, values))

  }

  // TODO check how works with implicits
  private def processScResolveRes(args: Seq[ScExpression], rr: ScalaResolveResult, scope: GlobalSearchScope) = {
    val handler = new DCHandler.Compatibility

    val argExprs = args.map(Compatibility.Expression.apply) // TODO how to handle many parrents?
    val element = rr.getActualElement
    val s = rr.substitutor
    val subs = MethodResolveProcessor.undefinedSubstitutor(element, s, false, Seq()) // TODO maybe typeArgElements is necessary
    println(s"begining subs is $subs")
    val c = Compatibility.compatible(element, subs, List(argExprs), false, scope, false, handler = Some(handler))
    println(handler.args)
    val sHandler = new DCHandler.Substitutor
    c.undefSubst.getSubstitutorWithBounds(notNonable = true, handler = Some(sHandler)) match {
      case Some((substitutor, _, _)) =>
        println(substitutor)
      case None =>
    }

    c.problems.foreach { p =>
      println(p.description)
    }
  }


  private def processScExpr(e: ScExpression)(implicit editor: Editor): Unit = {
    implicit val typeSystem: TypeSystem = e.typeSystem
    val handler = new DCHandler.Conformance(true)

    val leftOption = e.expectedType()
    val rightTypeResult = e.getNonValueType().map(_.inferValueType)
    leftOption match {
      case Some(left) => // TODO get fresh type variable if expected not found
        rightTypeResult match {
          case Success(right, _) =>
            handler.log("Action fired on:")
            handler.logtn(left, right)
            val inner = handler.inner
            val (canConform, subst) = Conformance.conformsInner(left, right, handler = Some(inner))
            val conformance = Relation.Conformance(left, right, inner.conditions)
            val values = Seq(DCTreeStructureConformance.Value(if (true) DebugConformanceAdapter(conformance) else conformance))
            showPopup(new DCTreeStructureConformance(editor.getProject, values))
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
