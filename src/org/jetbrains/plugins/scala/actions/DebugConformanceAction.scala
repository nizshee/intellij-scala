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
import com.intellij.psi.{PsiElement, PsiWhiteSpace}
import com.intellij.ui.ScrollPaneFactory
import com.intellij.ui.treeStructure.Tree
import org.jetbrains.plugins.scala.lang.psi.api.ScalaFile
import org.jetbrains.plugins.scala.lang.psi.api.base.{ScFieldId, ScLiteral}
import org.jetbrains.plugins.scala.lang.psi.api.base.patterns.ScBindingPattern
import org.jetbrains.plugins.scala.lang.psi.api.expr.ScExpression
import org.jetbrains.plugins.scala.lang.psi.api.statements.params.ScParameter
import org.jetbrains.plugins.scala.lang.psi.types.api.designator.{ScDesignatorType, ScProjectionType, ScThisType}
import org.jetbrains.plugins.scala.lang.psi.types.api.{JavaArrayType, ParameterizedType, StdType, TypeParameterType, TypeSystem, UndefinedType}
import org.jetbrains.plugins.scala.lang.psi.types.nonvalue.{ScMethodType, ScTypePolymorphicType}
import org.jetbrains.plugins.scala.lang.psi.types.result.{Failure, Success}
import org.jetbrains.plugins.scala.lang.psi.types.{Conformance, ScAbstractType, ScCompoundType, ScExistentialArgument, ScExistentialType, ScType, ScalaTypeVisitor}
import org.jetbrains.plugins.scala.lang.refactoring.util.ScalaRefactoringUtil


object DebugConformanceAction {
  private val debug: Boolean = true
  def pr(msg: String): Unit = if (debug) println(msg)

  case class Value(scType: ScType, prefix: String = "")

  class DebugConformanceTreeStructure(project: Project, values: Seq[Value]) extends AbstractTreeStructure {

    private class DebugConformanceNode(value: Value) extends AbstractTreeNode[Value](project, value) {

      private var children: Seq[Value] = Seq()

      private var text: String = ""

      private val visitor = new ScalaTypeVisitor {
        override def visitStdType(s: StdType): Unit = {
          pr("std")
          text = s.name
        }

        override def visitJavaArrayType(`type`: JavaArrayType): Unit = {
          pr("javaArray")
          ???
        }

        override def visitMethodType(m: ScMethodType): Unit = {
          pr("method")
          text = "method"
          children = m.params.zipWithIndex.map(p => Value(p._1.paramType, s"par${p._2}")) :+ Value(m.returnType, "ret")
        }

        override def visitUndefinedType(`type`: UndefinedType): Unit = {
          pr("undefined")
        }

        override def visitTypeParameterType(t: TypeParameterType): Unit = {
          pr("typeParameter")
          text = t.name
          children = t.arguments.map { argument => Value(argument) }
        }

        override def visitParameterizedType(p: ParameterizedType): Unit = {
          pr("parametrized")
          text = "parametrized"
          children = Value(p.designator, "designator") +: p.typeArguments.zipWithIndex.map(p => Value(p._1, s"arg${p._2}"))
        }

        override def visitProjectionType(p: ScProjectionType): Unit = {
          pr("projection")
        }

        override def visitThisType(t: ScThisType): Unit = {
          pr("this")
        }

        override def visitDesignatorType(d: ScDesignatorType): Unit = {
          text = d.element.getName // TODO how about type costructors?
          d.element match {
            case v: ScBindingPattern =>
              pr("binding pattern")
            case v: ScParameter =>
              pr("parameter")
            case v: ScFieldId =>
              pr("fieldId")
            case _ =>
              pr(d.isAliasType.toString)
          }
        }

        override def visitCompoundType(c: ScCompoundType): Unit = {
          pr("compound")
        }

        override def visitExistentialType(e: ScExistentialType): Unit = {
          pr("existential")
        }

        override def visitExistentialArgument(s: ScExistentialArgument): Unit = {
          pr("existentialArgument")
        }

        override def visitAbstractType(a: ScAbstractType): Unit = {
          pr("abstract")
        }

        override def visitTypePolymorphicType(t: ScTypePolymorphicType): Unit = {
          pr("typePolymorphic")
        }
      }

      value.scType.visitType(visitor)

      override def getChildren: util.Collection[_ <: AbstractTreeNode[_]] = {
        val list = new util.ArrayList[AbstractTreeNode[_]]()
        children.foreach { child =>
          list.add(new DebugConformanceNode(child))
        }
        list
      }

      override def update(presentationData: PresentationData): Unit = {
        presentationData.setPresentableText(value.prefix + (if (value.prefix.nonEmpty) ": " else "") + text)
      }

    }

    private class RootNode extends AbstractTreeNode[Any](project, ()) {
      override def getChildren: util.Collection[_ <: AbstractTreeNode[_]] = {
        val list = new util.ArrayList[AbstractTreeNode[_]]()
        values.foreach { result => list.add(new DebugConformanceNode(result)) }
        list
      }

      override def update(presentation: PresentationData): Unit = {}
    }

    override def getParentElement(o: scala.Any): AnyRef = null

    override def getRootElement: AnyRef = new RootNode

    override def getChildElements(o: scala.Any): Array[AnyRef] = o match {
      case _: RootNode => values.map(new DebugConformanceNode(_)).toArray
      case n: DebugConformanceNode =>
        val childrenImpl = n.getChildren
        childrenImpl.toArray(new Array[AnyRef](childrenImpl.size))
      case _ => Array.empty
    }

    override def createDescriptor(o: scala.Any, nodeDescriptor: NodeDescriptor[_]): NodeDescriptor[_] = o.asInstanceOf[NodeDescriptor[_]]

    override def hasSomethingToCommit: Boolean = false

    override def commit(): Unit = {}
  }

  class Handler(nesting: Int = 0, parent: Option[Handler] = None) {

    private val offset = nesting * 1
    private val delimeter = if (offset < 1) "" else "|" * (offset - 1) + "|"

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

    def inner: Handler = new Handler(nesting + 1, Some(this))
  }

}

/**
  * Created by user on 3/20/17.
  */
class DebugConformanceAction extends AnAction("Debug conformance action") {
  import DebugConformanceAction._

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
//      val elements = ScalaRefactoringUtil.selectedElements(editor, file.asInstanceOf[ScalaFile], trimComments = false)
//
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
    }
  }


  private def processScExpr(e: ScExpression)(implicit editor: Editor): Unit = {
    implicit val typeSystem: TypeSystem = e.typeSystem

    val leftOption = e.expectedType()
    e match {
      case l: ScLiteral => println(l.isSymbol)
      case _ =>
    }
//    val left1 = e match {
//      case f: ScFunction if f.paramClauses.clauses.length > 1 && !f.paramClauses.clauses.apply(1).isImplicit =>
//        Nothing
//      case f: ScFunction => f.returnType.getOrNothing
//      case f: ScFun => f.retType
//      case m: PsiMethod =>
//        Option(m.getReturnType).map { rt => rt.toScType() }.getOrElse(Nothing)
//      case _ =>
//        Nothing
//    }
//    println(left1)
    val rightTypeResult = e.getNonValueType().map(_.inferValueType)
    val handler = new DebugConformanceAction.Handler()
    leftOption match {
      case Some(left) => // TODO get fresh type variable if expected not found
        rightTypeResult match {
          case Success(right, _) =>
            handler.log("Action fired on:")
            handler.logtn(left, right)
//            val values = Seq(Value(right))
//            showPopup(values)
//            val (canConform, subst) = Conformance.conformsInner(left, right, handler = Some(handler.inner))
//            if (canConform) {
//              handler.logn("can conform")
//              handler.logn(subst)
//            }
//            else handler.logn("can't conform")
          case Failure(cause, _) => showHint(s"Can't derive type: $cause")
        }
      case None => showHint("No expected type found.")
    }


  }
}
