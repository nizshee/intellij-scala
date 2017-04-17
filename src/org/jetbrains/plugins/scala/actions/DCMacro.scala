package org.jetbrains.plugins.scala.actions

import scala.reflect.macros.whitebox.Context
import scala.language.experimental.macros
import scala.annotation.StaticAnnotation
import scala.annotation.compileTimeOnly
import scala.collection.immutable.{::, Nil}


@compileTimeOnly("for explicit generation")
class instrumentated extends StaticAnnotation

@compileTimeOnly("generate two methods / classes")
class uninstrumental(parameterName: String) extends StaticAnnotation {
  def macroTransform(annottees: Any*): Any = macro generateInstrumentationMacro.impl
}

/** todo
  * create class with new
  */
object generateInstrumentationMacro {
  /**
    * Generates from annotated method / class `f` two methods `f` and `f$I`.
    * NonInstrumentated version `f` not contains constructions connected with instrumental tool like:
    *   - arguments `parameterName: Option[???] = None`
    *   - applications like parameterName.foreach { _ => }
    *   - new values obtained with transformations like `val inner = handler.map(_ => ???)` (not works with def) (not looks forward)
    *   - simplify boolean expressions like `a && handler.isEmpty`
    *   - parameters in function calls like `g(..., handler = inner)`
    * Instrumentated version `f$I` contains all constructions and transforms all connected functions calls:
    *   - `g(..., handler = inner)` -> `g$I(..., handler = inner)`
    */
  def impl(c: Context)(annottees: c.Expr[Any]*): c.Expr[Any] = {
    import c.universe._

    val parameter = c.prefix match {
      case Expr(q"new uninstrumental($s)") => c.eval[String](c.Expr(s))
      case _ => c.abort(c.enclosingPosition, "No parameter name was given!")
    }

    def prepareBlock(body: List[Tree], instrumentation: Set[String], remove: Boolean, e: Option[String] = None): (List[Tree], Set[String]) = body match {
      case Nil => (Nil, instrumentation)
      case head :: tail => head match {
        case ValDef(_, TermName(name), _, Apply(Select(Ident(TermName(fName)), TermName(_)), _)) if instrumentation(fName) =>
          val (nTail, nForbidden) = prepareBlock(tail, instrumentation + name, remove, e)
          val list = if (remove) nTail else head :: nTail
          (list, nForbidden)
        case ValDef(_, TermName(name), _, _) if e.contains(name) =>
          val (nTail, nForbidden) = prepareBlock(tail, instrumentation, remove, e)
          val list = if (remove) nTail else head :: nTail
          (list, nForbidden)
        case ValDef(_, TermName(name), _, _) =>
          val (nTail, nForbidden) = prepareBlock(tail, instrumentation - name, remove, e)
          (head :: nTail, nForbidden)
        case Apply(Select(Ident(TermName(name)), TermName(_)), _) if instrumentation(name) =>
          val (nTail, nForbidden) = prepareBlock(tail, instrumentation, remove, e)
          val list = if (remove) nTail else head :: nTail
          (list, nForbidden)
        case o =>
          val (nTail, nForbidden) = prepareBlock(tail, instrumentation, remove, e)
          (o :: nTail, nForbidden)
      }

    }

    def instrumentedTransformer(init: Set[String] = Set(parameter)) = new Transformer {
      private var instrumentation = init

      override def transform(tree: c.universe.Tree): c.universe.Tree = tree match {
        case f@DefDef(_, _, _, args, _, _) =>
          val names = args.flatMap(_.collect { case ValDef(_, TermName(name), _, _) => name }).toSet
          val permitted = instrumentation.intersect(names)
          instrumentation --= permitted
          val res = super.transform(f)
          instrumentation ++= permitted
          res
        case c@ClassDef(_, _, _, Template(_, _, body)) =>
          val (_, nForbidden) = prepareBlock(body, instrumentation, remove = false)
          val pForbidden = instrumentation
          instrumentation = nForbidden
          val res = super.transform(c)
          instrumentation = pForbidden
          res
        case b@Block(body, _) =>
          val (_, nForbidden) = prepareBlock(body, instrumentation, remove = false)
          val pForbidden = instrumentation
          instrumentation = nForbidden
          val res = super.transform(b)
          instrumentation = pForbidden
          res
        case Apply(Ident(TermName(fName)), args) =>
          val contains = args.exists {
            case Ident(TermName(name)) => instrumentation(name)
            case AssignOrNamedArg(_, Ident(TermName(name))) => instrumentation(name)
            case _ => false
          }
          val nName = if (contains) fName + "$I" else fName
          Apply(Ident(TermName(nName)), args)
        case _ => super.transform(tree)
      }
    }

    def nonInstrumentedTransformer(init: Set[String] = Set(parameter)) = new Transformer {
      private var instrumentation = init

      override def transform(tree: c.universe.Tree): c.universe.Tree = tree match {
        case f@DefDef(_, _, _, args, _, _) =>
          val names = args.flatMap(_.collect { case ValDef(_, TermName(name), _, _) => name }).toSet
          val permitted = instrumentation.intersect(names)
          instrumentation --= permitted
          val res = super.transform(f)
          instrumentation ++= permitted
          res
        case ClassDef(mods, name, targs, Template(parents, self, body)) =>
          val (nBody, nForbidden) = prepareBlock(body, instrumentation, remove = true)
          val pForbidden = instrumentation
          instrumentation = nForbidden
          val res = super.transform(ClassDef(mods, name, targs, Template(parents, self, nBody)))
          instrumentation = pForbidden
          res
        case Block(body, tpt) =>
          val (nBody, nForbidden) = prepareBlock(body, instrumentation, remove = true)
          val pForbidden = instrumentation
          instrumentation = nForbidden
          val res = super.transform(Block(nBody, tpt))
          instrumentation = pForbidden
          res
        case Apply(Select(term, TermName("$amp$amp")), List(Select(Ident(TermName(name)), TermName("isEmpty"))))
          if instrumentation(name) => transform(term)
        case Apply(Select(Select(Ident(TermName(name)), TermName("isEmpty")), TermName("$amp$amp")), List(term))
          if instrumentation(name) => transform(term)
        case Apply(Select(term, TermName("$bar$bar")), List(Select(Ident(TermName(name)), TermName("nonEmpty"))))
          if instrumentation(name) => transform(term)
        case Apply(Select(Select(Ident(TermName(name)), TermName("nonEmpty")), TermName("$bar$bar")), List(term))
          if instrumentation(name) => transform(term)
        case Apply(fun, args) =>
          val nArgs = args.filterNot {
            case Ident(TermName(name)) => instrumentation(name)
            case AssignOrNamedArg(_, Ident(TermName(name))) => instrumentation(name)
            case _ => false
          }
          super.transform(Apply(fun, nArgs))
        case TermName(name) if instrumentation(name) =>
          c.abort(c.enclosingPosition, s"There is a not cut forbidden name $name.")
        case _ => super.transform(tree)
      }
    }

    def containsInstumetationTool(v: ValDef): Boolean = v match {
      case ValDef(_, TermName(name), _, _) => name == parameter
      case _ => false
    }

    @inline def generateNonInstrumented(method: DefDef): DefDef = method match {
      case DefDef(mods, name, types, args, tpt, rhs) =>
        val nArgs = args.map(_ filterNot containsInstumetationTool)
        val nRhs = nonInstrumentedTransformer().transform(rhs)
        DefDef(mods, name, types, nArgs, tpt, nRhs)
    }

    @inline def genetateInstrumented(method: DefDef): DefDef = method match {
      case DefDef(mods, TermName(name), types, args, tpt, rhs) =>
        val nName = name + "$I"
        val nRhs = instrumentedTransformer().transform(rhs)
        DefDef(mods, TermName(nName), types, args, tpt, nRhs)
    }

    @inline def generateNonInstrumentedClass(clazz: ClassDef): ClassDef = clazz match {
      case ClassDef(mods, name, targs, Template(parents, self, body)) =>
        val (iBody, instrumented) = prepareBlock(body, Set(parameter), remove = true, e = Some(parameter))
        val nBody = iBody.map(nonInstrumentedTransformer(instrumented).transform(_))
        ClassDef(mods, name, targs, Template(parents, self, nBody))
    }

    @inline def generateInstrumentedClass(clazz: ClassDef): ClassDef = clazz match {
      case ClassDef(mods, TypeName(name), targs, Template(parents, self, body)) =>
        val nName = name + "$I"
        val (_, instrumented) = prepareBlock(body, Set(parameter), remove = false, e = Some(parameter))
        val nBody = body.map(instrumentedTransformer(instrumented).transform(_))
        ClassDef(mods, TypeName(nName), targs, Template(parents, self, nBody))
    }

    val inputs = annottees.map(_.tree).toList
    val (annottee, expandees) = inputs match {
      case (func: DefDef) :: rest => // method case
        val nonIntrumented = generateNonInstrumented(func)
        val instrumented = genetateInstrumented(func)
        println(nonIntrumented)
        println(showRaw(nonIntrumented))
        (func, nonIntrumented :: instrumented :: rest)
      case (clazz: ClassDef) :: rest =>
        val nonIstrumented = generateNonInstrumentedClass(clazz)
        val instrumented = generateInstrumentedClass(clazz)
        println(nonIstrumented)
        println(showRaw(nonIstrumented))
        (clazz, nonIstrumented :: instrumented :: rest)
      case (param: ValDef) :: (rest @ (_ :: _)) => (param, rest)
      case (param: TypeDef) :: (rest @ (_ :: _)) => (param, rest)
      case _ => (EmptyTree, inputs)
    }

    c.Expr[Any](Block(expandees, Literal(Constant(()))))
  }
}

@compileTimeOnly("enable macro paradise to expand macro annotations")
class identity extends StaticAnnotation {
  def macroTransform(annottees: Any*): Any = macro identityMacro.impl
}

object identityMacro {
  def impl(c: Context)(annottees: c.Expr[Any]*): c.Expr[Any] = {
    import c.universe._
    implicit val x: c.type = c

    val inputs = annottees.map(_.tree).toList
    val (annottee, expandees) = inputs match {
      case (param: ValDef) :: (rest @ (_ :: _)) => (param, rest)
      case (param: TypeDef) :: (rest @ (_ :: _)) => (param, rest)
      case _ => (EmptyTree, inputs)
    }
    println((annottee, expandees))
    val outputs = expandees
    c.Expr[Any](Block(outputs, Literal(Constant(()))))
  }
}


