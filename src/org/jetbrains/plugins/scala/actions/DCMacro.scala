package org.jetbrains.plugins.scala.actions

import scala.reflect.macros.whitebox.Context
import scala.language.experimental.macros
import scala.annotation.StaticAnnotation
import scala.annotation.compileTimeOnly


@compileTimeOnly("generate two methods / classes")
class uninstrumental(parameterName: String) extends StaticAnnotation {
  def macroTransform(annottees: Any*): Any = macro generateInstrumentationMacro.impl
}

object generateInstrumentationMacro {
  /**
    * Generate from annotated method `f` two methods `f` and `f$I`.
    * NonInstrumentated version `f` not contains constructions connected with Handler like:
    *   - arguments `parameterName: Option[DCHandler.???] = None`
    *   - applications like parameterName.foreach { _ => }
    * Instrumentated version
    */
  def impl(c: Context)(annottees: c.Expr[Any]*): c.Expr[Any] = {
    import c.universe._

    val parameter = c.prefix match {
      case Expr(q"new uninstrumental($s)") => c.eval[String](c.Expr(s))/*showRaw(s)*/
      case _ => c.abort(c.enclosingPosition, "No parameter name was given!")
    }

    val nameTransformer = new Transformer {
      var forbiddenNames = Set(parameter)
//      var p = false

      override def transform(tree: c.universe.Tree): c.universe.Tree = tree match {
        case m@ModuleDef(_, _, Template(_, _, body)) => // find fields
          super.transform(m)
        case c@ClassDef(_, _, _, Template(_, _, body)) => // find construcor and fields
          super.transform(c)
        case b@Block(parameters) => // find definitions and remove
          println(parameters)
          super.transform(b)
        case a@Apply(Select(Ident(TermName(name)), TermName(_)), _) if forbiddenNames(name) =>
          EmptyTree
        case _ =>
          super.transform(tree)
      }
    }

    def containsInstumetationTool(v: ValDef): Boolean = v match {
      case ValDef(_, TermName(name), _, _) =>
        name == parameter
      case _ => false
    }

    @inline def generateNonInstrumentated(method: DefDef): DefDef = method match {
      case DefDef(mods, name, types, args, tpt, rhs) =>
        val nArgs = args.map(_ filterNot containsInstumetationTool)
        val nRhs = nameTransformer.transform(rhs)
        DefDef(mods, name, types, nArgs, tpt, nRhs)
    }

    @inline def genetateInstrumented(method: DefDef): DefDef = method match {
      case DefDef(mods, TermName(name), types, args, tpt, rhs) =>
        val nName = name + "$I"
        DefDef(mods, TermName(nName), types, args, tpt, rhs)
    }

    val inputs = annottees.map(_.tree).toList
    val (annottee, expandees) = inputs match {
      case (func: DefDef) :: rest => // method case
        val nonIntrumentated = generateNonInstrumentated(func)
        val instrumented = genetateInstrumented(func)
        println(nonIntrumentated)
        println(showRaw(nonIntrumentated))
        (func, nonIntrumentated :: instrumented :: rest)
      case (param: ValDef) :: (rest @ (_ :: _)) => (param, rest)
      case (param: TypeDef) :: (rest @ (_ :: _)) => (param, rest)
      case _ => (EmptyTree, inputs)
    }

    println(annottee, expandees)
    println("it is done")
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


