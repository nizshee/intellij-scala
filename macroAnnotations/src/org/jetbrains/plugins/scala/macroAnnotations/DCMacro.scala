package org.jetbrains.plugins.scala.macroAnnotations

import java.io.PrintWriter

import scala.annotation.{StaticAnnotation, compileTimeOnly}
import scala.collection.immutable.{::, Nil}
import scala.language.experimental.macros
import scala.reflect.macros.whitebox.Context


@compileTimeOnly("generate two methods / classes")
class uninstrumental(parameterName: String) extends StaticAnnotation {
  def macroTransform(annottees: Any*): Any = macro generateInstrumentationMacro.impl
}

/** bugs:
  *   - multiple constructors
  */
object generateInstrumentationMacro {

  private def printToFile(s: String) = new PrintWriter("tmpFile") { write(s); close() }

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

    def substitution(prev: String, next: String) = new Transformer {
      private def containsShadow(body: List[Tree]): Boolean = body.exists {
        case ValDef(_, TermName(name), _, _) => name == prev
        case DefDef(_, TermName(name), _, _, _, _) => name == prev
        case _ => false
      }

      override def transform(tree: c.universe.Tree): c.universe.Tree = tree match {
        case Ident(TermName(name)) if name == prev => Ident(TermName(next))
        case d@DefDef(_, _, _, args, _, _) =>
          if (args.exists(_.exists { case ValDef(_, TermName(name), _, _) => name == prev })) d
          else super.transform(d)
        case b@Block(body, _) =>
          if (containsShadow(body)) b
          else super.transform(b)
        case c@ClassDef(_, _, _, Template(_, _, body)) if !containsShadow(body) =>
          if (containsShadow(body)) c
          else super.transform(c)
        case _ => super.transform(tree)
      }
    }

    /**
      * This method looks fresh nad instrumentated variables up to down.
      * It is not correct sometimes but much easier.
      */
    def prepareBlock(body: List[Tree], instrumentation: Set[String], remove: Boolean, isUpper: Boolean): (List[Tree], Set[String]) = body match {
      case Nil => (Nil, instrumentation) // TODO maybe not work in inner classes and we should permiss names
      case head :: tail => head match {
        case ValDef(mods, TermName(name), tpt, rhs) if isUpper =>
          val nMods = if (remove) mods else mods match {
            case Modifiers(flags, n, annotations) =>
              var nFlags = flags
              if (!mods.hasFlag(Flag.PRIVATE) && !mods.hasFlag(Flag.MUTABLE)) nFlags |= Flag.OVERRIDE
              nFlags |= (nFlags.asInstanceOf[Long] & ((1L << 1) ^ -1L)).asInstanceOf[FlagSet] // very bad - remove case
              Modifiers(nFlags, n, annotations)
          }
          val nVal = ValDef(nMods, TermName(name), tpt, rhs)
          val (nTail, nForbidden) = prepareBlock(tail, instrumentation, remove, isUpper)
          val nList = if (remove && instrumentation(name)) nTail else nVal :: nTail
          (nList, nForbidden)
        case ValDef(_, TermName(name), _, Apply(Select(Ident(TermName(fName)), TermName(_)), _)) if instrumentation(fName) =>
          val (nTail, nForbidden) = prepareBlock(tail, instrumentation + name, remove, isUpper)
          val list = if (remove) nTail else head :: nTail
          (list, nForbidden)
        case ValDef(_, TermName(name), _, _) =>
          val (nTail, nForbidden) = prepareBlock(tail, instrumentation - name, remove, isUpper)
          (head :: nTail, nForbidden)
        case Apply(Select(Ident(TermName(name)), TermName(_)), _) if instrumentation(name) =>
          val (nTail, nForbidden) = prepareBlock(tail, instrumentation, remove, isUpper)
          val list = if (remove) nTail else head :: nTail
          (list, nForbidden)
        case _ =>
          val (nTail, nForbidden) = prepareBlock(tail, instrumentation, remove, isUpper)
          (head :: nTail, nForbidden)
      }

    }

    def nonInstrumentedTransformer(init: Set[String] = Set(parameter)) = new Transformer {
      private var instrumentation = init

      override def transform(tree: c.universe.Tree): c.universe.Tree = tree match {
        case DefDef(mods, TermName("<init>"), targs, args, tpt, rhs) =>
          val nArgs = args.map(_.filterNot { case ValDef(_, TermName(name), _, _) => instrumentation(name) })
          super.transform(DefDef(mods, TermName("<init>"), targs, nArgs, tpt, rhs))
        case Apply(Ident(TermName("<init>")), args) =>
          val nArgs = args.filterNot {
            case Ident(TermName(name)) => instrumentation(name)
            case AssignOrNamedArg(Ident(TermName(name)), _) => instrumentation(name)
            case AssignOrNamedArg(_, Ident(TermName(name))) => instrumentation(name)
            case _ => false
          }
          super.transform(Apply(Ident(TermName("<init>")), nArgs))
        case f@DefDef(_, _, _, args, _, _) =>
          val names = args.flatMap(_.collect { case ValDef(_, TermName(name), _, _) => name }).toSet
          val permitted = instrumentation.intersect(names)
          instrumentation --= permitted
          val res = super.transform(f)
          instrumentation ++= permitted
          res
        case ClassDef(mods, name, targs, Template(parents, self, body)) =>
          val (nBody, nForbidden) = prepareBlock(body, instrumentation, remove = true, isUpper = false)
          val pForbidden = instrumentation
          instrumentation = nForbidden
          val res = super.transform(ClassDef(mods, name, targs, Template(parents, self, nBody)))
          instrumentation = pForbidden
          res
        case Block(body, tpt) =>
          val (nBody, nForbidden) = prepareBlock(body, instrumentation, remove = true, isUpper = false)
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
        case a@Apply(fun, args) if a != pendingSuperCall => // pendingSuperCall matches on Apply and ruins final ast
          val nArgs = args.filterNot {
            case Ident(TermName(name)) => instrumentation(name)
            case AssignOrNamedArg(_, Ident(TermName(name))) => instrumentation(name)
            case _ => false
          }
          super.transform(Apply(fun, nArgs))
        case Apply(TermName(name), _) if instrumentation(name) => EmptyTree
        case TermName(name) if instrumentation(name) =>
          c.abort(c.enclosingPosition, s"There is a not cut forbidden name $name.")
        case _ => super.transform(tree)
      }
    }

    def instrumentedTransformer(init: Set[String] = Set(parameter)) = new Transformer {
      private var instrumentation = init

      override def transform(tree: c.universe.Tree): c.universe.Tree = tree match {
        case Apply(Select(New(Ident(TypeName(cName))), TermName("<init>")), args) =>
          val contains = args.exists {
            case Ident(TermName(name)) => instrumentation(name)
            case AssignOrNamedArg(_, Ident(TermName(name))) => instrumentation(name)
            case _ => false
          }
          val nName = if (contains) cName + ".$I" else cName
          super.transform(Apply(Select(New(Ident(TypeName(nName))), TermName("<init>")), args))
        case f@DefDef(_, _, _, args, _, _) =>
          val names = args.flatMap(_.collect { case ValDef(_, TermName(name), _, _) => name }).toSet
          val permitted = instrumentation.intersect(names)
          instrumentation --= permitted
          val res = super.transform(f)
          instrumentation ++= permitted
          res
        case c@ClassDef(_, _, _, Template(p, _, body)) =>
          val (_, nForbidden) = prepareBlock(body, instrumentation, remove = false, isUpper = false)
          val pForbidden = instrumentation
          instrumentation = nForbidden
          val res = super.transform(c)
          instrumentation = pForbidden
          res
        case b@Block(body, _) =>
          val (_, nForbidden) = prepareBlock(body, instrumentation, remove = false, isUpper = false)
          val pForbidden = instrumentation
          instrumentation = nForbidden
          val res = super.transform(b)
          instrumentation = pForbidden
          res
        case a@Apply(tName, args) if a != pendingSuperCall =>
          val contains = args.exists {
            case Ident(TermName(name)) => instrumentation(name)
            case AssignOrNamedArg(_, Ident(TermName(name))) => instrumentation(name)
            case _ => false
          }
          val nName =
            if (contains) tName match {
              case Ident(TermName(n)) => Ident(TermName(n + "$I"))
              case Ident(TypeName(n)) => Select(Ident(TermName(n)), TypeName("$I"))
              case Select(q, TermName(n)) => Select(q, TermName(n + "$I"))
              case Select(q, TypeName(n)) => Select(Select(q, TermName(n)), TypeName("$I"))
            } else tName
          super.transform(Apply(nName, args))
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

    @inline def generateInstrumentedClass(clazz: ClassDef, constructorArgs: Option[List[List[ValDef]]]): ClassDef = clazz match {
      case ClassDef(mods, TypeName(name), targs, Template(parents, self, body)) =>
        println(showRaw(parents))
        var substitutions = Map.empty[String, String]
        val iBody = body.map {
          case ValDef(ms, TermName(n), tpt, rhs) if ms.hasFlag(Flag.PARAMACCESSOR) => ValDef(ms, TermName(n + "$I"), tpt, rhs)
          case DefDef(ms, TermName(n), tyargs, args, tpt, rhs) if  =>
//          case ValDef(ms, n, tpt, rhs) if ms.hasFlag(Flag.PRIVATE) && ms.hasFlag(Flag.MUTABLE) => EmptyTree
//          case ValDef(ms, n, tpt, rhs) if !ms.hasFlag(Flag.PRIVATE) =>
          case o => o
        }

        val parent = constructorArgs match {
          case Some(args) =>
            args.foldLeft[Tree](Ident(TypeName(name))) { (prev, as) =>
              val idents = as.map { case ValDef(_, TermName(n), _, _) =>  Ident(TermName(n + "$I")) }
              Apply(prev, idents)
            }
          case None => Ident(TypeName(name))
        }
        val (iiBody, instrumented) = prepareBlock(body, Set(parameter), remove = false, isUpper = true)
        val nBody = iiBody.map(instrumentedTransformer(instrumented).transform(_))
        ClassDef(mods, TypeName("$I"), targs, Template(List(parent), self, nBody))
    }

    @inline def generateNonInstrumentedClass(clazz: ClassDef, rest: List[Tree]): (ClassDef, List[Tree]) = clazz match {
      case ClassDef(mods, TypeName(name), targs, Template(parents, self, body)) =>
        val (iBody, instrumented) = prepareBlock(body, Set(parameter), remove = true, isUpper = true)
        val nBody = iBody.map(nonInstrumentedTransformer(instrumented).transform(_))
        val constructorArgs = nBody.collectFirst {
          case DefDef(_, TermName("<init>"), _, args, _, cBody) if cBody.exists(_ == pendingSuperCall) => args
        }
        val instrumentedClass = generateInstrumentedClass(clazz, constructorArgs)
        val compainion = rest match {
          case ModuleDef(cMods, TermName(cName), Template(cParents, cSelf, cBody)) :: tail =>
            val companion = ModuleDef(cMods, TermName(cName), Template(cParents, cSelf, cBody :+ instrumentedClass))
            companion :: tail
          case _ => q"object ${TermName(name)} { $instrumentedClass }" :: rest
        }
        ClassDef(mods, TypeName(name), targs, Template(parents, self, nBody)) -> compainion
    }


    val inputs = annottees.map(_.tree).toList
    val (annottee, expandees) = inputs match {
      case (func: DefDef) :: rest => // method case
        val nonIntrumented = generateNonInstrumented(func)
        val instrumented = genetateInstrumented(func)
//        println(show(func))
//        println(showRaw(nonIntrumented))
//        println(show(instrumented))
//        println(showRaw(instrumented))
        (func, nonIntrumented :: instrumented :: rest)
      case (clazz: ClassDef) :: rest =>
        val (nonIstrumented, nRest) = generateNonInstrumentedClass(clazz, rest)
        (clazz, nonIstrumented :: nRest)
      case _ => (EmptyTree, inputs)
    }

    println(annottee, expandees)

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
    println((annottee, expandees.map(showRaw(_))))
    val outputs = expandees
    c.Expr[Any](Block(outputs, Literal(Constant(()))))
  }
}


