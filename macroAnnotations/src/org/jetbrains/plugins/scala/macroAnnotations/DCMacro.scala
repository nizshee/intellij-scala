package org.jetbrains.plugins.scala.macroAnnotations

import scala.annotation.{StaticAnnotation, compileTimeOnly}
import scala.collection.immutable.{::, Nil}
import scala.language.experimental.macros
import scala.reflect.macros.whitebox.Context


@compileTimeOnly("generate two methods / classes")
class uninstrumental(parameterName: String, debug: Boolean = false) extends StaticAnnotation {
  def macroTransform(annottees: Any*): Any = macro generateInstrumentationMacro.impl
}

/** bugs:
  *   - multiple constructors
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
    *
    * Class super calls, no constructors, no init
    */
  def impl(c: Context)(annottees: c.Expr[Any]*): c.Expr[Any] = {
    import c.universe._

    val (parameter, debug) = c.prefix match {
      case Expr(q"new uninstrumental($s)") => (c.eval[String](c.Expr(s)), false)
      case Expr(q"new uninstrumental($s, debug = $b)") => (c.eval[String](c.Expr(s)), c.eval[Boolean](c.Expr(b)))
      case _ => c.abort(c.enclosingPosition, "No parameter name was given!")
    }

    implicit class ModifiersUtil(modifiers: Modifiers) {
      def addFlag(flagSet: FlagSet): Modifiers = modifiers match {
        case Modifiers(flags, name, annotations) =>
          Modifiers(flags | flagSet, name, annotations)
      }

      def removeFlag(flagSet: FlagSet): Modifiers = modifiers match {
        case Modifiers(flags, name, annotations) =>
          val nFlags = (flags.asInstanceOf[Long] & (flagSet.asInstanceOf[Long] ^ -1L)).asInstanceOf[FlagSet]
          Modifiers(nFlags, name, annotations)
      }
    }

    val fixImplicitBug = new Transformer {
      override def transform(tree: c.universe.Tree): c.universe.Tree = tree match {
        case ValDef(mods, name, tpt, rhs) if mods.hasFlag(Flag.PARAMACCESSOR) && mods.hasFlag(Flag.CASEACCESSOR) && mods.hasFlag(Flag.IMPLICIT) =>
          ValDef(mods.removeFlag(Flag.CASEACCESSOR), name, tpt, rhs)
        case _ => super.transform(tree)
      }
    }

    def superMethods(clazz: ClassDef) = clazz match {
      case ClassDef(_, _, _, Template(_, _, body)) =>

        var methods: Map[(String, List[List[ValDef]]), DefDef] = Map.empty // Set not works

        def transformer(current: Option[DefDef]) = new Transformer {

          override def transform(tree: c.universe.Tree): c.universe.Tree = tree match {
            case s@Select(Super(This(TypeName("")), TypeName("")), TermName(method)) =>
              current match {
                case Some(DefDef(_, TermName(mName), targs, args, tpt, _)) if mName == method =>
                  val nRhs = args.foldLeft[Tree](Select(Super(This(TypeName("")), TypeName("")), TermName(method))) { (prev, as) =>
                    val idents = as.map { case ValDef(_, TermName(n), _, _) =>  Ident(TermName(n)) }
                    Apply(prev, idents)
                  }
                  methods += (method, args) -> DefDef(Modifiers(Flag.PROTECTED), TermName(method + "$IS"), targs, args, tpt, nRhs)
                case _ if method == "<init>" =>
                case _ => c.abort(c.enclosingPosition, s"Super calls only in same method $s.")
              }
              s
            case Select(Super(This(TypeName(_)), TypeName(_)), TermName(_)) =>
              c.abort(c.enclosingPosition, s"Not handling general super calls.")
            case _ => super.transform(tree)
          }
        }

        body.foreach {
          case d@DefDef(mods, _, _, _, _, rhs) if mods.hasFlag(Flag.OVERRIDE) =>
            transformer(Some(d)).transform(rhs)
          case o =>
            transformer(None).transform(o)
        }

        methods.values.toSet
    }

    def parameterContainsInstrumentation(tree: Tree, instrumentation: Set[String]): Boolean =  tree match {
      case Ident(TermName(name)) => instrumentation(name)
      case AssignOrNamedArg(_, Ident(TermName(name))) => instrumentation(name)
      case Apply(Select(Ident(TermName(name)), _), _) => instrumentation(name)
      case AssignOrNamedArg(_, Apply(Select(Ident(TermName(name)), _), _)) => instrumentation(name)
      case _ => false
    }

    def trueExpression(instrumentation: Set[String], tree: Tree): Boolean = tree match {
      case Select(Ident(TermName(name)), TermName("isEmpty")) => instrumentation(name)
      case Apply(Select(Ident(TermName(name)), TermName("forall")), _) => instrumentation(name)
      case _ => false
    }

    def falseExpression(instrumentation: Set[String], tree: Tree): Boolean = tree match {
      case Select(Ident(TermName(name)), TermName("nonEmpty")) => instrumentation(name)
      case Apply(Select(Ident(TermName(name)), TermName("exists")), _) => instrumentation(name)
      case _ => false
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
        case ValDef(_, TermName(name), _, _) if isUpper =>
          val (nTail, nForbidden) = prepareBlock(tail, instrumentation, remove, isUpper)
          val nList = if (remove && instrumentation(name)) nTail else head :: nTail
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
        case Assign(Ident(TermName(name)), _) if instrumentation(name) =>
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
        case Apply(Select(term, TermName("$amp$amp")), List(maybeTrue)) if trueExpression(instrumentation, maybeTrue) =>
          transform(term)
        case Apply(Select(maybeTrue, TermName("$amp$amp")), List(term)) if trueExpression(instrumentation, maybeTrue) =>
          transform(term)
        case Apply(Select(term, TermName("$bar$bar")), List(maybeFalse)) if falseExpression(instrumentation, maybeFalse) =>
          transform(term)
        case Apply(Select(maybeFalse, TermName("$bar$bar")), List(term)) if falseExpression(instrumentation, maybeFalse) =>
          transform(term)
        case Apply(Select(Ident(TermName(name)), _), _) if instrumentation(name) => Literal(Constant(()))
        case a@Apply(fun, args) if a != pendingSuperCall => // pendingSuperCall matches on Apply and ruins final ast
          val nArgs = args.filterNot(parameterContainsInstrumentation(_, instrumentation))
          super.transform(Apply(fun, nArgs))
        case If(maybeTrue, tr, _) if trueExpression(instrumentation, maybeTrue) => transform(tr)
        case If(maybeFalse, _, tr) if falseExpression(instrumentation, maybeFalse) => transform(tr)
        case TermName(name) if instrumentation(name) =>
          c.abort(c.enclosingPosition, s"There is a not cut forbidden name $name.")
        case _ => super.transform(tree)
      }
    }

    def instrumentedTransformer(init: Set[String] = Set(parameter), clazz: Option[String]) = new Transformer {
      private var instrumentation = init
      private var _clazz: Option[String] = clazz

      override def transform(tree: c.universe.Tree): c.universe.Tree = tree match {
        case Apply(Select(New(Ident(TypeName(cName))), TermName("<init>")), args) => // TODO merge?
          val contains = args.exists {
            case Ident(TermName(name)) => instrumentation(name)
            case AssignOrNamedArg(_, Ident(TermName(name))) => instrumentation(name)
            case _ => false
          }
          val nName = if (contains) Select(Ident(TermName(cName)), TypeName("$I")) else Ident(TypeName(cName))
          val nArgs = if (contains) args.map {
            case AssignOrNamedArg(Ident(TermName(n)), r) => AssignOrNamedArg(Ident(TermName(n + "$I")), r)
            case o => o
          } else args
          super.transform(Apply(Select(New(nName), TermName("<init>")), nArgs))
        case f@DefDef(_, _, _, args, _, _) =>
          val names = args.flatMap(_.collect { case ValDef(_, TermName(name), _, _) => name }).toSet
          val permitted = instrumentation.intersect(names)
          instrumentation --= permitted
          val res = super.transform(f)
          instrumentation ++= permitted
          res
        case c@ClassDef(_, TypeName(name), _, Template(p, _, body)) =>
          val (_, nForbidden) = prepareBlock(body, instrumentation, remove = false, isUpper = false)
          val pForbidden = instrumentation
          val pClazz = _clazz
          instrumentation = nForbidden
          _clazz = Some(name)
          val res = super.transform(c)
          _clazz = pClazz
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
          val contains = args.exists(parameterContainsInstrumentation(_, instrumentation))
          var isClass = false
          val nName =
            if (contains) tName match {
              case Ident(TermName(n)) =>
                if (n.headOption.exists(_.isUpper)) { // hack but how else?
                  isClass = true
                  Select(Ident(TermName(n)), TermName("$I"))
                }
                else Ident(TermName(n + "$I"))
              case Ident(TypeName(n)) =>
                isClass = true
                Select(Ident(TermName(n)), TypeName("$I"))
              case Select(q, TermName(n)) =>
                if (n.headOption.exists(_.isUpper)) { // hack but how else?
                  isClass = true
                  Select(Select(q, TermName(n)), TypeName("$I"))
                }
                else Select(q, TermName(n + "$I"))
              case Select(q, TypeName(n)) =>
                isClass = true
                Select(Select(q, TermName(n)), TypeName("$I"))
            } else tName
          val nArgs = if (contains && isClass) args.map {
            case AssignOrNamedArg(Ident(TermName(n)), r) => AssignOrNamedArg(Ident(TermName(n + "$I")), r)
            case o => o
          } else args
          super.transform(Apply(nName, nArgs))
        case Select(Super(This(TypeName("")), TypeName("")), TermName(method)) if _clazz.exists(_.endsWith("$I")) =>
          Ident(TermName(method + "$IS"))
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
        val nRhs = instrumentedTransformer(clazz = None).transform(rhs)
        DefDef(mods, TermName(nName), types, args, tpt, nRhs)
    }

    @inline def generateInstrumentedClass(clazz: ClassDef, constructorArgs: Option[List[List[ValDef]]]): ClassDef = clazz match {
      case ClassDef(mods, TypeName(name), targs, Template(_, self, body)) =>
        val notOnlyFieldsAndMethods = body.exists {
          case ValDef(ms, _, _, _) => !ms.hasFlag(Flag.PARAMACCESSOR) && !ms.hasFlag(Flag.PRIVATE)
          case DefDef(_, _, _, _, _, _) => false
          case ClassDef(_, _, _, _) => false
          case _ => true
        }

        if (notOnlyFieldsAndMethods)
          c.abort(c.enclosingPosition, s"Classes with only parameter values / variables, inner classes and methods can use this annotation.")

        val parent = constructorArgs match {
          case Some(args) =>
            args.foldLeft[Tree](Ident(TypeName(name))) { (prev, as) =>
              val idents = as.map { case ValDef(_, TermName(n), _, _) =>  Ident(TermName(n + "$I")) }
              Apply(prev, idents)
            }
          case None => Ident(TypeName(name))
        }
        val (iBody, instrumented) = prepareBlock(body, Set(parameter), remove = false, isUpper = true)
        val iiBody = iBody.flatMap {
          case ValDef(ms, TermName(n), tpt, rhs) if !ms.hasFlag(Flag.PARAMACCESSOR) && ms.hasFlag(Flag.PRIVATE) =>
            Seq(ValDef(ms, TermName(n), tpt, rhs))
          case ValDef(ms, TermName(n), tpt, rhs) if ms.hasFlag(Flag.PRIVATE) || instrumented(n) =>
            val nVal = ValDef(ms.removeFlag(Flag.CASEACCESSOR | Flag.IMPLICIT), TermName(n + "$I"), tpt, rhs)
            val oVal = ValDef(ms.removeFlag(Flag.CASEACCESSOR | Flag.PARAMACCESSOR), TermName(n), tpt, Ident(TermName(n + "$I")))
            Seq(nVal, oVal)
          case ValDef(ms, TermName(n), tpt, rhs) =>
            Seq(ValDef(ms.removeFlag(Flag.CASEACCESSOR | Flag.OVERRIDE), TermName(n + "$I"), tpt, rhs))
          case DefDef(ms, TermName("<init>"), targs, args, tpt, cBody) if cBody.exists(_ == pendingSuperCall) =>
            val nArgs = args.map(_.map { case ValDef(ms, TermName(n), tpt, rhs) => ValDef(ms, TermName(n + "$I"), tpt, rhs) })
            Seq(DefDef(ms, TermName("<init>"), targs, nArgs, tpt, cBody))
          case DefDef(ms, n, targs, args, tpt, body) if !ms.hasFlag(Flag.PRIVATE) =>
            Seq(DefDef(ms.addFlag(Flag.OVERRIDE), n, targs, args, tpt, body))
          case o => Seq(o)
        }

        val nBody = iiBody.map(instrumentedTransformer(instrumented, Some("$I")).transform(_))
        ClassDef(mods.removeFlag(Flag.CASE | Flag.PRIVATE | Flag.PROTECTED), TypeName("$I"), targs, Template(List(parent), self, nBody))
    }

    @inline def generateNonInstrumentedClass(clazz: ClassDef, rest: List[Tree]): (ClassDef, List[Tree]) = clazz match {
      case ClassDef(mods, TypeName(name), targs, Template(parents, self, body)) =>
        val (iBody, instrumented) = prepareBlock(body, Set(parameter), remove = true, isUpper = true)
        val nBody = iBody.map(nonInstrumentedTransformer(instrumented).transform(_))
        val constrArgs = nBody.collectFirst {
          case DefDef(_, TermName("<init>"), _, as, _, cBody) if cBody.exists(_ == pendingSuperCall) => as
        }
        val instrumentedClass = generateInstrumentedClass(clazz, constrArgs)
        val constructorFunction = if (mods.hasFlag(Flag.CASE)) {
          body.collectFirst {
            case DefDef(_, TermName("<init>"), targs, args, tpt, cBody) if cBody.exists(_ == pendingSuperCall) =>
              val nBody = args.foldLeft[Tree](Select(New(Ident(TypeName("$I"))), TermName("<init>"))) { (prev, as) =>
                val idents = as.map { case ValDef(_, TermName(n), _, _) =>  Ident(TermName(n + "$I")) }
                Apply(prev, idents)
              }
              val nArgs = args.map(_.map {
                case ValDef(ms, TermName(n), tpt, rhs) => ValDef(ms, TermName(n + "$I"), tpt, rhs)
              })
              DefDef(Modifiers(), TermName("$I"), targs, nArgs, tpt, nBody)
          }
        } else None
        val compainion = rest match {
          case ModuleDef(cMods, TermName(cName), Template(cParents, cSelf, cBody)) :: tail =>
            val companion = ModuleDef(cMods, TermName(cName), Template(cParents, cSelf, (cBody :+ instrumentedClass) ++ constructorFunction))
            companion :: tail
          case _ => constructorFunction match {
            case Some(f) => q"object ${TermName(name)} { $instrumentedClass; $f }" :: rest
            case None => q"object ${TermName(name)} { $instrumentedClass }" :: rest
          }
        }
        val methods = superMethods(clazz)
        val nMods = if (mods.hasFlag(Flag.PRIVATE)) mods.removeFlag(Flag.PRIVATE).addFlag(Flag.PROTECTED) else mods
        ClassDef(nMods, TypeName(name), targs, Template(parents, self, nBody ++ methods)) -> compainion
    }


    val inputs = annottees.map(_.tree).toList
    val (annottee, expandees) = inputs match {
      case (func: DefDef) :: rest =>
        val nonIntrumented = generateNonInstrumented(func)
        val instrumented = genetateInstrumented(func)
        (func, nonIntrumented :: instrumented :: rest)
      case (clazz: ClassDef) :: rest =>
        val fixedClass = fixImplicitBug.transform(clazz).asInstanceOf[ClassDef]
        val (nonIstrumented, nRest) = generateNonInstrumentedClass(fixedClass, rest)
        (fixedClass, nonIstrumented :: nRest)
      case _ => (EmptyTree, inputs)
    }

    if (debug) {
//      println(annottee)
//      expandees.foreach(println)
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


