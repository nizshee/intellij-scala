package org.jetbrains.plugins.scala
package lang
package psi
package types

import com.intellij.openapi.progress.ProgressManager
import com.intellij.openapi.util.Computable
import com.intellij.psi._
import org.jetbrains.plugins.scala.actions.DebugConformanceAction
import org.jetbrains.plugins.scala.decompiler.DecompilerUtil
import org.jetbrains.plugins.scala.extensions._
import org.jetbrains.plugins.scala.lang.psi.ScalaPsiUtil._
import org.jetbrains.plugins.scala.lang.psi.api.base.ScFieldId
import org.jetbrains.plugins.scala.lang.psi.api.base.patterns.ScBindingPattern
import org.jetbrains.plugins.scala.lang.psi.api.statements._
import org.jetbrains.plugins.scala.lang.psi.api.statements.params._
import org.jetbrains.plugins.scala.lang.psi.api.toplevel.ScTypeParametersOwner
import org.jetbrains.plugins.scala.lang.psi.api.toplevel.typedef.ScTypeDefinition
import org.jetbrains.plugins.scala.lang.psi.impl.ScalaPsiElementFactory.createTypeParameterFromText
import org.jetbrains.plugins.scala.lang.psi.impl.toplevel.synthetic.ScSyntheticClass
import org.jetbrains.plugins.scala.lang.psi.types.api._
import org.jetbrains.plugins.scala.lang.psi.types.api.designator.{ScDesignatorType, ScProjectionType, ScThisType}
import org.jetbrains.plugins.scala.lang.psi.types.nonvalue.{ScMethodType, ScTypePolymorphicType}
import org.jetbrains.plugins.scala.lang.psi.types.result.{Success, Typeable, TypingContext}
import org.jetbrains.plugins.scala.lang.refactoring.util.ScTypeUtil.AliasType
import org.jetbrains.plugins.scala.lang.resolve.processor.{CompoundTypeCheckSignatureProcessor, CompoundTypeCheckTypeAliasProcessor}
import org.jetbrains.plugins.scala.util.ScEquivalenceUtil._

import _root_.scala.collection.immutable.HashSet
import scala.annotation.tailrec
import scala.collection.mutable.ArrayBuffer
import scala.collection.{Seq, immutable, mutable}

object Conformance extends api.Conformance {
  override implicit lazy val typeSystem = ScalaTypeSystem


  override protected def computable(left: ScType, right: ScType, visited: Set[PsiClass], checkWeak: Boolean, handler: Option[DebugConformanceAction.Handler]) =
    new Computable[(Boolean, ScUndefinedSubstitutor)] {
      override def compute(): (Boolean, ScUndefinedSubstitutor) = {
        val substitutor = ScUndefinedSubstitutor()
        val leftVisitor = new LeftConformanceVisitor(left, right, visited, substitutor, checkWeak, handler = handler)

        handler.foreach { h =>
          h.log("compute")
          h.logtn(left, right)
        }

        left.visitType(leftVisitor)
        if (leftVisitor.getResult != null) return leftVisitor.getResult

        handler.foreach { h =>
          h.log("visitor didn't get result")
          h.logn("check classes conformance")
        }

        //tail, based on class inheritance
        right.extractClassType() match {
          case Some((clazz: PsiClass, _)) if visited.contains(clazz) =>
            handler.foreach { h =>
              h.logn("right class was visited before")
            }
            return (false, substitutor)
          case Some((rClass: PsiClass, subst: ScSubstitutor)) =>
            left.extractClass(rClass.getProject) match {
              case Some(lClass) =>
                if (rClass.qualifiedName == "java.lang.Object") {
                  handler.foreach { h =>
                    h.logn("right equals Object, try to conformance AnyRef (HACK?)")
                  }
                  return conformsInner(left, AnyRef, visited, substitutor, checkWeak, handler = handler.map(_.inner))
                } else if (lClass.qualifiedName == "java.lang.Object") {
                  handler.foreach { h =>
                    h.logn("left equlas Object, try to conformance AnyRef (HACK?)")
                  }
                  return conformsInner(AnyRef, right, visited, substitutor, checkWeak, handler = handler.map(_.inner))
                }
                val inh = smartIsInheritor(rClass, subst, lClass)
                if (!inh._1) {
                  handler.foreach { h =>
                    h.logn("smartInheritor says not subclass")
                  }
                  return (false, substitutor)
                }
                val tp = inh._2
                handler.foreach { h =>
                  h.logn(s"expected type ${tp.presentableText}")
                }
                //Special case for higher kind types passed to generics.
                if (lClass.hasTypeParameters) {
                  left match {
                    case _: ScParameterizedType =>
                    case _ =>
                      handler.foreach { h =>
                        h.log("some strange case says that if left has type parameters, but is not ScParametrizedType")
                        h.logn("so it right can be cast to it (HACK?)")
                      }
                      return (true, substitutor)
                  }
                }
                val t = conformsInner(left, tp, visited + rClass, substitutor, checkWeak = false, handler = handler.map(_.inner))
                if (t._1) return (true, t._2)
                else return (false, substitutor)
              case _ =>
            }
          case _ =>
        }
        handler.foreach { h =>
          h.logn("second part of conformance if no PsiClassesWereFound")
        }
        val bases: Seq[ScType] = BaseTypes.get(right)
        val iterator = bases.iterator
        while (iterator.hasNext) {
          ProgressManager.checkCanceled()
          val tp = iterator.next()
          val t = conformsInner(left, tp, visited, substitutor, checkWeak = true, handler = handler.map(_.inner))
          if (t._1) return (true, t._2)
        }
        handler.foreach { h =>
          h.logn("not left <: right")
        }
        (false, substitutor)
      }
    }


  private def checkParameterizedType(parametersIterator: Iterator[PsiTypeParameter], args1: scala.Seq[ScType],
                                     args2: scala.Seq[ScType], _undefinedSubst: ScUndefinedSubstitutor,
                                     visited: Set[PsiClass], checkWeak: Boolean, handler: Option[DebugConformanceAction.Handler]): (Boolean, ScUndefinedSubstitutor) = {
    var undefinedSubst = _undefinedSubst

    handler.foreach { h =>
      h.log("checkParameterizedType")
    }

    // TODO how to fire; what means abstract if 'you cannot use this type to resolve generics'
    def addAbstract(upper: ScType, lower: ScType, tp: ScType, alternateTp: ScType): Boolean = {
      if (!upper.equiv(Any)) {
        handler.foreach { h =>
          h.log("try to conform tp to upper")
        }
        val t = conformsInner(upper, tp, visited, undefinedSubst, checkWeak, handler = handler.map(_.inner))
        if (!t._1) {
          handler.foreach { h =>
            h.log("not success, try to conform alternateTp to upper")
          }
          val t = conformsInner(upper, alternateTp, visited, undefinedSubst, checkWeak, handler = handler.map(_.inner))
          if (!t._1) {
            handler.foreach { h =>
              h.logn("can't satisfy upper bound")
            }
            return false
          }
          else undefinedSubst = t._2
        } else undefinedSubst = t._2
      }
      if (!lower.equiv(Nothing)) {
        handler.foreach { h =>
          h.log("try to conform tp to lower")
        }
        val t = conformsInner(tp, lower, visited, undefinedSubst, checkWeak, handler = handler.map(_.inner))
        if (!t._1) {
          handler.foreach { h =>
            h.log("not success, try to conform alternateTp to lower")
          }
          val t = conformsInner(alternateTp, lower, visited, undefinedSubst, checkWeak, handler = handler.map(_.inner))
          if (!t._1) {
            handler.foreach { h =>
              h.logn("can't satisfy lower bound")
            }
            return false
          }
          else undefinedSubst = t._2
        } else undefinedSubst = t._2
      }
      handler.foreach { h =>
        h.logn("satisfy")
      }
      true
    }

    val args1Iterator = args1.iterator
    val args2Iterator = args2.iterator

    while (parametersIterator.hasNext && args1Iterator.hasNext && args2Iterator.hasNext) {
      val tp = parametersIterator.next()
      val argsPair = (args1Iterator.next(), args2Iterator.next())
      handler.foreach { h =>
        h.log("check for arguments:")
        h.logtn(argsPair._1, argsPair._2)
      }
      tp match {
        case scp: ScTypeParam if scp.isContravariant =>
          handler.foreach { h =>
            h.log("parameter is contrvariant so try to confrom left to right")
          }
          val y = conformsInner(argsPair._2, argsPair._1, HashSet.empty, undefinedSubst, handler = handler.map(_.inner))
          if (!y._1) {
            handler.foreach { h =>
              h.logn("failure")
            }
            return (false, undefinedSubst)
          }
          else undefinedSubst = y._2

        case scp: ScTypeParam if scp.isCovariant =>
          handler.foreach { h =>
            h.log("parameter is covariant so try to confrom right to left")
          }
          val y = conformsInner(argsPair._1, argsPair._2, HashSet.empty, undefinedSubst, handler = handler.map(_.inner))
          if (!y._1) {
            handler.foreach { h =>
              h.logn("failure")
            }
            return (false, undefinedSubst)
          }
          else undefinedSubst = y._2
        //this case filter out such cases like undefined type
        case _ =>
          argsPair match {
            case (UndefinedType(parameterType, _), rt) =>
              handler.foreach { h =>
                h.log("left is underfinded, so try to add constraints") // TODO how to fire????
              }
              val y = addParam(parameterType, rt, undefinedSubst, args2, args1, handler)
              if (!y._1) {
                handler.foreach { h =>
                  h.logn("failure")
                }
                return (false, undefinedSubst)
              }
              undefinedSubst = y._2
            case (lt, UndefinedType(parameterType, _)) =>
              handler.foreach { h =>
                h.log("right is underfinded, so try to add constraints") // TODO how to fire????
              }
              val y = addParam(parameterType, lt, undefinedSubst, args1, args2, handler)
              if (!y._1) {
                handler.foreach { h =>
                  h.logn("failure")
                }
                return (false, undefinedSubst)
              }
              undefinedSubst = y._2
            case (ScAbstractType(tpt, lower, upper), r) =>
              handler.foreach { h =>
                h.logn("left is abstract, so ???") // TODO how to fire????
              }
              val (right, alternateRight) =
                if (tpt.arguments.nonEmpty && !r.isInstanceOf[ScParameterizedType])
                  (ScParameterizedType(r, tpt.arguments), r)
                else (r, r)
              if (!addAbstract(upper, lower, right, alternateRight)) return (false, undefinedSubst)
            case (l, ScAbstractType(tpt, lower, upper)) =>
              handler.foreach { h =>
                h.logn("right is abstract, so ???") // TODO how to fire????
              }
              val (left, alternateLeft) =
                if (tpt.arguments.nonEmpty && !l.isInstanceOf[ScParameterizedType])
                  (ScParameterizedType(l, tpt.arguments), l)
                else (l, l)
              if (!addAbstract(upper, lower, left, alternateLeft)) return (false, undefinedSubst)
            case _ =>
              handler.foreach { h =>
                h.log("check left and right equiv")
              }
              val t = argsPair._1.equiv(argsPair._2, undefinedSubst, falseUndef = false)
              if (!t._1) {
                handler.foreach { h =>
                  h.logn("failure")
                }
                return (false, undefinedSubst)
              }
              undefinedSubst = t._2
          }
      }
    }
    handler.foreach { h =>
      h.logn("return constrainsts")
    }
    (true, undefinedSubst)
  }

  private class LeftConformanceVisitor(l: ScType, r: ScType, visited: Set[PsiClass],
                                       subst: ScUndefinedSubstitutor,
                                       checkWeak: Boolean = false,
                                       handler: Option[DebugConformanceAction.Handler]) extends ScalaTypeVisitor {
    private def addBounds(parameterType: TypeParameterType, `type`: ScType) = {
      val name = parameterType.nameAndId
      undefinedSubst = undefinedSubst.addLower(name, `type`, variance = 0)
        .addUpper(name, `type`, variance = 0)
    }

    /*
      Different checks from right type in order of appearence.
      todo: It's seems it's possible to check order and simplify code in many places.
     */
    trait ValDesignatorSimplification extends ScalaTypeVisitor {
      override def visitDesignatorType(d: ScDesignatorType) {
        handler.foreach { h =>
          h.rvisit("ValDesignatorSimplification")
          h.log("it unpack std type and continue conformance with it")
        }
        d.getValType match {
          case Some(v) =>
            handler.foreach { h =>
              h.logn("success")
            }
            result = conformsInner(l, v, visited, subst, checkWeak, handler = handler.map(_.inner))
          case _ =>
            handler.foreach { h =>
              h.logn("failure")
            }
        }
      }
    }

    trait UndefinedSubstVisitor extends ScalaTypeVisitor {
      override def visitUndefinedType(u: UndefinedType) {
        handler.foreach { h =>
          h.rvisit("UndefinedSubstVisitor")
          h.log("it add upper constaint to parameter type")
        }
        result = (true, undefinedSubst.addUpper(u.parameterType.nameAndId, l))
      }
    }

    trait AbstractVisitor extends ScalaTypeVisitor { // TODO ???? check that left conforms to right
    override def visitAbstractType(a: ScAbstractType) {
      handler.foreach { h =>
        h.rvisit("AbstractVisitor")
      }
      val left =
        if (a.parameterType.arguments.nonEmpty && !l.isInstanceOf[ScParameterizedType]) {
          handler.foreach { h => // TODO ???? how to fire?
            h.log("type has type parameters, but left is not abstract") // TODO !l.isInstanceOf[ScParameterizedType] ???? not bad result
          }
          ScParameterizedType(l, a.parameterType.arguments)
        }
        else l
      if (!a.lower.equiv(Nothing)) {
        handler.foreach { h =>
          h.logn("check left conforms lower bound")
        }
        result = conformsInner(left, a.lower, visited, undefinedSubst, checkWeak, handler = handler.map(_.inner))
      } else {
        result = (true, undefinedSubst)
      }
      if (result._1 && !a.upper.equiv(Any)) {
        handler.foreach { h =>
          h.logn("check left conforms upper bound")
        }
        val t = conformsInner(a.upper, left, visited, result._2, checkWeak, handler = handler.map(_.inner))
        if (t._1) result = t //this is optionally
      }
    }
    }

    trait ParameterizedAbstractVisitor extends ScalaTypeVisitor { // TODO ???? if type is parametrized and abstract
    override def visitParameterizedType(p: ParameterizedType) { // TODO ???? it tries to conform deparametrized lower boud to left
      handler.foreach { h =>
        h.log(p.designator, p.typeArguments)
        h.rvisit("ParameterizedAbstractVisitor")
      }
      p.designator match {
        case ScAbstractType(parameterType, lowerBound, _) =>
          val subst = ScSubstitutor(parameterType.arguments.zip(p.typeArguments).map {
            case (tpt: TypeParameterType, tp: ScType) => (tpt.nameAndId, tp)
          }.toMap)
          val lower: ScType =
            subst.subst(lowerBound) match {
              case ParameterizedType(lower, _) => ScParameterizedType(lower, p.typeArguments)
              case lower => ScParameterizedType(lower, p.typeArguments)
            }
          if (!lower.equiv(Nothing)) {
            result = conformsInner(l, lower, visited, undefinedSubst, checkWeak, handler = handler.map(_.inner))
          }
        case _ =>
      }
    }
    }

    private def checkEquiv() {
      val isEquiv = l.equiv(r, undefinedSubst)
      if (isEquiv._1) result = isEquiv
    }

    trait ExistentialSimplification extends ScalaTypeVisitor { // TODO ???? simplifies existential
    override def visitExistentialType(e: ScExistentialType) {
      handler.foreach { h =>
        h.rvisit("ExistentialSimplification")
      }
      val simplified = e.simplify()
      if (simplified != r) result = conformsInner(l, simplified, visited, undefinedSubst, checkWeak, handler = handler.map(_.inner))
    }
    }

    trait ExistentialArgumentVisitor extends ScalaTypeVisitor {
      override def visitExistentialArgument(s: ScExistentialArgument): Unit = {
        handler.foreach { h =>
          h.rvisit("ExistentialArgumentVisitor")
        }
        result = conformsInner(l, s.upper, HashSet.empty, undefinedSubst, handler = handler.map(_.inner))
      }
    }

    trait ParameterizedExistentialArgumentVisitor extends ScalaTypeVisitor {
      override def visitParameterizedType(p: ParameterizedType) {
        handler.foreach { h =>
          h.rvisit("ParameterizedExistentialArgumentVisitor")
        }
        p.designator match {
          case s: ScExistentialArgument =>
            s.upper match {
              case ParameterizedType(upper, _) =>
                result = conformsInner(l, upper, visited, undefinedSubst, checkWeak, handler = handler.map(_.inner))
              case upper =>
                result = conformsInner(l, upper, visited, undefinedSubst, checkWeak, handler = handler.map(_.inner))
            }
          case _ =>
        }
      }
    }

    trait OtherNonvalueTypesVisitor extends ScalaTypeVisitor {
      override def visitUndefinedType(u: UndefinedType) {
        handler.foreach { h =>
          h.rvisit("OtherNonvalueTypes - undefined")
        }
        result = (false, undefinedSubst)
      }

      override def visitMethodType(m: ScMethodType) {
        handler.foreach { h =>
          h.rvisit("OtherNonvalueTypes - method")
        }
        result = (false, undefinedSubst)
      }

      override def visitAbstractType(a: ScAbstractType) {
        handler.foreach { h =>
          h.rvisit("OtherNonvalueTypes - abstract")
        }
        result = (false, undefinedSubst)
      }

      override def visitTypePolymorphicType(t: ScTypePolymorphicType) {
        handler.foreach { h =>
          h.rvisit("OtherNonvalueTypes - typePolymorphic")
        }
        result = (false, undefinedSubst)
      }
    }

    trait NothingNullVisitor extends ScalaTypeVisitor {
      override def visitStdType(x: StdType) {
        handler.foreach { h =>
          h.rvisit("NothingNullVisitor")
        }
        if (x eq Nothing) result = (true, undefinedSubst)
        else if (x eq Null) {
          /*
            this case for checking: val x: T = null
            This is good if T class type: T <: AnyRef and !(T <: NotNull)
           */
          if (!l.conforms(AnyRef)) {
            result = (false, undefinedSubst)
            return
          }
          l.extractDesignated(expandAliases = false) match {
            case Some(el) =>
              val flag = el.elementScope.getCachedClass("scala.NotNull")
                .map {
                  ScDesignatorType(_)
                }.exists {
                l.conforms(_)
              }
              result = (!flag, undefinedSubst) // todo: think about undefinedSubst
            case _ => result = (true, undefinedSubst)
          }
        }
      }
    }

    trait TypeParameterTypeVisitor extends ScalaTypeVisitor {
      override def visitTypeParameterType(tpt: TypeParameterType) {
        handler.foreach { h =>
          h.rvisit("TypeParameterTypeVisitor")
        }
        result = conformsInner(l, tpt.upperType.v, substitutor = undefinedSubst, handler = handler.map(_.inner))
      }
    }

    trait ThisVisitor extends ScalaTypeVisitor {
      override def visitThisType(t: ScThisType) {
        handler.foreach { h =>
          h.rvisit("ThisVisitor")
        }
        val clazz = t.element
        val res = clazz.getTypeWithProjections(TypingContext.empty)
        if (res.isEmpty) result = (false, undefinedSubst)
        else result = conformsInner(l, res.get, visited, subst, checkWeak, handler = handler.map(_.inner))
      }
    }

    trait DesignatorVisitor extends ScalaTypeVisitor {
      override def visitDesignatorType(d: ScDesignatorType) {
        handler.foreach { h =>
          h.rvisit("DesignatorVisitor")
        }
        d.element match {
          case v: ScBindingPattern =>
            val res = v.getType(TypingContext.empty)
            if (res.isEmpty) result = (false, undefinedSubst)
            else result = conformsInner(l, res.get, visited, undefinedSubst, handler = handler.map(_.inner))
          case v: ScParameter =>
            val res = v.getType(TypingContext.empty)
            if (res.isEmpty) result = (false, undefinedSubst)
            else result = conformsInner(l, res.get, visited, undefinedSubst, handler = handler.map(_.inner))
          case v: ScFieldId =>
            val res = v.getType(TypingContext.empty)
            if (res.isEmpty) result = (false, undefinedSubst)
            else result = conformsInner(l, res.get, visited, undefinedSubst, handler = handler.map(_.inner))
          case _ =>
        }
      }
    }

    trait ParameterizedAliasVisitor extends ScalaTypeVisitor {
      override def visitParameterizedType(p: ParameterizedType) {
        handler.foreach { h =>
          h.rvisit("ParameterizedAliasVisitor")
        }
        p.isAliasType match {
          case Some(AliasType(_, _, upper)) =>
            if (upper.isEmpty) {
              result = (false, undefinedSubst)
              return
            }
            result = conformsInner(l, upper.get, visited, undefinedSubst, handler = handler.map(_.inner))
          case _ =>
        }
      }
    }

    trait AliasDesignatorVisitor extends ScalaTypeVisitor {
      def stopDesignatorAliasOnFailure: Boolean = false

      override def visitDesignatorType(des: ScDesignatorType) {
        handler.foreach { h =>
          h.rvisit("AliasDesignatorVisitor")
        }
        des.isAliasType match {
          case Some(AliasType(_, _, upper)) =>
            if (upper.isEmpty) return
            val res = conformsInner(l, upper.get, visited, undefinedSubst, handler = handler.map(_.inner))
            if (stopDesignatorAliasOnFailure || res._1) result = res
          case _ =>
        }
      }
    }

    trait CompoundTypeVisitor extends ScalaTypeVisitor {
      override def visitCompoundType(c: ScCompoundType) {
        handler.foreach { h =>
          h.rvisit("CompoundTypeVisitor")
        }
        var comps = c.components.toList
        var results = List[ScUndefinedSubstitutor]()
        def traverse(check: (ScType, ScUndefinedSubstitutor) => (Boolean, ScUndefinedSubstitutor)) = {
          val iterator = comps.iterator
          while (iterator.hasNext) {
            val comp = iterator.next()
            val t = check(comp, undefinedSubst)
            if (t._1) {
              results = t._2 :: results
              comps = comps.filter(_ == comp)
            }
          }
        }
        traverse(Equivalence.equivInner(l, _, _))
        traverse(conformsInner(l, _, HashSet.empty, _, handler = handler.map(_.inner)))

        if (results.length == 1) {
          result = (true, results.head)
          return
        } else if (results.length > 1) {
          result = (true, ScUndefinedSubstitutor.multi(results.reverse))
          return
        }

        result = l.isAliasType match {
          case Some(AliasType(_: ScTypeAliasDefinition, Success(comp: ScCompoundType, _), _)) =>
            conformsInner(comp, c, HashSet.empty, undefinedSubst, handler = handler.map(_.inner))
          case _ => (false, undefinedSubst)
        }
      }
    }

    trait ExistentialVisitor extends ScalaTypeVisitor {
      override def visitExistentialType(ex: ScExistentialType) {
        handler.foreach { h =>
          h.rvisit("ExistentialVisitor")
        }
        result = conformsInner(l, ex.quantified, HashSet.empty, undefinedSubst, handler = handler.map(_.inner))
      }
    }

    trait ProjectionVisitor extends ScalaTypeVisitor {
      def stopProjectionAliasOnFailure: Boolean = false

      override def visitProjectionType(proj2: ScProjectionType) {
        handler.foreach { h =>
          h.rvisit("ProjectionVisitor")
        }
        proj2.isAliasType match {
          case Some(AliasType(_, _, upper)) =>
            if (upper.isEmpty) return
            val res = conformsInner(l, upper.get, visited, undefinedSubst, handler = handler.map(_.inner))
            if (stopProjectionAliasOnFailure || res._1) result = res
          case _ =>
            l match {
              case proj1: ScProjectionType if smartEquivalence(proj1.actualElement, proj2.actualElement) =>
                val projected1 = proj1.projected
                val projected2 = proj2.projected
                result = conformsInner(projected1, projected2, visited, undefinedSubst, handler = handler.map(_.inner))
              case param@ParameterizedType(projDes: ScProjectionType, _) =>
                //TODO this looks overcomplicated. Improve the code.
                def cutProj(p: ScType, acc: List[ScProjectionType]): ScType = {
                  if (acc.isEmpty) p else acc.foldLeft(p){
                    case (proj, oldProj) => ScProjectionType(proj, oldProj.element, oldProj.superReference)
                  }
                }
                @tailrec
                def findProjectionBase(proj: ScProjectionType, acc: List[ScProjectionType] = List()): Unit = {
                  val t = proj.projected.equiv(projDes.projected, undefinedSubst)
                  if (t._1) {
                    undefinedSubst = t._2
                    (projDes.actualElement, proj.actualElement) match {
                      case (desT: Typeable, projT: Typeable) =>
                        desT.getType(TypingContext.empty).filter(_.isInstanceOf[ScParameterizedType]).
                          map(_.asInstanceOf[ScParameterizedType]).flatMap(dt => projT.getType(TypingContext.empty).
                          map(c => conformsInner(ScParameterizedType(dt.designator, param.typeArguments),
                            cutProj(c, acc), visited, undefinedSubst, handler = handler))).map(t => if (t._1) result = t)
                      case _ =>
                    }
                  } else {
                    proj.projected match {
                      case p: ScProjectionType => findProjectionBase(p, proj :: acc)
                      case _ =>
                    }
                  }
                }
                findProjectionBase(proj2)
              case _ =>
                proj2.actualElement match {
                  case syntheticClass: ScSyntheticClass =>
                    result = conformsInner(l, syntheticClass.t, HashSet.empty, undefinedSubst, handler = handler.map(_.inner))
                  case v: ScBindingPattern =>
                    val res = v.getType(TypingContext.empty)
                    if (res.isEmpty) result = (false, undefinedSubst)
                    else result = conformsInner(l, proj2.actualSubst.subst(res.get), visited, undefinedSubst, handler = handler.map(_.inner))
                  case v: ScParameter =>
                    val res = v.getType(TypingContext.empty)
                    if (res.isEmpty) result = (false, undefinedSubst)
                    else result = conformsInner(l, proj2.actualSubst.subst(res.get), visited, undefinedSubst, handler = handler.map(_.inner))
                  case v: ScFieldId =>
                    val res = v.getType(TypingContext.empty)
                    if (res.isEmpty) result = (false, undefinedSubst)
                    else result = conformsInner(l, proj2.actualSubst.subst(res.get), visited, undefinedSubst, handler = handler.map(_.inner))
                  case _ =>
                }
            }
        }
      }
    }

    private var result: (Boolean, ScUndefinedSubstitutor) = null
    private var undefinedSubst: ScUndefinedSubstitutor = subst

    def getResult: (Boolean, ScUndefinedSubstitutor) = result

    override def visitStdType(x: StdType) {
      handler.foreach { h =>
        h.visit("visitStdType")
      }
      var rightVisitor: ScalaTypeVisitor =
        new ValDesignatorSimplification with UndefinedSubstVisitor
          with AbstractVisitor
          with ParameterizedAbstractVisitor {}
      r.visitType(rightVisitor)
      if (result != null) {
        handler.foreach { h =>
          h.logn("visitor found result")
        }
        return
      }

      checkEquiv()
      if (result != null) {
        handler.foreach { h =>
          h.logn("types are equivavalent")
        }
        return
      }

      rightVisitor = new ExistentialSimplification with ExistentialArgumentVisitor
        with ParameterizedExistentialArgumentVisitor with OtherNonvalueTypesVisitor {}
      r.visitType(rightVisitor)
      if (result != null) return

      if (checkWeak && r.isInstanceOf[ValType]) {
        (r, x) match {
          case (Byte, Short | Int | Long | Float | Double) =>
            result = (true, undefinedSubst)
            return
          case (Short, Int | Long | Float | Double) =>
            result = (true, undefinedSubst)
            return
          case (Char, Byte | Short | Int | Long | Float | Double) =>
            result = (true, undefinedSubst)
            return
          case (Int, Long | Float | Double) =>
            result = (true, undefinedSubst)
            return
          case (Long, Float | Double) =>
            result = (true, undefinedSubst)
            return
          case (Float, Double) =>
            result = (true, undefinedSubst)
            return
          case _ =>
        }
      }

      if (x eq Any) {
        result = (true, undefinedSubst)
        return
      }

      if (x == Nothing && r == Null) {
        result = (false, undefinedSubst)
        return
      }

      rightVisitor = new NothingNullVisitor with TypeParameterTypeVisitor {}
      r.visitType(rightVisitor)
      if (result != null) return

      rightVisitor = new ThisVisitor with DesignatorVisitor
        with ParameterizedAliasVisitor {}
      r.visitType(rightVisitor)
      if (result != null) return

      rightVisitor = new AliasDesignatorVisitor with CompoundTypeVisitor with ExistentialVisitor
        with ProjectionVisitor {}
      r.visitType(rightVisitor)
      if (result != null) return

      if (x eq Null) {
        result = (r == Nothing, undefinedSubst)
        return
      }

      if (x eq AnyRef) {
        if (r eq Any) {
          result = (false, undefinedSubst)
          return
        }
        else if (r eq AnyVal) {
          result = (false, undefinedSubst)
          return
        }
        else if (r.isInstanceOf[ValType]) {
          result = (false, undefinedSubst)
          return
        }
        else if (!r.isInstanceOf[ScExistentialType]) {
          rightVisitor = new AliasDesignatorVisitor with ProjectionVisitor {
            override def stopProjectionAliasOnFailure: Boolean = true

            override def stopDesignatorAliasOnFailure: Boolean = true
          }
          r.visitType(rightVisitor)
          if (result != null) return
          result = (true, undefinedSubst)
          return
        }
      }

      if (x eq Singleton) {
        result = (false, undefinedSubst)
      }

      if (x eq AnyVal) {
        result = (r.isInstanceOf[ValType] || ValueClassType.isValueType(r), undefinedSubst)
        return
      }
      if (l.isInstanceOf[ValType] && r.isInstanceOf[ValType]) {
        result = (false, undefinedSubst)
        return
      }
    }

    override def visitCompoundType(c: ScCompoundType) {
      handler.foreach { h =>
        h.visit("visitCompoundType")
      }
      var rightVisitor: ScalaTypeVisitor =
        new ValDesignatorSimplification with UndefinedSubstVisitor with AbstractVisitor
          with ParameterizedAbstractVisitor {}
      r.visitType(rightVisitor)
      if (result != null) return

      checkEquiv()
      if (result != null) return

      rightVisitor = new ExistentialSimplification with ExistentialArgumentVisitor
        with ParameterizedExistentialArgumentVisitor with OtherNonvalueTypesVisitor with NothingNullVisitor
        with TypeParameterTypeVisitor with ThisVisitor with DesignatorVisitor {}
      r.visitType(rightVisitor)
      if (result != null) return

      rightVisitor = new ParameterizedAliasVisitor with AliasDesignatorVisitor {}
      r.visitType(rightVisitor)
      if (result != null) return

      /*If T<:Ui for i=1,...,n and for every binding d of a type or value x in R there exists a member binding
      of x in T which subsumes d, then T conforms to the compound type	U1	with	. . .	with	Un	{R }.

      U1	with	. . .	with	Un	{R } === t1
      T                             === t2
      U1	with	. . .	with	Un       === comps1
      Un                            === compn*/
      def workWithSignature(s: Signature, retType: ScType): Boolean = {
        val processor = new CompoundTypeCheckSignatureProcessor(s,retType, undefinedSubst, s.substitutor)
        processor.processType(r, s.namedElement)
        undefinedSubst = processor.getUndefinedSubstitutor
        processor.getResult
      }

      def workWithTypeAlias(sign: TypeAliasSignature): Boolean = {
        val processor = new CompoundTypeCheckTypeAliasProcessor(sign, undefinedSubst, ScSubstitutor.empty)
        processor.processType(r, sign.ta)
        undefinedSubst = processor.getUndefinedSubstitutor
        processor.getResult
      }

      result = (c.components.forall(comp => {
        val t = conformsInner(comp, r, HashSet.empty, undefinedSubst, handler = handler.map(_.inner))
        undefinedSubst = t._2
        t._1
      }) && c.signatureMap.forall {
        case (s: Signature, retType) => workWithSignature(s, retType)
      } && c.typesMap.forall {
        case (_, sign) => workWithTypeAlias(sign)
      }, undefinedSubst)
    }

    override def visitProjectionType(proj: ScProjectionType) {
      handler.foreach { h =>
        h.visit("visitProjectionType")
      }
      var rightVisitor: ScalaTypeVisitor =
        new ValDesignatorSimplification with UndefinedSubstVisitor with AbstractVisitor
          with ParameterizedAbstractVisitor {}
      r.visitType(rightVisitor)
      if (result != null) return

      checkEquiv()
      if (result != null) return

      rightVisitor = new ExistentialSimplification with ExistentialArgumentVisitor
        with ParameterizedExistentialArgumentVisitor with OtherNonvalueTypesVisitor with NothingNullVisitor
        with TypeParameterTypeVisitor with ThisVisitor with DesignatorVisitor with ParameterizedAliasVisitor {}
      r.visitType(rightVisitor)
      if (result != null) return

      rightVisitor = new ParameterizedAliasVisitor with AliasDesignatorVisitor with CompoundTypeVisitor with ProjectionVisitor {}
      r.visitType(rightVisitor)
      if (result != null) return

      r match {
        case proj1: ScProjectionType if smartEquivalence(proj1.actualElement, proj.actualElement) =>
          val projected1 = proj.projected
          val projected2 = proj1.projected
          result = conformsInner(projected1, projected2, visited, undefinedSubst, handler = handler.map(_.inner))
          if (result != null) return
        case proj1: ScProjectionType if proj1.actualElement.name == proj.actualElement.name =>
          val projected1 = proj.projected
          val projected2 = proj1.projected
          val t = conformsInner(projected1, projected2, visited, undefinedSubst, handler = handler.map(_.inner))
          if (t._1) {
            result = t
            return
          }
        case _ =>
      }

      proj.isAliasType match {
        case Some(AliasType(_, lower, _)) =>
          if (lower.isEmpty) {
            result = (false, undefinedSubst)
            return
          }
          result = conformsInner(lower.get, r, visited, undefinedSubst, handler = handler.map(_.inner))
          return
        case _ =>
      }

      rightVisitor = new ExistentialVisitor {}
      r.visitType(rightVisitor)
      if (result != null) return
    }

    override def visitJavaArrayType(a1: JavaArrayType) {
      handler.foreach { h =>
        h.visit("visitJavaArrayType")
      }
      val JavaArrayType(arg1) = a1
      var rightVisitor: ScalaTypeVisitor =
        new ValDesignatorSimplification with UndefinedSubstVisitor with AbstractVisitor
          with ParameterizedAbstractVisitor {}
      r.visitType(rightVisitor)
      if (result != null) return

      checkEquiv()
      if (result != null) return

      rightVisitor = new ExistentialSimplification with ExistentialArgumentVisitor
        with ParameterizedExistentialArgumentVisitor with OtherNonvalueTypesVisitor with NothingNullVisitor
        with TypeParameterTypeVisitor with ThisVisitor with DesignatorVisitor {}
      r.visitType(rightVisitor)
      if (result != null) return

      rightVisitor = new ParameterizedAliasVisitor {}
      r.visitType(rightVisitor)
      if (result != null) return

      r match {
        case JavaArrayType(arg2) =>
          val argsPair = (arg1, arg2)
          argsPair match {
            case (ScAbstractType(tpt, lower, upper), r) =>
              val right =
                if (tpt.arguments.nonEmpty && !r.isInstanceOf[ScParameterizedType])
                  ScParameterizedType(r, tpt.arguments)
                else r
              if (!upper.equiv(Any)) {
                val t = conformsInner(upper, right, visited, undefinedSubst, checkWeak, handler = handler.map(_.inner))
                if (!t._1) {
                  result = (false, undefinedSubst)
                  return
                }
                undefinedSubst = t._2
              }
              if (!lower.equiv(Nothing)) {
                val t = conformsInner(right, lower, visited, undefinedSubst, checkWeak, handler = handler.map(_.inner))
                if (!t._1) {
                  result = (false, undefinedSubst)
                  return
                }
                undefinedSubst = t._2
              }
            case (l, ScAbstractType(tpt, lower, upper)) =>
              val left =
                if (tpt.arguments.nonEmpty && !l.isInstanceOf[ScParameterizedType])
                  ScParameterizedType(l, tpt.arguments)
                else l
              if (!upper.equiv(Any)) {
                val t = conformsInner(upper, left, visited, undefinedSubst, checkWeak, handler = handler.map(_.inner))
                if (!t._1) {
                  result = (false, undefinedSubst)
                  return
                }
                undefinedSubst = t._2
              }
              if (!lower.equiv(Nothing)) {
                val t = conformsInner(left, lower, visited, undefinedSubst, checkWeak, handler = handler.map(_.inner))
                if (!t._1) {
                  result = (false, undefinedSubst)
                  return
                }
                undefinedSubst = t._2
              }
            case (UndefinedType(parameterType, _), rt) => addBounds(parameterType, rt)
            case (lt, UndefinedType(parameterType, _)) => addBounds(parameterType, lt)
            case _ =>
              val t = argsPair._1.equiv(argsPair._2, undefinedSubst, falseUndef = false)
              if (!t._1) {
                result = (false, undefinedSubst)
                return
              }
              undefinedSubst = t._2
          }
          result = (true, undefinedSubst)
          return
        case p2: ScParameterizedType =>
          val args = p2.typeArguments
          val des = p2.designator
          if (args.length == 1 && (des.extractClass() match {
            case Some(q) => q.qualifiedName == "scala.Array"
            case _ => false
          })) {
            val arg = a1.argument
            val argsPair = (arg, args.head)
            argsPair match {
              case (ScAbstractType(tpt, lower, upper), r) =>
                val right =
                  if (tpt.arguments.nonEmpty && !r.isInstanceOf[ScParameterizedType])
                    ScParameterizedType(r, tpt.arguments)
                  else r
                if (!upper.equiv(Any)) {
                  val t = conformsInner(upper, right, visited, undefinedSubst, checkWeak, handler = handler.map(_.inner))
                  if (!t._1) {
                    result = (false, undefinedSubst)
                    return
                  }
                  undefinedSubst = t._2
                }
                if (!lower.equiv(Nothing)) {
                  val t = conformsInner(right, lower, visited, undefinedSubst, checkWeak, handler = handler.map(_.inner))
                  if (!t._1) {
                    result = (false, undefinedSubst)
                    return
                  }
                  undefinedSubst = t._2
                }
              case (l, ScAbstractType(tpt, lower, upper)) =>
                val left =
                  if (tpt.arguments.nonEmpty && !l.isInstanceOf[ScParameterizedType])
                    ScParameterizedType(l, tpt.arguments)
                  else l
                if (!upper.equiv(Any)) {
                  val t = conformsInner(upper, left, visited, undefinedSubst, checkWeak, handler = handler.map(_.inner))
                  if (!t._1) {
                    result = (false, undefinedSubst)
                    return
                  }
                  undefinedSubst = t._2
                }
                if (!lower.equiv(Nothing)) {
                  val t = conformsInner(left, lower, visited, undefinedSubst, checkWeak, handler = handler.map(_.inner))
                  if (!t._1) {
                    result = (false, undefinedSubst)
                    return
                  }
                  undefinedSubst = t._2
                }
              case (UndefinedType(parameterType, _), rt) => addBounds(parameterType, rt)
              case (lt, UndefinedType(parameterType, _)) => addBounds(parameterType, lt)
              case _ =>
                val t = argsPair._1.equiv(argsPair._2, undefinedSubst, falseUndef = false)
                if (!t._1) {
                  result = (false, undefinedSubst)
                  return
                }
                undefinedSubst = t._2
            }
            result = (true, undefinedSubst)
            return
          }
        case _ =>
      }

      rightVisitor = new AliasDesignatorVisitor with CompoundTypeVisitor with ExistentialVisitor
        with ProjectionVisitor {}
      r.visitType(rightVisitor)
      if (result != null) return
    }

    override def visitParameterizedType(p: ParameterizedType) {
      handler.foreach { h =>
        //        p.designator match {
        //          case p: ScProjectionType =>
        //            p.actualElement match {
        //              case a: ScTypeAlias => println(a.typeParameters) // for List (it is alias for ....)
        //              case _ =>
        //            }
        //            println(p.projected.canonicalText)
        //            println(p.element.getName)
        //            println(p.actualElement.getName)
        //            println(p.v.v.v.v.v.v.v)
        //        }
        h.log(p.designator.isValue, p.typeArguments)
        h.visit("visitParameterizedType")
      }

      var rightVisitor: ScalaTypeVisitor =
        new ValDesignatorSimplification with UndefinedSubstVisitor with AbstractVisitor {}
      r.visitType(rightVisitor)
      if (result != null) return

      p.designator match {
        case a: ScAbstractType =>
          val subst = ScSubstitutor(a.parameterType.arguments.zip(p.typeArguments).map {
            case (tpt: TypeParameterType, tp: ScType) => (tpt.nameAndId, tp)
          }.toMap)
          val upper: ScType =
            subst.subst(a.upper) match {
              case ParameterizedType(upper, _) => ScParameterizedType(upper, p.typeArguments)
              case upper => ScParameterizedType(upper, p.typeArguments)
            }
          handler.foreach { h =>
            h.log(a.upper, a.lower, a.parameterType, a.parameterType.arguments)
            h.logn(s"designator is abstract, instead of it upper ~ $upper")
          }
          if (!upper.equiv(Any)) {
            result = conformsInner(upper, r, visited, undefinedSubst, checkWeak, handler = handler.map(_.inner))
          } else {
            result = (true, undefinedSubst)
          }
          if (result._1) {
            val lower: ScType =
              subst.subst(a.lower) match {
                case ParameterizedType(lower, _) => ScParameterizedType(lower, p.typeArguments)
                case lower => ScParameterizedType(lower, p.typeArguments)
              }
            if (!lower.equiv(Nothing)) {
              val t = conformsInner(r, lower, visited, result._2, checkWeak, handler = handler.map(_.inner))
              if (t._1) result = t
            }
          }
          return
        case _ =>
      }

      rightVisitor = new ParameterizedAbstractVisitor {}
      r.visitType(rightVisitor)
      if (result != null) return

      checkEquiv()
      if (result != null) return

      rightVisitor = new ExistentialSimplification with ExistentialArgumentVisitor {}
      r.visitType(rightVisitor)
      if (result != null) return

      p.designator match {
        case s: ScExistentialArgument =>
          s.lower match {
            case ParameterizedType(lower, _) =>
              result = conformsInner(lower, r, visited, undefinedSubst, checkWeak, handler = handler.map(_.inner))
              return
            case lower =>
              result = conformsInner(lower, r, visited, undefinedSubst, checkWeak, handler = handler.map(_.inner))
              return
          }
        case _ =>
      }

      rightVisitor = new ParameterizedExistentialArgumentVisitor with OtherNonvalueTypesVisitor with NothingNullVisitor
        with ThisVisitor with DesignatorVisitor {}
      r.visitType(rightVisitor)
      if (result != null) return

      def processEquivalentDesignators(args2: Seq[ScType]): Unit = {
        val args1 = p.typeArguments
        val des1 = p.designator
        if (args1.length != args2.length) {
          result = (false, undefinedSubst)
          return
        }
        des1.extractDesignated(expandAliases = true) match {
          case Some(ownerDesignator) =>
            val parametersIterator = ownerDesignator match {
              case td: ScTypeParametersOwner => td.typeParameters.iterator
              case ownerDesignator: PsiTypeParameterListOwner => ownerDesignator.getTypeParameters.iterator
              case _ =>
                result = (false, undefinedSubst)
                return
            }
            result = checkParameterizedType(parametersIterator, args1, args2,
              undefinedSubst, visited, checkWeak, handler = handler)
          case _ =>
            result = (false, undefinedSubst)
        }
      }

      //todo: looks like this code can be simplified and unified.
      //todo: what if left is type alias declaration, right is type alias definition, which is alias to that declaration?
      p.isAliasType match {
        case Some(AliasType(ta, lower, _)) =>
          if (ta.isInstanceOf[ScTypeAliasDeclaration])
            r match {
              case ParameterizedType(proj, args2) if r.isAliasType.isDefined && (proj equiv p.designator) =>
                processEquivalentDesignators(args2)
                return
              case _ =>
            }
          if (lower.isEmpty) {
            result = (false, undefinedSubst)
            return
          }
          result = conformsInner(lower.get, r, visited, undefinedSubst, handler = handler.map(_.inner))
          return
        case _ =>
      }

      r match {
        case p2: ScParameterizedType =>
          val des1 = p.designator
          val des2 = p2.designator
          val args1 = p.typeArguments
          val args2 = p2.typeArguments
          (des1, des2) match {
            case (owner1: TypeParameterType, _: TypeParameterType) =>
              if (des1 equiv des2) {
                if (args1.length != args2.length) {
                  result = (false, undefinedSubst)
                } else {
                  result = checkParameterizedType(owner1.arguments.map(_.psiTypeParameter).iterator, args1, args2,
                    undefinedSubst, visited, checkWeak, handler = handler)
                }
              } else {
                result = (false, undefinedSubst)
              }
            case (_: UndefinedType, UndefinedType(parameterType, _)) =>
              (if (args1.length != args2.length) findDiffLengthArgs(l, args2.length) else Some((args1, des1))) match {
                case Some((aArgs, aType)) =>
                  undefinedSubst = undefinedSubst.addUpper(parameterType.nameAndId, aType)
                  result = checkParameterizedType(parameterType.arguments.map(_.psiTypeParameter).iterator, aArgs,
                    args2, undefinedSubst, visited, checkWeak, handler = handler)
                case _ =>
                  result = (false, undefinedSubst)
              }
            case (UndefinedType(parameterType, _), _) =>
              (if (args1.length != args2.length) findDiffLengthArgs(r, args1.length) else Some((args2, des2))) match {
                case Some((aArgs, aType)) =>
                  undefinedSubst = undefinedSubst.addLower(parameterType.nameAndId, aType)
                  result = checkParameterizedType(parameterType.arguments.map(_.psiTypeParameter).iterator, args1,
                    aArgs, undefinedSubst, visited, checkWeak, handler = handler)
                case _ =>
                  result = (false, undefinedSubst)
              }
            case (_, UndefinedType(parameterType, _)) =>
              (if (args1.length != args2.length) findDiffLengthArgs(l, args2.length) else Some((args1, des1))) match {
                case Some((aArgs, aType)) =>
                  undefinedSubst = undefinedSubst.addUpper(parameterType.nameAndId, aType)
                  result = checkParameterizedType(parameterType.arguments.map(_.psiTypeParameter).iterator, aArgs,
                    args2, undefinedSubst, visited, checkWeak, handler = handler)
                case _ =>
                  result = (false, undefinedSubst)
              }
            case _ if des1 equiv des2 =>
              result =
                if (args1.length != args2.length) (false, undefinedSubst)
                else extractParams(des1) match {
                  case Some(params) => checkParameterizedType(params, args1, args2, undefinedSubst, visited, checkWeak, handler = handler)
                  case _ => (false, undefinedSubst)
                }
            case (_, t: TypeParameterType) if t.arguments.length == p2.typeArguments.length =>
              val subst = ScSubstitutor(t.arguments.zip(p.typeArguments).map {
                case (tpt: TypeParameterType, tp: ScType) => (tpt.nameAndId, tp)
              }.toMap)
              result = conformsInner(des1, subst.subst(t.upperType.v), visited, undefinedSubst, checkWeak, handler = handler.map(_.inner))
            case (proj1: ScProjectionType, proj2: ScProjectionType)
              if smartEquivalence(proj1.actualElement, proj2.actualElement) =>
              val t = conformsInner(proj1, proj2, visited, undefinedSubst, handler = handler.map(_.inner))
              if (!t._1) {
                result = (false, undefinedSubst)
              } else {
                undefinedSubst = t._2
                if (args1.length != args2.length) {
                  result = (false, undefinedSubst)
                } else {
                  proj1.actualElement match {
                    case td: ScTypeParametersOwner =>
                      result = checkParameterizedType(td.typeParameters.iterator, args1, args2, undefinedSubst, visited, checkWeak, handler = handler)
                    case td: PsiTypeParameterListOwner =>
                      result = checkParameterizedType(td.getTypeParameters.iterator, args1, args2, undefinedSubst, visited, checkWeak, handler = handler)
                    case _ =>
                      result = (false, undefinedSubst)
                  }
                }
              }
            case _ =>
          }
        case _ =>
      }

      if (result != null) {
        //sometimes when the above part has failed, we still have to check for alias
        if (!result._1) r.isAliasType match {
          case Some(aliasType) =>
            rightVisitor = new ParameterizedAliasVisitor with TypeParameterTypeVisitor {}
            r.visitType(rightVisitor)
          case _ =>
        }
        return
      }

      rightVisitor = new ParameterizedAliasVisitor with TypeParameterTypeVisitor {}
      r.visitType(rightVisitor)
      if (result != null) return

      r match {
        case _: JavaArrayType =>
          val args = p.typeArguments
          val des = p.designator
          if (args.length == 1 && (des.extractClass() match {
            case Some(q) => q.qualifiedName == "scala.Array"
            case _ => false
          })) {
            val arg = r.asInstanceOf[JavaArrayType].argument
            val argsPair = (arg, args.head)
            argsPair match {
              case (ScAbstractType(tpt, lower, upper), r) =>
                val right =
                  if (tpt.arguments.nonEmpty && !r.isInstanceOf[ScParameterizedType])
                    ScParameterizedType(r, tpt.arguments)
                  else r
                if (!upper.equiv(Any)) {
                  val t = conformsInner(upper, right, visited, undefinedSubst, checkWeak, handler = handler.map(_.inner))
                  if (!t._1) {
                    result = (false, undefinedSubst)
                    return
                  }
                  undefinedSubst = t._2
                }
                if (!lower.equiv(Nothing)) {
                  val t = conformsInner(right, lower, visited, undefinedSubst, checkWeak, handler = handler.map(_.inner))
                  if (!t._1) {
                    result = (false, undefinedSubst)
                    return
                  }
                  undefinedSubst = t._2
                }
              case (l, ScAbstractType(tpt, lower, upper)) =>
                val left =
                  if (tpt.arguments.nonEmpty && !l.isInstanceOf[ScParameterizedType])
                    ScParameterizedType(l, tpt.arguments)
                  else l
                if (!upper.equiv(Any)) {
                  val t = conformsInner(upper, left, visited, undefinedSubst, checkWeak, handler = handler.map(_.inner))
                  if (!t._1) {
                    result = (false, undefinedSubst)
                    return
                  }
                  undefinedSubst = t._2
                }
                if (!lower.equiv(Nothing)) {
                  val t = conformsInner(left, lower, visited, undefinedSubst, checkWeak, handler = handler.map(_.inner))
                  if (!t._1) {
                    result = (false, undefinedSubst)
                    return
                  }
                  undefinedSubst = t._2
                }
              case (UndefinedType(parameterType, _), rt) => addBounds(parameterType, rt)
              case (lt, UndefinedType(parameterType, _)) => addBounds(parameterType, lt)
              case _ =>
                val t = argsPair._1.equiv(argsPair._2, undefinedSubst, falseUndef = false)
                if (!t._1) {
                  result = (false, undefinedSubst)
                  return
                }
                undefinedSubst = t._2
            }
            result = (true, undefinedSubst)
            return
          }
        case _ =>
      }

      p.designator match {
        case t: TypeParameterType if t.arguments.length == p.typeArguments.length =>
          val subst = ScSubstitutor(t.arguments.zip(p.typeArguments).map {
            case (tpt: TypeParameterType, tp: ScType) => (tpt.nameAndId, tp)
          }.toMap)
          result = conformsInner(subst.subst(t.lowerType.v), r, visited, undefinedSubst, checkWeak, handler = handler.map(_.inner))
          return
        case _ =>
      }

      rightVisitor = new AliasDesignatorVisitor with CompoundTypeVisitor with ExistentialVisitor
        with ProjectionVisitor {}
      r.visitType(rightVisitor)
      if (result != null) return
    }

    override def visitExistentialType(e: ScExistentialType) {
      handler.foreach { h =>
        h.visit("visitExistentialType")
      }
      var rightVisitor: ScalaTypeVisitor =
        new ValDesignatorSimplification with UndefinedSubstVisitor
          with AbstractVisitor
          with ParameterizedAbstractVisitor {}
      r.visitType(rightVisitor)
      if (result != null) return

      checkEquiv()
      if (result != null) return

      val simplified = e.simplify()
      if (simplified != l) {
        result = conformsInner(simplified, r, visited, undefinedSubst, checkWeak, handler = handler.map(_.inner))
        return
      }

      rightVisitor = new ExistentialSimplification with ExistentialArgumentVisitor
        with ParameterizedExistentialArgumentVisitor with OtherNonvalueTypesVisitor with NothingNullVisitor
        with TypeParameterTypeVisitor with ThisVisitor with DesignatorVisitor {}
      r.visitType(rightVisitor)
      if (result != null) return

      rightVisitor = new ParameterizedAliasVisitor with AliasDesignatorVisitor {}
      r.visitType(rightVisitor)
      if (result != null) return

      val tptsMap = new mutable.HashMap[String, TypeParameterType]()
      def updateType(t: ScType, rejected: HashSet[String] = HashSet.empty): ScType = {
        t.recursiveUpdate {
          case ScExistentialArgument(name, _, _, _) =>
            e.wildcards.find(_.name == name) match {
              case Some(ScExistentialArgument(thatName, args, lower, upper)) if !rejected.contains(thatName) =>
                val tpt = tptsMap.getOrElseUpdate(thatName,
                  TypeParameterType(args, Suspension(lower), Suspension(upper),
                    createTypeParameterFromText(name)(PsiManager.getInstance(DecompilerUtil.obtainProject))) //todo: remove obtainProject?
                )
                (true, tpt)
              case _ => (false, t)
            }
          case ScExistentialType(innerQ, wilds) =>
            (true, ScExistentialType(updateType(innerQ, rejected ++ wilds.map(_.name)), wilds))
          case tp: ScType => (false, tp)
        }
      }
      val q = updateType(e.quantified)
      val subst = tptsMap.foldLeft(ScSubstitutor.empty) {
        case (subst: ScSubstitutor, (_, tpt)) => subst.bindT(tpt.nameAndId, UndefinedType(tpt))
      }
      val res = conformsInner(subst.subst(q), r, HashSet.empty, undefinedSubst, handler = handler.map(_.inner))
      if (!res._1) {
        result = (false, undefinedSubst)
      } else {
        val unSubst: ScUndefinedSubstitutor = res._2
        unSubst.getSubstitutor(notNonable = false) match {
          case Some(uSubst) =>
            for (tpt <- tptsMap.values if result == null) {
              val substedTpt = uSubst.subst(tpt)
              var t = conformsInner(substedTpt, uSubst.subst(updateType(tpt.lowerType.v)), immutable.Set.empty, undefinedSubst, handler = handler.map(_.inner))
              if (substedTpt != tpt && !t._1) {
                result = (false, undefinedSubst)
                return
              }
              undefinedSubst = t._2
              t = conformsInner(uSubst.subst(updateType(tpt.upperType.v)), substedTpt, immutable.Set.empty, undefinedSubst, handler = handler.map(_.inner))
              if (substedTpt != tpt && !t._1) {
                result = (false, undefinedSubst)
                return
              }
              undefinedSubst = t._2
            }
            if (result == null) {
              val filterFunction: (((String, Long), Set[ScType])) => Boolean = {
                case (id: (String, Long), _: Set[ScType]) =>
                  !tptsMap.values.exists(_.nameAndId == id)
              }
              val newUndefSubst = unSubst.filter(filterFunction)
              undefinedSubst += newUndefSubst
              result = (true, undefinedSubst)
            }
          case None => result = (false, undefinedSubst)
        }
      }
    }

    override def visitThisType(t: ScThisType) {
      handler.foreach { h =>
        h.visit("visitThisType")
      }
      var rightVisitor: ScalaTypeVisitor =
        new ValDesignatorSimplification with UndefinedSubstVisitor with AbstractVisitor
          with ParameterizedAbstractVisitor {}
      r.visitType(rightVisitor)
      if (result != null) return

      checkEquiv()
      if (result != null) return

      rightVisitor = new ExistentialSimplification with ExistentialArgumentVisitor
        with ParameterizedExistentialArgumentVisitor with OtherNonvalueTypesVisitor with NothingNullVisitor
        with TypeParameterTypeVisitor {}
      r.visitType(rightVisitor)
      if (result != null) return

      val clazz = t.element
      val res = clazz.getTypeWithProjections(TypingContext.empty)
      if (res.isEmpty) result = (false, undefinedSubst)
      else result = conformsInner(res.get, r, visited, subst, checkWeak, handler = handler.map(_.inner))
    }

    override def visitDesignatorType(des: ScDesignatorType) {
      handler.foreach { h =>
        h.visit("visitDesignatorType")
      }
      des.getValType match {
        case Some(v) =>
          result = conformsInner(v, r, visited, subst, checkWeak, handler = handler.map(_.inner))
          return
        case _ =>
      }

      var rightVisitor: ScalaTypeVisitor =
        new ValDesignatorSimplification with UndefinedSubstVisitor with AbstractVisitor
          with ParameterizedAbstractVisitor {}
      r.visitType(rightVisitor)
      if (result != null) return

      checkEquiv()
      if (result != null) return

      rightVisitor = new ExistentialSimplification with ExistentialArgumentVisitor
        with ParameterizedExistentialArgumentVisitor with OtherNonvalueTypesVisitor with NothingNullVisitor
      {}
      r.visitType(rightVisitor)
      if (result != null) return

      rightVisitor = new TypeParameterTypeVisitor
        with ThisVisitor with DesignatorVisitor with ParameterizedAliasVisitor {}
      r.visitType(rightVisitor)
      if (result != null) return

      rightVisitor = new AliasDesignatorVisitor with ProjectionVisitor {}
      r.visitType(rightVisitor)
      if (result != null) return

      des.isAliasType match {
        case Some(AliasType(_, lower, _)) =>
          if (lower.isEmpty) {
            result = (false, undefinedSubst)
            return
          }
          result = conformsInner(lower.get, r, visited, undefinedSubst, handler = handler.map(_.inner))
          return
        case _ =>
      }

      rightVisitor = new CompoundTypeVisitor with ExistentialVisitor {}
      r.visitType(rightVisitor)
      if (result != null) return
    }

    override def visitTypeParameterType(tpt1: TypeParameterType) {
      handler.foreach { h =>
        h.visit("visitTypeParameterType")
      }
      var rightVisitor: ScalaTypeVisitor =
        new ValDesignatorSimplification with UndefinedSubstVisitor with AbstractVisitor
          with ParameterizedAbstractVisitor {}
      r.visitType(rightVisitor)
      if (result != null) return

      checkEquiv()
      if (result != null) return

      trait TypeParameterTypeNothingNullVisitor extends NothingNullVisitor {
        override def visitStdType(x: StdType) {
          handler.foreach { h =>
            h.rvisit("TypeParameterTypeNothingNullVisitor")
          }
          if (x eq Nothing) result = (true, undefinedSubst)
          else if (x eq Null) {
            result = conformsInner(tpt1.lowerType.v, r, HashSet.empty, undefinedSubst, handler = handler.map(_.inner))
          }
        }
      }

      rightVisitor = new ExistentialSimplification with ExistentialArgumentVisitor
        with ParameterizedExistentialArgumentVisitor with OtherNonvalueTypesVisitor with TypeParameterTypeNothingNullVisitor
        with DesignatorVisitor {}
      r.visitType(rightVisitor)
      if (result != null) return

      r match {
        case tpt2: TypeParameterType =>
          val res = conformsInner(tpt1.lowerType.v, r, HashSet.empty, undefinedSubst, handler = handler.map(_.inner))
          if (res._1) {
            result = res
            return
          }
          result = conformsInner(l, tpt2.upperType.v, HashSet.empty, undefinedSubst, handler = handler.map(_.inner))
          return
        case _ =>
      }

      val t = conformsInner(tpt1.lowerType.v, r, HashSet.empty, undefinedSubst, handler = handler.map(_.inner))
      if (t._1) {
        result = t
        return
      }

      rightVisitor = new ParameterizedAliasVisitor with AliasDesignatorVisitor with CompoundTypeVisitor
        with ExistentialVisitor with ProjectionVisitor {}
      r.visitType(rightVisitor)
      if (result != null) return

      result = (false, undefinedSubst)
    }

    override def visitExistentialArgument(s: ScExistentialArgument): Unit = {
      handler.foreach { h =>
        h.visit("visitExistentialArgument")
      }
      var rightVisitor: ScalaTypeVisitor =
        new ValDesignatorSimplification with UndefinedSubstVisitor
          with AbstractVisitor
          with ParameterizedAbstractVisitor {}
      r.visitType(rightVisitor)
      if (result != null) return

      checkEquiv()
      if (result != null) return

      val t = conformsInner(s.lower, r, HashSet.empty, undefinedSubst, handler = handler.map(_.inner))

      if (t._1) {
        result = t
        return
      }

      rightVisitor = new OtherNonvalueTypesVisitor with NothingNullVisitor
        with TypeParameterTypeVisitor with ThisVisitor with DesignatorVisitor {}
      r.visitType(rightVisitor)
      if (result != null) return

      rightVisitor = new ParameterizedAliasVisitor with AliasDesignatorVisitor with CompoundTypeVisitor
        with ExistentialVisitor with ProjectionVisitor {}
      r.visitType(rightVisitor)
      if (result != null) return
    }

    override def visitUndefinedType(u: UndefinedType) {
      handler.foreach { h =>
        h.visit("visitUndefinedType")
      }
      val rightVisitor = new ValDesignatorSimplification {
        override def visitUndefinedType(u2: UndefinedType) {
          val name = u2.parameterType.nameAndId
          result = (true, if (u2.level > u.level) {
            undefinedSubst.addUpper(name, u)
          } else if (u.level > u2.level) {
            undefinedSubst.addUpper(name, u)
          } else {
            undefinedSubst
          })
        }
      }
      r.visitType(rightVisitor)
      if (result == null)
        result = (true, undefinedSubst.addLower(u.parameterType.nameAndId, r))
    }

    override def visitMethodType(m1: ScMethodType) {
      handler.foreach { h =>
        h.visit("visitMethodType")
      }
      var rightVisitor: ScalaTypeVisitor =
        new ValDesignatorSimplification with UndefinedSubstVisitor
          with AbstractVisitor
          with ParameterizedAbstractVisitor {}
      r.visitType(rightVisitor)
      if (result != null) return

      checkEquiv()
      if (result != null) return

      rightVisitor = new ExistentialSimplification {}
      r.visitType(rightVisitor)
      if (result != null) return

      r match {
        case m2: ScMethodType =>
          val params1 = m1.params
          val params2 = m2.params
          val returnType1 = m1.returnType
          val returnType2 = m2.returnType
          if (params1.length != params2.length) {
            result = (false, undefinedSubst)
            return
          }
          var t = conformsInner(returnType1, returnType2, HashSet.empty, undefinedSubst, handler = handler.map(_.inner))
          if (!t._1) {
            result = (false, undefinedSubst)
            return
          }
          undefinedSubst = t._2
          var i = 0
          while (i < params1.length) {
            if (params1(i).isRepeated != params2(i).isRepeated) {
              result = (false, undefinedSubst)
              return
            }
            t = params1(i).paramType.equiv(params2(i).paramType, undefinedSubst, falseUndef = false)
            if (!t._1) {
              result = (false, undefinedSubst)
              return
            }
            undefinedSubst = t._2
            i = i + 1
          }
          result = (true, undefinedSubst)
        case _ =>
          result = (false, undefinedSubst)
      }
    }

    override def visitAbstractType(a: ScAbstractType) {
      handler.foreach { h =>
        h.visit("visitAbstractType")
      }
      val rightVisitor = new ValDesignatorSimplification with UndefinedSubstVisitor {}
      r.visitType(rightVisitor)
      if (result != null) return
      val right =
        if (a.parameterType.arguments.nonEmpty && !r.isInstanceOf[ScParameterizedType])
          ScParameterizedType(r, a.parameterType.arguments)
        else r

      result = conformsInner(a.upper, right, visited, undefinedSubst, checkWeak, handler = handler.map(_.inner))
      if (result._1) {
        val t = conformsInner(right, a.lower, visited, result._2, checkWeak, handler = handler.map(_.inner))
        if (t._1) result = t
      }
    }

    override def visitTypePolymorphicType(t1: ScTypePolymorphicType) {
      handler.foreach { h =>
        h.visit("visitTypePolymorphicType")
      }
      var rightVisitor: ScalaTypeVisitor =
        new ValDesignatorSimplification with UndefinedSubstVisitor
          with AbstractVisitor
          with ParameterizedAbstractVisitor {}
      r.visitType(rightVisitor)
      if (result != null) return

      checkEquiv()
      if (result != null) return

      rightVisitor = new ExistentialSimplification {}
      r.visitType(rightVisitor)
      if (result != null) return

      r match {
        case t2: ScTypePolymorphicType =>
          val typeParameters1 = t1.typeParameters
          val typeParameters2 = t2.typeParameters
          val internalType1 = t1.internalType
          val internalType2 = t2.internalType
          if (typeParameters1.length != typeParameters2.length) {
            result = (false, undefinedSubst)
            return
          }
          var i = 0
          while (i < typeParameters1.length) {
            var t = conformsInner(typeParameters1(i).lowerType.v, typeParameters2(i).lowerType.v, HashSet.empty, undefinedSubst, handler = handler.map(_.inner))
            if (!t._1) {
              result = (false, undefinedSubst)
              return
            }
            undefinedSubst = t._2
            t = conformsInner(typeParameters2(i).upperType.v, typeParameters1(i).lowerType.v, HashSet.empty, undefinedSubst, handler = handler.map(_.inner))
            if (!t._1) {
              result = (false, undefinedSubst)
              return
            }
            undefinedSubst = t._2
            i = i + 1
          }
          val subst = ScSubstitutor(typeParameters1.zip(typeParameters2).map {
            case (key, TypeParameter(_, lowerType, upperType, psiTypeParameter)) => (key.nameAndId,
              TypeParameterType(
                (psiTypeParameter match {
                  case typeParam: ScTypeParam => typeParam.typeParameters
                  case _ => Seq.empty
                }).map(TypeParameterType(_)),
                lowerType,
                upperType,
                psiTypeParameter))
          }.toMap)
          val t = conformsInner(subst.subst(internalType1), internalType2, HashSet.empty, undefinedSubst, handler = handler.map(_.inner))
          if (!t._1) {
            result = (false, undefinedSubst)
            return
          }
          undefinedSubst = t._2
          result = (true, undefinedSubst)
        case _ =>
          result = (false, undefinedSubst)
      }
    }
  }

  private def smartIsInheritor(leftClass: PsiClass, substitutor: ScSubstitutor, rightClass: PsiClass) : (Boolean, ScType) = {
    if (areClassesEquivalent(leftClass, rightClass)) return (false, null)
    if (!isInheritorDeep(leftClass, rightClass)) return (false, null)
    smartIsInheritor(leftClass, substitutor, areClassesEquivalent(_, rightClass), new collection.immutable.HashSet[PsiClass])
  }

  private def parentWithArgNumber(leftClass: PsiClass, substitutor: ScSubstitutor, argsNumber: Int): (Boolean, ScType) = {
    smartIsInheritor(leftClass, substitutor, c => c.getTypeParameters.length == argsNumber, new collection.immutable.HashSet[PsiClass]())
  }

  private def smartIsInheritor(leftClass: PsiClass, substitutor: ScSubstitutor, condition: PsiClass => Boolean,
                               visited: collection.immutable.HashSet[PsiClass]): (Boolean, ScType) = {
    ProgressManager.checkCanceled()
    val bases: Seq[Any] = leftClass match {
      case td: ScTypeDefinition => td.superTypes
      case _ => leftClass.getSuperTypes
    }
    val iterator = bases.iterator
    val later: ArrayBuffer[(PsiClass, ScSubstitutor)] = new ArrayBuffer[(PsiClass, ScSubstitutor)]()
    var res: ScType = null
    while (iterator.hasNext) {
      val tp: ScType = iterator.next() match {
        case tp: ScType => substitutor.subst(tp)
        case pct: PsiClassType =>
          substitutor.subst(pct.toScType()) match {
            case ex: ScExistentialType => ex.quantified //it's required for the raw types
            case r => r
          }
      }
      tp.extractClassType(leftClass.getProject) match {
        case Some((clazz: PsiClass, _)) if visited.contains(clazz) =>
        case Some((clazz: PsiClass, _)) if condition(clazz) =>
          if (res == null) res = tp
          else if (tp.conforms(res)) res = tp
        case Some((clazz: PsiClass, subst)) =>
          later += ((clazz, subst))
        case _ =>
      }
    }
    val laterIterator = later.iterator
    while (laterIterator.hasNext) {
      val (clazz, subst) = laterIterator.next()
      val recursive = smartIsInheritor(clazz, subst, condition, visited + clazz)
      if (recursive._1) {
        if (res == null) res = recursive._2
        else if (recursive._2.conforms(res)) res = recursive._2
      }
    }
    if (res == null) (false, null)
    else (true, res)
  }

  def extractParams(des: ScType): Option[Iterator[PsiTypeParameter]] = {
    des match {
      case undef: UndefinedType =>
        Option(undef.parameterType.psiTypeParameter).map(_.getTypeParameters.iterator)
      case _ =>
        des.extractClass().map {
          case td: ScTypeDefinition => td.typeParameters.iterator
          case other => other.getTypeParameters.iterator
        }
    }
  }

  def addParam(parameterType: TypeParameterType, bound: ScType, undefinedSubst: ScUndefinedSubstitutor,
               defArgs: Seq[ScType], undefArgs: Seq[ScType], handler: Option[DebugConformanceAction.Handler] = None): (Boolean, ScUndefinedSubstitutor) =
    addArgedBound(parameterType, bound, undefinedSubst, defArgs, undefArgs, variance = 0, addUpper = true, addLower = true, handler)

  def addArgedBound(parameterType: TypeParameterType, bound: ScType, undefinedSubst: ScUndefinedSubstitutor,
                    defArgs: Seq[ScType], undefArgs: Seq[ScType], variance: Int = 1,
                    addUpper: Boolean = false, addLower: Boolean = false, handler: Option[DebugConformanceAction.Handler]): (Boolean, ScUndefinedSubstitutor) = {
    handler.foreach { h =>
      h.logn("addArgedBound")
    }
    if (!addUpper && !addLower) return (false, undefinedSubst)
    var res = undefinedSubst
    if (addUpper) res = res.addUpper(parameterType.nameAndId, bound, variance = variance)
    if (addLower) res = res.addLower(parameterType.nameAndId, bound, variance = variance)
    (true, res)
  }

  def processHigherKindedTypeParams(undefType: ParameterizedType, defType: ParameterizedType, undefinedSubst: ScUndefinedSubstitutor,
                                    falseUndef: Boolean): (Boolean, ScUndefinedSubstitutor) = {
    val defTypeExpanded = defType.isAliasType.map(_.lower).map {
      case Success(p: ScParameterizedType, _) => p
      case _ => defType
    }.getOrElse(defType)
    extractParams(defTypeExpanded.designator) match {
      case Some(params) =>
        val undef = undefType.designator.asInstanceOf[UndefinedType]
        var defArgsReplace = defTypeExpanded.typeArguments
        val bound = if (params.nonEmpty) {
          if (defTypeExpanded.typeArguments.length != undefType.typeArguments.length)
          {
            if (defType.typeArguments.length != undefType.typeArguments.length) {
              findDiffLengthArgs(defType, undefType.typeArguments.length) match {
                case Some((newArgs, newDes)) =>
                  defArgsReplace = newArgs
                  newDes
                case _ => return (false, undefinedSubst)
              }
            } else {
              defArgsReplace =defType.typeArguments
              defType.designator
            }
          } else defTypeExpanded.designator
        } else {
          defTypeExpanded.designator
        }
        val y = undef.equiv(bound, undefinedSubst, falseUndef)
        if (!y._1) {
          (false, undefinedSubst)
        } else {
          val undefArgIterator = undefType.typeArguments.iterator
          val defIterator = defArgsReplace.iterator
          var sub = y._2
          while (params.hasNext && undefArgIterator.hasNext && defIterator.hasNext) {
            val arg1 = undefArgIterator.next()
            val arg2 = defIterator.next()
            val t = arg1.equiv(arg2, sub, falseUndef = false)
            if (!t._1) return (false, undefinedSubst)
            sub = t._2
          }
          (true, sub)
        }
      case _ => (false, undefinedSubst)
    }
  }

  def findDiffLengthArgs(eType: ScType, argLength: Int): Option[(Seq[ScType], ScType)] =
    eType.extractClassType() match {
      case Some((clazz, classSubst)) =>
        val t: (Boolean, ScType) = parentWithArgNumber(clazz, classSubst, argLength)
        if (!t._1) {
          None
        } else t._2 match {
          case ParameterizedType(newDes, newArgs) =>
            Some(newArgs, newDes)
          case _ =>
            None
        }
      case _ =>
        None
    }
}
