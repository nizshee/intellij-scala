package org.jetbrains.plugins.scala
package lang
package psi
package types

import com.intellij.openapi.progress.ProgressManager
import com.intellij.openapi.util.Computable
import com.intellij.psi._
import org.jetbrains.plugins.scala.actions.{ConformanceCondition, DCHandler, DebugConformanceAction, Relation}
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
import org.jetbrains.plugins.scala.macroAnnotations.uninstrumental
import org.jetbrains.plugins.scala.util.ScEquivalenceUtil._

import _root_.scala.collection.immutable.HashSet
import scala.annotation.tailrec
import scala.collection.mutable.ArrayBuffer
import scala.collection.{Seq, immutable, mutable}

object Conformance extends api.Conformance {
  override implicit lazy val typeSystem = ScalaTypeSystem

  @uninstrumental("handler")
  override protected def computable(left: ScType, right: ScType, visited: Set[PsiClass], checkWeak: Boolean, handler: Option[DCHandler.Conformance]) =
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

        handler.foreach(_.log("visitor didn't get result"))

        //tail, based on class inheritance
        right.extractClassType() match {
          case Some((clazz: PsiClass, _)) if visited.contains(clazz) =>
            return (false, substitutor)
          case Some((rClass: PsiClass, subst: ScSubstitutor)) =>
            left.extractClass(rClass.getProject) match {
              case Some(lClass) =>
                if (rClass.qualifiedName == "java.lang.Object") {
                  return conformsInner(left, AnyRef, visited, substitutor, checkWeak, handler = handler)
                } else if (lClass.qualifiedName == "java.lang.Object") {
                  return conformsInner(AnyRef, right, visited, substitutor, checkWeak, handler = handler)
                }
                val inh = smartIsInheritor(rClass, subst, lClass)
                if (!inh._1) {
                  handler.foreach(_ + ConformanceCondition.BaseClass(left, right, satisfy = false))
                  return (false, substitutor)
                }
                val tp = inh._2

                //Special case for higher kind types passed to generics.
                if (lClass.hasTypeParameters) {
                  left match {
                    case _: ScParameterizedType =>
                    case _ =>
                      handler.foreach(_ + ConformanceCondition.BaseClass(left, right, satisfy = true))
                      return (true, substitutor)
                  }
                }
                val inner = handler.map(_.inner)
                val t = conformsInner(left, tp, visited + rClass, substitutor, checkWeak = false, handler = inner)
                handler.foreach { h =>
                  h + ConformanceCondition.Transitive(left, tp, right,
                    Relation.Conformance(left, tp, inner.get.conditions),
                    Relation.Conformance(tp, right, Seq(ConformanceCondition.BaseClass(tp, right, satisfy = true)))
                  )
                }
                if (t._1) return (true, t._2)
                else return (false, substitutor)
              case _ =>
            }
          case _ =>
        }
        val bases: Seq[ScType] = BaseTypes.get(right)
        val iterator = bases.iterator
        while (iterator.hasNext) {
          ProgressManager.checkCanceled()
          val tp = iterator.next()
          val t = conformsInner(left, tp, visited, substitutor, checkWeak = true, handler = handler.map(_.inner))
          if (t._1) return (true, t._2)
        }

        (false, substitutor)
      }
    }

  @uninstrumental("handler")
  private def checkParameterizedType(parametersIterator: Iterator[PsiTypeParameter], args1: scala.Seq[ScType],
                                     args2: scala.Seq[ScType], _undefinedSubst: ScUndefinedSubstitutor,
                                     visited: Set[PsiClass], checkWeak: Boolean, handler: Option[DCHandler.Conformance]): (Boolean, ScUndefinedSubstitutor) = {
    var undefinedSubst = _undefinedSubst

    handler.foreach(_.log("checkParameterizedType"))

    def addAbstract(upper: ScType, lower: ScType, tp: ScType, alternateTp: ScType): Boolean = {
      handler.foreach(_.log("addAbstract - todo"))
      if (!upper.equiv(Any)) {
        val t = conformsInner(upper, tp, visited, undefinedSubst, checkWeak, handler = handler.map(_.inner))
        if (!t._1) {
          val t = conformsInner(upper, alternateTp, visited, undefinedSubst, checkWeak, handler = handler.map(_.inner))
          if (!t._1) {
            return false
          }
          else undefinedSubst = t._2
        } else undefinedSubst = t._2
      }
      if (!lower.equiv(Nothing)) {
        val t = conformsInner(tp, lower, visited, undefinedSubst, checkWeak, handler = handler.map(_.inner))
        if (!t._1) {
          val t = conformsInner(alternateTp, lower, visited, undefinedSubst, checkWeak, handler = handler.map(_.inner))
          if (!t._1) {
            return false
          }
          else undefinedSubst = t._2
        } else undefinedSubst = t._2
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
          val inner = handler.map(_.inner)
          val y = conformsInner(argsPair._2, argsPair._1, HashSet.empty, undefinedSubst, handler = inner)
          handler.foreach(_ + ConformanceCondition.Contrvariant(scp.name, Relation.Conformance(argsPair._2, argsPair._1,
            inner.get.conditions)))
          if (!y._1) {
            if (handler.nonEmpty) handler.foreach(_.corrupt())
            else return (false, undefinedSubst)
          }
          else undefinedSubst = y._2
        case scp: ScTypeParam if scp.isCovariant =>
          val inner = handler.map(_.inner)
          val y = conformsInner(argsPair._1, argsPair._2, HashSet.empty, undefinedSubst, handler = inner)
          handler.foreach(_ + ConformanceCondition.Covariant(scp.name, Relation.Conformance(argsPair._1, argsPair._2,
            inner.get.conditions)))
          if (!y._1) {
            if (handler.nonEmpty) handler.foreach(_.corrupt())
            else return (false, undefinedSubst)
          }
          undefinedSubst = y._2
        //this case filter out such cases like undefined type
        case _ =>
          argsPair match {
            case (UndefinedType(parameterType, _), rt) =>
              val y = addParam(parameterType, rt, undefinedSubst, args2, args1, handler)
              handler.foreach(_ + ConformanceCondition.Invariant(tp.name, Relation.Equivalence(argsPair._1, rt, satisfy = y._1), restriction = true))
              if (!y._1) {
                if (handler.nonEmpty) handler.foreach(_.corrupt())
                else return (false, undefinedSubst)
              }
              undefinedSubst = y._2
            case (lt, UndefinedType(parameterType, _)) =>
              val y = addParam(parameterType, lt, undefinedSubst, args1, args2, handler)
              handler.foreach(_ + ConformanceCondition.Invariant(tp.name, Relation.Equivalence(lt, argsPair._2, satisfy = y._1), restriction = true))
              if (!y._1) {
                if (handler.nonEmpty) handler.foreach(_.corrupt())
                else return (false, undefinedSubst)
              }
              undefinedSubst = y._2
            case (ScAbstractType(tpt, lower, upper), r) =>
              handler.foreach(_.log("ScAbstractType left - todo"))
              val (right, alternateRight) =
                if (tpt.arguments.nonEmpty && !r.isInstanceOf[ScParameterizedType])
                  (ScParameterizedType(r, tpt.arguments), r)
                else (r, r)
              if (!addAbstract(upper, lower, right, alternateRight)) {
                if (handler.nonEmpty) handler.foreach(_.corrupt())
                else return (false, undefinedSubst)
              }
            case (l, ScAbstractType(tpt, lower, upper)) =>
              handler.foreach(_.log("ScAbstractType right - todo"))
              val (left, alternateLeft) =
                if (tpt.arguments.nonEmpty && !l.isInstanceOf[ScParameterizedType])
                  (ScParameterizedType(l, tpt.arguments), l)
                else (l, l)
              if (!addAbstract(upper, lower, left, alternateLeft)) {
                if (handler.nonEmpty) handler.foreach(_.corrupt())
                else return (false, undefinedSubst)
              }
            case _ =>
              val t = argsPair._1.equiv(argsPair._2, undefinedSubst, falseUndef = false)
              handler.foreach(_ + ConformanceCondition.Invariant(tp.name,
                Relation.Equivalence(argsPair._1, argsPair._2, satisfy = t._1)))
              if (!t._1) {
                if (handler.nonEmpty) handler.foreach(_.corrupt())
                else return (false, undefinedSubst)
              }
              undefinedSubst = t._2
          }
      }
    }
    if (handler.nonEmpty) if (handler.exists(_.corrupted)) return (false, undefinedSubst) // TODO? add exists to macros
    (true, undefinedSubst)
  }

  @uninstrumental("handler")
  private class LeftConformanceVisitor(l: ScType, r: ScType, visited: Set[PsiClass],
                                       subst: ScUndefinedSubstitutor,
                                       checkWeak: Boolean = false,
                                       handler: Option[DCHandler.Conformance] = None) extends ScalaTypeVisitor {
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
        handler.foreach(_.rvisit("ValDesignatorSimplification - ok"))
        d.getValType match {
          case Some(v) =>
            val inner = handler.map(_.inner)
            result = conformsInner(l, v, visited, subst, checkWeak, handler = inner)
            handler.foreach { h =>
              val m = v
              h + ConformanceCondition.Transitive(l, m, r,
                Relation.Conformance(l, m, Seq(ConformanceCondition.Equivalent(Relation.Equivalence(l, m, satisfy = true)))),
                Relation.Conformance(m, r, inner.get.conditions)
              )
            }
          case _ =>
        }
      }
    }

    trait UndefinedSubstVisitor extends ScalaTypeVisitor {
      override def visitUndefinedType(u: UndefinedType) {
        handler.foreach { h =>
          h.rvisit("UndefinedSubstVisitor - ok")
          h + ConformanceCondition.Undefined(l, u, l) // TODO? add subst; where upper, lower?
        }
        result = (true, undefinedSubst.addUpper(u.parameterType.nameAndId, l))
      }
    }

    trait AbstractVisitor extends ScalaTypeVisitor {
      override def visitAbstractType(a: ScAbstractType) {
        handler.foreach(_.rvisit(s"AbstractVisitor - todo"))
        val left =
          if (a.parameterType.arguments.nonEmpty && !l.isInstanceOf[ScParameterizedType]) {
            ScParameterizedType(l, a.parameterType.arguments)
          }
          else l
        var conditions1 = handler.map(_ => Seq.empty[ConformanceCondition])
        if (!a.lower.equiv(Nothing)) {
          val inner = handler.map(_.inner)
          result = conformsInner(left, a.lower, visited, undefinedSubst, checkWeak, handler = inner)
          handler.foreach(_ => conditions1 = inner.map(_.conditions))
        } else {
          result = (true, undefinedSubst)
          handler.foreach(_ => conditions1 = Some(Seq(ConformanceCondition.FromNothing(a))))
        }
        if ((result._1 && !a.upper.equiv(Any)) || handler.nonEmpty) {
          val inner = handler.map(_.inner)
          val t = conformsInner(a.upper, left, visited, result._2, checkWeak, handler = inner)
//          handler.foreach(_ + ConformanceCondition.AbstractRight(left, a, a.upper, ???, ???, ???))
          if (t._1) result = t //this is optionally
        }
      }
    }

    trait ParameterizedAbstractVisitor extends ScalaTypeVisitor {
      override def visitParameterizedType(p: ParameterizedType) {
        handler.foreach(_.rvisit(s"ParameterizedAbstractVisitor - todo (not common)"))
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
      if (isEquiv._1) {
        handler.foreach(_ + ConformanceCondition.Equivalent(Relation.Equivalence(l, r, satisfy = true)))
        result = isEquiv
      }
    }

    trait ExistentialSimplification extends ScalaTypeVisitor {
      override def visitExistentialType(e: ScExistentialType) {
        handler.foreach(_.rvisit("ExistentialSimplification - ok"))
        val simplified = e.simplify()
        if (simplified != r) {
          val inner = handler.map(_.inner)
          result = conformsInner(l, simplified, visited, undefinedSubst, checkWeak, handler = inner)
          handler.foreach(_ + ConformanceCondition.ExistentialRight(l, e, Relation.Conformance(l, simplified, inner.get.conditions)))
        }
      }
    }

    trait ExistentialArgumentVisitor extends ScalaTypeVisitor {
      override def visitExistentialArgument(s: ScExistentialArgument): Unit = {
        handler.foreach(_.rvisit("ExistentialArgumentVisitor - ok"))
        val inner = handler.map(_.inner)
        result = conformsInner(l, s.upper, HashSet.empty, undefinedSubst, handler = inner)
        handler.foreach(_ + ConformanceCondition.Transitive(l, s.upper, s,
          Relation.Conformance(l, s.upper, inner.get.conditions),
          Relation.Conformance(s.upper, s, Seq(ConformanceCondition.TypeUpper(s.upper, s, satisfy = true)))
        ))
      }
    }

    trait ParameterizedExistentialArgumentVisitor extends ScalaTypeVisitor {
      override def visitParameterizedType(p: ParameterizedType) {
        handler.foreach(_.rvisit(s"ParameterizedExistentialArgumentVisitor - ok"))
        p.designator match {
          case s: ScExistentialArgument =>
            s.upper match {
              case ParameterizedType(upper, _) =>
                val inner = handler.map(_.inner)
                result = conformsInner(l, upper, visited, undefinedSubst, checkWeak, handler = inner)
                handler.foreach(_ + ConformanceCondition.Transitive(l, upper, p,
                  Relation.Conformance(l, upper, inner.get.conditions),
                  Relation.Conformance(upper, p, Seq(ConformanceCondition.TypeUpper(upper, p, satisfy = true)))
                ))
              case upper =>
                val inner = handler.map(_.inner)
                result = conformsInner(l, upper, visited, undefinedSubst, checkWeak, handler = inner)
                handler.foreach(_ + ConformanceCondition.Transitive(l, upper, p,
                  Relation.Conformance(l, upper, inner.get.conditions),
                  Relation.Conformance(upper, p, Seq(ConformanceCondition.TypeUpper(upper, p, satisfy = true)))
                ))
            }
          case _ =>
        }
      }
    }

    trait OtherNonvalueTypesVisitor extends ScalaTypeVisitor {
      override def visitUndefinedType(u: UndefinedType) {
        handler.foreach(_.rvisit("OtherNonvalueTypes - undefined - ok"))
        result = (false, undefinedSubst)
      }

      override def visitMethodType(m: ScMethodType) {
        handler.foreach(_.rvisit("OtherNonvalueTypes - method - ok"))
        result = (false, undefinedSubst)
      }

      override def visitAbstractType(a: ScAbstractType) {
        handler.foreach(_.rvisit("OtherNonvalueTypes - abstract - ok"))
        result = (false, undefinedSubst)
      }

      override def visitTypePolymorphicType(t: ScTypePolymorphicType) {
        handler.foreach(_.rvisit("OtherNonvalueTypes - typePolymorphic - ok"))
        result = (false, undefinedSubst)
      }
    }

    trait NothingNullVisitor extends ScalaTypeVisitor {
      override def visitStdType(x: StdType) {
        handler.foreach(_.rvisit("NothingNullVisitor - ok"))
        if (x eq Nothing) {
          handler.foreach(_ + ConformanceCondition.FromNothing(l))
          result = (true, undefinedSubst)
        }
        else if (x eq Null) {
          /*
            this case for checking: val x: T = null
            This is good if T class type: T <: AnyRef and !(T <: NotNull)
           */
          if (!l.conforms(AnyRef)) {
            handler.foreach(_ + ConformanceCondition.FromNull(l, anyRef = false, notNull = false))
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
              handler.foreach(_ + ConformanceCondition.FromNull(l, anyRef = true, notNull = flag))
              result = (!flag, undefinedSubst) // todo: think about undefinedSubst
            case _ =>
              handler.foreach(_ + ConformanceCondition.FromNull(l, anyRef = true, notNull = false))
              result = (true, undefinedSubst)
          }
        }
      }
    }

    trait TypeParameterTypeVisitor extends ScalaTypeVisitor {
      override def visitTypeParameterType(tpt: TypeParameterType) {
        handler.foreach(_.rvisit("TypeParameterTypeVisitor - ok"))
        val inner = handler.map(_.inner)
        result = conformsInner(l, tpt.upperType.v, substitutor = undefinedSubst, handler = inner)
        handler.foreach { h =>
          val u = tpt.upperType.v
          h + ConformanceCondition.Transitive(l, u, r,
            Relation.Conformance(l, u, Seq(ConformanceCondition.TypeUpper(u, tpt, satisfy = true))),
            Relation.Conformance(u, r, inner.get.conditions)
          )
        }
      }
    }

    trait ThisVisitor extends ScalaTypeVisitor {
      override def visitThisType(t: ScThisType) {
        handler.foreach(_.rvisit("ThisVisitor - ok"))
        val clazz = t.element
        val res = clazz.getTypeWithProjections(TypingContext.empty)
        if (res.isEmpty) result = (false, undefinedSubst)
        else {
          val inner = handler.map(_.inner)
          result = conformsInner(l, res.get, visited, subst, checkWeak, handler = inner)
          handler.foreach(_ + ConformanceCondition.Transitive(l, res.get, t,
            Relation.Conformance(res.get, t, inner.get.conditions),
            Relation.Conformance(l, res.get, Seq(ConformanceCondition.Equivalent(Relation.Equivalence(l, res.get, satisfy = true))))
          ))
        }
      }
    }

    trait DesignatorVisitor extends ScalaTypeVisitor {
      override def visitDesignatorType(d: ScDesignatorType) {
        handler.foreach(_.rvisit("DesignatorVisitor - ok"))
        d.element match {
          case v: ScBindingPattern =>
            val res = v.getType(TypingContext.empty)
            if (res.isEmpty) result = (false, undefinedSubst)
            else {
              val inner = handler.map(_.inner)
              result = conformsInner(l, res.get, visited, undefinedSubst, handler = inner)
              handler.foreach { h =>
                val m = res.get
                h + ConformanceCondition.Transitive(l, m, r,
                  Relation.Conformance(l, m, inner.get.conditions),
                  Relation.Conformance(m, r, Seq(ConformanceCondition.Equivalent(Relation.Equivalence(m, r, satisfy = true))))
                )
              }
            }
          case v: ScParameter =>
            val res = v.getType(TypingContext.empty)
            if (res.isEmpty) result = (false, undefinedSubst)
            else {
              val inner = handler.map(_.inner)
              result = conformsInner(l, res.get, visited, undefinedSubst, handler = inner)
              handler.foreach { h =>
                val m = res.get
                h + ConformanceCondition.Transitive(l, m, r,
                  Relation.Conformance(l, m, inner.get.conditions),
                  Relation.Conformance(m, r, Seq(ConformanceCondition.Equivalent(Relation.Equivalence(m, r, satisfy = true))))
                )
              }
            }
          case v: ScFieldId =>
            val res = v.getType(TypingContext.empty)
            if (res.isEmpty) result = (false, undefinedSubst)
            else {
              val inner = handler.map(_.inner)
              result = conformsInner(l, res.get, visited, undefinedSubst, handler = inner)
              handler.foreach { h =>
                val m = res.get
                h + ConformanceCondition.Transitive(l, m, r,
                  Relation.Conformance(l, m, inner.get.conditions),
                  Relation.Conformance(m, r, Seq(ConformanceCondition.Equivalent(Relation.Equivalence(m, r, satisfy = true))))
                )
              }
            }
          case _ =>
        }
      }
    }

    trait ParameterizedAliasVisitor extends ScalaTypeVisitor {
      override def visitParameterizedType(p: ParameterizedType) {
        handler.foreach(_.rvisit("ParameterizedAliasVisitor - ok"))
        p.isAliasType match {
          case Some(AliasType(_, _, upper)) =>
            if (upper.isEmpty) {
              result = (false, undefinedSubst)
              return
            }
            val inner = handler.map(_.inner)
            result = conformsInner(l, upper.get, visited, undefinedSubst, handler = inner)
            handler.foreach { h =>
              val m = upper.get
              h + ConformanceCondition.Transitive(l, m, r,
                Relation.Conformance(l, m, inner.get.conditions),
                Relation.Conformance(m, r, Seq(ConformanceCondition.TypeUpper(m, r, satisfy = true)))
              )
            }
          case _ =>
        }
      }
    }

    trait AliasDesignatorVisitor extends ScalaTypeVisitor {
      def stopDesignatorAliasOnFailure: Boolean = false

      override def visitDesignatorType(des: ScDesignatorType) {
        handler.foreach(_.rvisit("AliasDesignatorVisitor - ok"))
        des.isAliasType match {
          case Some(AliasType(_, _, upper)) =>
            if (upper.isEmpty) return
            val inner = handler.map(_.inner)
            val res = conformsInner(l, upper.get, visited, undefinedSubst, handler = inner)
            handler.foreach { h =>
              val m = upper.get
              h + ConformanceCondition.Transitive(l, r, m,
                Relation.Conformance(l, m, inner.get.conditions),
                Relation.Conformance(m, r, Seq(ConformanceCondition.TypeUpper(m, r, satisfy = true)))
              )
            }
            if (stopDesignatorAliasOnFailure || res._1) result = res
          case _ =>
        }
      }
    }

    trait CompoundTypeVisitor extends ScalaTypeVisitor {
      override def visitCompoundType(c: ScCompoundType) {
        handler.foreach(_.rvisit("CompoundTypeVisitor - ok"))
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
        var relations = handler.map(_ => Seq.empty[Relation.Conformance])
        traverse { (t, s) =>
          handler.foreach { _ =>
            val r = Equivalence.equivInner(l, t, s)
            if (r._1) relations = Some(
              relations.get :+
                Relation.Conformance(l, t, Seq(ConformanceCondition.Equivalent(Relation.Equivalence(l, t, r._1))))
            )
          }
          Equivalence.equivInner(l, t, s)
        }
        traverse { (t, s) =>
          handler.foreach { _ =>
            val inner = handler.map(_.inner)
            conformsInner(l, t, HashSet.empty, s, handler = inner)
            relations = Some(relations.get :+ Relation.Conformance(l, t, inner.get.conditions))
          }
          conformsInner(l, t, HashSet.empty, s)
        }

        handler.foreach(_ + ConformanceCondition.CompoundRight(l, c, relations.get))

        if (results.length == 1) {
          result = (true, results.head)
          return
        } else if (results.length > 1) {
          result = (true, ScUndefinedSubstitutor.multi(results.reverse))
          return
        }

        result = l.isAliasType match {
          case Some(AliasType(_: ScTypeAliasDefinition, Success(comp: ScCompoundType, _), _)) =>
            conformsInner(comp, c, HashSet.empty, undefinedSubst, handler = handler)
          case _ => (false, undefinedSubst)
        }
      }
    }

    trait ExistentialVisitor extends ScalaTypeVisitor {
      override def visitExistentialType(ex: ScExistentialType) {
        handler.foreach(_.rvisit("ExistentialVisitor - ok"))
        val inner = handler.map(_.inner)
        result = conformsInner(l, ex.quantified, HashSet.empty, undefinedSubst, handler = inner)
        handler.foreach(_ + ConformanceCondition.ExistentialRight(l, ex, Relation.Conformance(l, ex.quantified, inner.get.conditions)))
      }
    }

    trait ProjectionVisitor extends ScalaTypeVisitor {
      def stopProjectionAliasOnFailure: Boolean = false

      override def visitProjectionType(proj2: ScProjectionType) {
        handler.foreach(_.rvisit("ProjectionVisitor - ok"))
        proj2.isAliasType match {
          case Some(AliasType(_, _, upper)) =>
            if (upper.isEmpty) return
            val inner = handler.map(_.inner)
            val res = conformsInner(l, upper.get, visited, undefinedSubst, handler = inner)
            handler.foreach { h =>
              val m = upper.get
              h + ConformanceCondition.Transitive(l, m, r,
                Relation.Conformance(l, m, inner.get.conditions),
                Relation.Conformance(m, r, Seq(ConformanceCondition.TypeUpper(m, r, satisfy = true)))
              )
            }
            if (stopProjectionAliasOnFailure || res._1) result = res
          case _ =>
            l match {
              case proj1: ScProjectionType if smartEquivalence(proj1.actualElement, proj2.actualElement) =>
                val projected1 = proj1.projected
                val projected2 = proj2.projected
                val inner = handler.map(_.inner)
                result = conformsInner(projected1, projected2, visited, undefinedSubst, handler = inner)
                handler.foreach(_ + ConformanceCondition.Projection(Relation.Conformance(projected1, projected2, inner.get.conditions)))
              case param@ParameterizedType(projDes: ScProjectionType, _) => // TODO?
                handler.foreach(_.logn("left is parametrized type of projection - skip"))
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
                          map(c => conformsInner(ScParameterizedType(dt.designator, param.typeArguments), // TODO? wit
                            cutProj(c, acc), visited, undefinedSubst, handler = handler.map(_.inner)))).map(t => if (t._1) result = t)
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
                    val inner = handler.map(_.inner)
                    result = conformsInner(l, syntheticClass.t, HashSet.empty, undefinedSubst, handler = inner)
                    handler.foreach { h =>
                      val m = syntheticClass.t
                      h + ConformanceCondition.Transitive(l, m, r,
                        Relation.Conformance(l, m, inner.get.conditions),
                        Relation.Conformance(m, r, Seq(ConformanceCondition.Equivalent(Relation.Equivalence(m, r, satisfy = true))))
                      )
                    }
                  case v: ScBindingPattern =>
                    val res = v.getType(TypingContext.empty)
                    if (res.isEmpty) result = (false, undefinedSubst)
                    else {
                      val inner = handler.map(_.inner)
                      result = conformsInner(l, proj2.actualSubst.subst(res.get), visited, undefinedSubst, handler = inner)
                      handler.foreach { h =>
                        val m = proj2.actualSubst.subst(res.get)
                        h + ConformanceCondition.Transitive(l, m, r,
                          Relation.Conformance(l, m, inner.get.conditions),
                          Relation.Conformance(m, r, Seq(ConformanceCondition.Equivalent(Relation.Equivalence(m, r, satisfy = true))))
                        )
                      }
                    }
                  case v: ScParameter =>
                    val res = v.getType(TypingContext.empty)
                    if (res.isEmpty) result = (false, undefinedSubst)
                    else {
                      val inner = handler.map(_.inner)
                      result = conformsInner(l, proj2.actualSubst.subst(res.get), visited, undefinedSubst, handler = inner)
                      handler.foreach { h =>
                        val m = proj2.actualSubst.subst(res.get)
                        h + ConformanceCondition.Transitive(l, m, r,
                          Relation.Conformance(l, m, inner.get.conditions),
                          Relation.Conformance(m, r, Seq(ConformanceCondition.Equivalent(Relation.Equivalence(m, r, satisfy = true))))
                        )
                      }
                    }
                  case v: ScFieldId =>
                    val res = v.getType(TypingContext.empty)
                    if (res.isEmpty) result = (false, undefinedSubst)
                    else {
                      val inner = handler.map(_.inner)
                      result = conformsInner(l, proj2.actualSubst.subst(res.get), visited, undefinedSubst, handler = inner)
                      handler.foreach { h =>
                        val m = proj2.actualSubst.subst(res.get)
                        h + ConformanceCondition.Transitive(l, m, r,
                          Relation.Conformance(l, m, inner.get.conditions),
                          Relation.Conformance(m, r, Seq(ConformanceCondition.Equivalent(Relation.Equivalence(m, r, satisfy = true))))
                        )
                      }
                    }
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
      handler.foreach(_.visit("visitStdType - ok"))
      var rightVisitor: ScalaTypeVisitor =
        new ValDesignatorSimplification with UndefinedSubstVisitor
          with AbstractVisitor
          with ParameterizedAbstractVisitor {}
      r.visitType(rightVisitor)
      if (result != null) return

      checkEquiv()
      if (result != null) return

      rightVisitor = new ExistentialSimplification with ExistentialArgumentVisitor
        with ParameterizedExistentialArgumentVisitor with OtherNonvalueTypesVisitor {}
      r.visitType(rightVisitor)
      if (result != null) return

      if (checkWeak && r.isInstanceOf[ValType]) {
        handler.foreach(_.log("visitStdType checkWeak - skip"))
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
        handler.foreach(_ + ConformanceCondition.ToAny(x))
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
        handler.foreach(_ + ConformanceCondition.FromNothing(x))
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
          handler.foreach(_ + ConformanceCondition.BaseClass(x, r, satisfy = true))
          return
        }
      }

      if (x eq Singleton) {
        result = (false, undefinedSubst)
      }

      if (x eq AnyVal) {
        result = (r.isInstanceOf[ValType] || ValueClassType.isValueType(r), undefinedSubst)
        handler.foreach(_ + ConformanceCondition.BaseClass(x, r, satisfy = r.isInstanceOf[ValType]))
        return
      }
      if (l.isInstanceOf[ValType] && r.isInstanceOf[ValType]) {
        result = (false, undefinedSubst)
        return
      }
    }

    override def visitCompoundType(c: ScCompoundType) {
      handler.foreach(_.visit("visitCompoundType - ok"))
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
        val processor = new CompoundTypeCheckSignatureProcessor(s, retType, undefinedSubst, s.substitutor, handler = handler)
        processor.processType(r, s.namedElement)
        undefinedSubst = processor.getUndefinedSubstitutor
        processor.getResult
      }

      def workWithTypeAlias(sign: TypeAliasSignature): Boolean = {
        val processor = new CompoundTypeCheckTypeAliasProcessor(sign, undefinedSubst, ScSubstitutor.empty, handler = handler)
        processor.processType(r, sign.ta)
        undefinedSubst = processor.getUndefinedSubstitutor
        processor.getResult
      }

      handler.foreach(_.addCompound(c, r))
      result = (c.components.forall(comp => {
        val inner = handler.map(_.inner)
        val t = conformsInner(comp, r, HashSet.empty, undefinedSubst, handler = inner)
        handler.foreach(_.addRelation(Relation.Conformance(comp, r, inner.get.conditions)))
        undefinedSubst = t._2
        if (handler.nonEmpty) { if (!t._1) handler.foreach(_.corrupt()); true }
        else t._1
      }) && c.signatureMap.forall {
        case (s: Signature, retType) =>
          if (handler.nonEmpty) { if (!workWithSignature(s, retType)) handler.foreach(_.corrupt()); true }
          else workWithSignature(s, retType)
      } && c.typesMap.forall {
        case (_, sign) =>
          if (handler.nonEmpty) { if (!workWithTypeAlias(sign)) handler.foreach(_.corrupt()); true }
          else workWithTypeAlias(sign)
      }, undefinedSubst)
      handler.foreach { h =>
        h.commitCompound()
        if (h.corrupted) result = (false, undefinedSubst)
      }
    }

    override def visitProjectionType(proj: ScProjectionType) {
      handler.foreach(_.visit("visitProjectionType - ok"))
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
          val inner = handler.map(_.inner)
          result = conformsInner(projected1, projected2, visited, undefinedSubst, handler = inner)
          handler.foreach(_ + ConformanceCondition.Projection(Relation.Conformance(projected1, projected2, inner.get.conditions)))
          if (result != null) return // TODO? later will be t._1; the same block in opposite side
        case proj1: ScProjectionType if proj1.actualElement.name == proj.actualElement.name =>
          val projected1 = proj.projected
          val projected2 = proj1.projected
          val inner = handler.map(_.inner)
          val t = conformsInner(projected1, projected2, visited, undefinedSubst, handler = inner)
          handler.foreach(_ + ConformanceCondition.Projection(Relation.Conformance(projected1, projected2, inner.get.conditions)))
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
          val inner = handler.map(_.inner)
          result = conformsInner(lower.get, r, visited, undefinedSubst, handler = inner)
          handler.foreach { h =>
            val m = lower.get
            h + ConformanceCondition.Transitive(l, m, r,
              Relation.Conformance(l, m, Seq(ConformanceCondition.Equivalent(Relation.Equivalence(l, m, satisfy = true)))),
              Relation.Conformance(m, r, inner.get.conditions)
            )
          }
          return
        case _ =>
      }

      rightVisitor = new ExistentialVisitor {}
      r.visitType(rightVisitor)
      if (result != null) return
    }

    override def visitJavaArrayType(a1: JavaArrayType) {
      handler.foreach { h =>
        h.visit("visitJavaArrayType - todo")
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
      handler.foreach(_.visit(s"visitParameterizedType - todo"))

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
          var conditions1 = handler.map(_ => Seq.empty[ConformanceCondition])
          if (!upper.equiv(Any)) {
            val inner = handler.map(_.inner)
            result = conformsInner(upper, r, visited, undefinedSubst, checkWeak, handler = inner)
            handler.foreach(_ => conditions1 = inner.map(_.conditions))
          } else {
            result = (true, undefinedSubst)
            handler.foreach(_ => conditions1 = Some(Seq(ConformanceCondition.ToAny(r))))
          }
          if (result._1 || handler.nonEmpty) {
            var conditions2 = handler.map(_ => Seq.empty[ConformanceCondition])
            val lower: ScType =
              subst.subst(a.lower) match {
                case ParameterizedType(lower, _) => ScParameterizedType(lower, p.typeArguments)
                case lower => ScParameterizedType(lower, p.typeArguments)
              }
            if (!lower.equiv(Nothing)) {
              val inner = handler.map(_.inner)
              val t = conformsInner(r, lower, visited, result._2, checkWeak, handler = inner)
              handler.foreach(_ => conditions2 = inner.map(_.conditions))
              if (t._1) result = t
            }
            else handler.foreach(_ => conditions2 = Some(Seq(ConformanceCondition.FromNothing(r))))
            handler.foreach(_ + ConformanceCondition.AbstractLeft(a, r, upper, conditions1.get, lower, conditions2.get))
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
          handler.foreach(_.logn("existential argument - skip"))
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

      def processEquivalentDesignators(args2: Seq[ScType], des2: ScType): Unit = {
        val args1 = p.typeArguments
        val des1 = p.designator
        if (args1.length != args2.length) {
          handler.foreach { h =>
            h + ConformanceCondition.Parametrize(l.asInstanceOf[ScParameterizedType], r.asInstanceOf[ScParameterizedType],
              Some(Relation.Equivalence(p.designator, des2, satisfy = true)), sameLength = false, Seq()
            )
          }
          result = (false, undefinedSubst)
          return
        }
        des1.extractDesignated(expandAliases = true) match {
          case Some(ownerDesignator) =>
            val parametersIterator = ownerDesignator match {
              case td: ScTypeParametersOwner => td.typeParameters.iterator
              case ownerDesignator: PsiTypeParameterListOwner => ownerDesignator.getTypeParameters.iterator
              case _ =>
                handler.foreach { h =>
                  h + ConformanceCondition.Parametrize(l.asInstanceOf[ScParameterizedType], r.asInstanceOf[ScParameterizedType],
                    Some(Relation.Equivalence(p.designator, des2, satisfy = true)), sameLength = true, Seq()
                  )
                }
                result = (false, undefinedSubst)
                return
            }
            result = checkParameterizedType(parametersIterator, args1, args2,
                undefinedSubst, visited, checkWeak, handler = handler)
            handler.foreach { h =>
              h + ConformanceCondition.Parametrize(l.asInstanceOf[ScParameterizedType], r.asInstanceOf[ScParameterizedType],
                Some(Relation.Equivalence(p.designator, des2, satisfy = true)), sameLength = true, h.relations
              )
            }
          case _ =>
            handler.foreach { h =>
              h + ConformanceCondition.Parametrize(l.asInstanceOf[ScParameterizedType], r.asInstanceOf[ScParameterizedType],
                Some(Relation.Equivalence(p.designator, des2, satisfy = true)), sameLength = false,Seq()
              )
            }
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
                processEquivalentDesignators(args2, proj)
                return
              case _ =>
            }
          if (lower.isEmpty) { // TODO? wit
            result = (false, undefinedSubst)
            return
          }
          val inner = handler.map(_.inner)
          result = conformsInner(lower.get, r, visited, undefinedSubst, handler = inner)
          handler.foreach { h =>
            val m = lower.get
            h + ConformanceCondition.Transitive(l, m, r,
              Relation.Conformance(l, m, Seq(ConformanceCondition.Equivalent(Relation.Equivalence(l, m, satisfy = true)))),
              Relation.Conformance(m, r, inner.get.conditions)
            )
          }
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
                  handler.foreach(_ + ConformanceCondition.Parametrize(p, p2,
                    Some(Relation.Equivalence(des1, des2, satisfy = true)), sameLength = false, Seq()))
                } else {
                  result = checkParameterizedType(owner1.arguments.map(_.psiTypeParameter).iterator, args1, args2,
                    undefinedSubst, visited, checkWeak, handler = handler)
                  handler.foreach(h => h + ConformanceCondition.Parametrize(p, p2,
                    Some(Relation.Equivalence(des1, des2, satisfy = true)), sameLength = true, h.relations))
                }
              } else {
                result = (false, undefinedSubst)
                handler.foreach(_ + ConformanceCondition.Parametrize(p, p2,
                  Some(Relation.Equivalence(des1, des2, satisfy = false)), sameLength = false, Seq()))
              }
            case (_: UndefinedType, UndefinedType(parameterType, _)) =>
              (if (args1.length != args2.length) findDiffLengthArgs(l, args2.length) else Some((args1, des1))) match {
                case Some((aArgs, aType)) =>
                  undefinedSubst = undefinedSubst.addUpper(parameterType.nameAndId, aType)
                  result = checkParameterizedType(parameterType.arguments.map(_.psiTypeParameter).iterator, aArgs,
                    args2, undefinedSubst, visited, checkWeak, handler = handler)
                  handler.foreach { h => // nontransitive relation
                    h + ConformanceCondition.Parametrize(p, p2,
                      Some(Relation.Equivalence(aType, des2, satisfy = true, restriction = true)), sameLength = true,
                      h.relations
                    )
                  }
                case _ =>
                  handler.foreach(_ + ConformanceCondition.Parametrize(p, p2,
                    Some(Relation.Equivalence(des1, des2, satisfy = true, restriction = true)), sameLength = true, Seq()))
                  result = (false, undefinedSubst)
              }
            case (UndefinedType(parameterType, _), _) =>
              (if (args1.length != args2.length) findDiffLengthArgs(r, args1.length) else Some((args2, des2))) match {
                case Some((aArgs, aType)) =>
                  undefinedSubst = undefinedSubst.addLower(parameterType.nameAndId, aType)
                  result = checkParameterizedType(parameterType.arguments.map(_.psiTypeParameter).iterator, args1,
                    aArgs, undefinedSubst, visited, checkWeak, handler = handler)
                  handler.foreach { h =>
                    val parent = ScParameterizedType(aType, aArgs) match {
                      case a: ScParameterizedType => a
                      case _ => p2 // and what can i do?
                    }
                    val conformsParent = Relation.Conformance(parent, p2, Seq(ConformanceCondition.BaseClass(parent, p2,
                      satisfy = true)))
                    val conformsParameterize = Relation.Conformance(p, parent, Seq(ConformanceCondition.Parametrize(p, parent,
                      Some(Relation.Equivalence(des1, aType, satisfy = true, restriction = true)), sameLength = true,
                      h.relations
                    )))
                    h + ConformanceCondition.Transitive(p, parent, p2, conformsParameterize, conformsParent)
                  }
                case _ =>
                  result = (false, undefinedSubst)
              }
            case (_, UndefinedType(parameterType, _)) =>
              (if (args1.length != args2.length) findDiffLengthArgs(l, args2.length) else Some((args1, des1))) match {
                case Some((aArgs, aType)) =>
                  undefinedSubst = undefinedSubst.addUpper(parameterType.nameAndId, aType)
                  result = checkParameterizedType(parameterType.arguments.map(_.psiTypeParameter).iterator, aArgs,
                    args2, undefinedSubst, visited, checkWeak, handler = handler)
                  handler.foreach { h => // nontransitive relation
                    h + ConformanceCondition.Parametrize(p, p2,
                      Some(Relation.Equivalence(aType, des2, satisfy = true, restriction = true)), sameLength = true,
                      h.relations
                    )
                  }
                case _ =>
                  handler.foreach(_ + ConformanceCondition.Parametrize(p, p2,
                    Some(Relation.Equivalence(des1, des2, satisfy = true, restriction = true)), sameLength = true, Seq()))
                  result = (false, undefinedSubst)
              }
            case _ if des1 equiv des2 =>
              result =
                if (args1.length != args2.length) {
                  handler.foreach(_ + ConformanceCondition.Parametrize(p, p2,
                    Some(Relation.Equivalence(des1, des2, satisfy = true)), sameLength = false, Seq()))
                  (false, undefinedSubst)
                }
                else extractParams(des1) match {
                  case Some(params) =>
                    val inner = handler.map(_.inner)
                    val t = checkParameterizedType(params, args1, args2, undefinedSubst, visited, checkWeak, handler = inner)
                    handler.foreach(h => h + ConformanceCondition.Parametrize(p, p2,
                      Some(Relation.Equivalence(des1, des2, satisfy = true)), sameLength = true, inner.get.relations))
                    t
                  case _ =>
                    handler.foreach(_ + ConformanceCondition.Parametrize(p, p2,
                      Some(Relation.Equivalence(des1, des2, satisfy = true)), sameLength = false, Seq()))
                    (false, undefinedSubst)
                }
            case (_, t: TypeParameterType) if t.arguments.length == p2.typeArguments.length =>
              val subst = ScSubstitutor(t.arguments.zip(p.typeArguments).map {
                case (tpt: TypeParameterType, tp: ScType) => (tpt.nameAndId, tp)
              }.toMap)
              val inner = handler.map(_.inner)
              result = conformsInner(des1, subst.subst(t.upperType.v), visited, undefinedSubst, checkWeak, handler = inner)
              handler.foreach { h =>
                val m = subst.subst(t.upperType.v)
                h + ConformanceCondition.Transitive(l, m, r, Relation.Conformance(des1, m, inner.get.conditions),
                  Relation.Conformance(m, r, Seq(ConformanceCondition.TypeUpper(m, r, satisfy = true))))
              }
            case (proj1: ScProjectionType, proj2: ScProjectionType)
              if smartEquivalence(proj1.actualElement, proj2.actualElement) =>
              val t = conformsInner(proj1, proj2, visited, undefinedSubst, handler = handler.map(_.inner))
              if (!t._1) {
                handler.foreach(_ + ConformanceCondition.Parametrize(p, p2, None, sameLength = true, Seq()))
                result = (false, undefinedSubst)
              } else {
                undefinedSubst = t._2
                if (args1.length != args2.length) {
                  handler.foreach(_ + ConformanceCondition.Parametrize(p, p2,
                    Some(Relation.Equivalence(proj1, proj2, satisfy = true)), sameLength = false, Seq()))
                  result = (false, undefinedSubst)
                } else {
                  proj1.actualElement match {
                    case td: ScTypeParametersOwner =>
                      result = checkParameterizedType(td.typeParameters.iterator, args1, args2, undefinedSubst, visited, checkWeak, handler = handler)
                      handler.foreach(h => h + ConformanceCondition.Parametrize(p, p2,
                        Some(Relation.Equivalence(proj1, proj2, satisfy = true)), sameLength = true, h.relations))
                    case td: PsiTypeParameterListOwner =>
                      result = checkParameterizedType(td.getTypeParameters.iterator, args1, args2, undefinedSubst, visited, checkWeak, handler = handler)
                      handler.foreach(h => h + ConformanceCondition.Parametrize(p, p2,
                        Some(Relation.Equivalence(proj1, proj2, satisfy = true)), sameLength = true, h.relations))
                    case _ =>
                      result = (false, undefinedSubst)
                      handler.foreach(h => h + ConformanceCondition.Parametrize(p, p2,
                        Some(Relation.Equivalence(proj1, proj2, satisfy = true)), sameLength = true, Seq()))
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
            rightVisitor = new ParameterizedAliasVisitor with TypeParameterTypeVisitor {} // TODO? next step do the same
            r.visitType(rightVisitor)
          case _ =>
        }
        return
      }

      rightVisitor = new ParameterizedAliasVisitor with TypeParameterTypeVisitor {}
      r.visitType(rightVisitor)
      if (result != null) return

      r match {
        case _: JavaArrayType => // TODO?
          handler.foreach(_.logn("right is java array - skip"))
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
                handler.foreach(_.log("ScAbstractType - skip (not common)"))
                val right =
                  if (tpt.arguments.nonEmpty && !r.isInstanceOf[ScParameterizedType])
                    ScParameterizedType(r, tpt.arguments)
                  else r
                if (!upper.equiv(Any)) {
                  val t = conformsInner(upper, right, visited, undefinedSubst, checkWeak, handler = handler)
                  if (!t._1) {
                    result = (false, undefinedSubst)
                    return
                  }
                  undefinedSubst = t._2
                }
                if (!lower.equiv(Nothing)) {
                  val t = conformsInner(right, lower, visited, undefinedSubst, checkWeak, handler = handler)
                  if (!t._1) {
                    result = (false, undefinedSubst)
                    return
                  }
                  undefinedSubst = t._2
                }
              case (l, ScAbstractType(tpt, lower, upper)) =>
                handler.foreach(_.log("ScAbstractType - skip (not common)"))
                val left =
                  if (tpt.arguments.nonEmpty && !l.isInstanceOf[ScParameterizedType])
                    ScParameterizedType(l, tpt.arguments)
                  else l
                if (!upper.equiv(Any)) {
                  val t = conformsInner(upper, left, visited, undefinedSubst, checkWeak, handler = handler)
                  if (!t._1) {
                    result = (false, undefinedSubst)
                    return
                  }
                  undefinedSubst = t._2
                }
                if (!lower.equiv(Nothing)) {
                  val t = conformsInner(left, lower, visited, undefinedSubst, checkWeak, handler = handler)
                  if (!t._1) {
                    result = (false, undefinedSubst)
                    return
                  }
                  undefinedSubst = t._2
                }
              case (UndefinedType(parameterType, _), rt) =>
                // TODO?
                addBounds(parameterType, rt)
              case (lt, UndefinedType(parameterType, _)) =>
                // TODO?
                addBounds(parameterType, lt)
              case _ =>
                val t = argsPair._1.equiv(argsPair._2, undefinedSubst, falseUndef = false)
                handler.foreach(_ + ConformanceCondition.Equivalent(Relation.Equivalence(argsPair._1, argsPair._2, satisfy = t._1)))
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
          val inner = handler.map(_.inner)
          result = conformsInner(subst.subst(t.lowerType.v), r, visited, undefinedSubst, checkWeak, handler = inner)
          handler.foreach { h =>
            val m = subst.subst(t.lowerType.v)
            h + ConformanceCondition.Transitive(l, m, r,
              Relation.Conformance(l, m, Seq(ConformanceCondition.TypeLower(l, m, satisfy = true))),
              Relation.Conformance(m, r, inner.get.conditions)
            )
          }
          return
        case _ =>
      }

      rightVisitor = new AliasDesignatorVisitor with CompoundTypeVisitor with ExistentialVisitor
        with ProjectionVisitor {}
      r.visitType(rightVisitor)
      if (result != null) return
    }

    override def visitExistentialType(e: ScExistentialType) {
      handler.foreach(_.visit("visitExistentialType - todo"))
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
        result = conformsInner(simplified, r, visited, undefinedSubst, checkWeak, handler = handler)
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
      val inner = handler.map(_.inner)
      val res = conformsInner(subst.subst(q), r, HashSet.empty, undefinedSubst, handler = handler.map(_.inner))
      if (!res._1) {
        handler.foreach(_ + ConformanceCondition.ExistentialLeft(e, r, Relation.Conformance(e, r, inner.get.conditions), Seq()))
        result = (false, undefinedSubst)
      } else {
        val unSubst: ScUndefinedSubstitutor = res._2
        val sHandler = handler.map(_.substitutor)
        unSubst.getSubstitutor(notNonable = false, handler = sHandler) match {
          case Some(uSubst) => // TODO? add condition
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
          case None =>
            handler.foreach(_ + ConformanceCondition.ExistentialLeft(e, r, Relation.Conformance(e, r, inner.get.conditions), sHandler.get.result))
            result = (false, undefinedSubst)
        }
      }
    }

    override def visitThisType(t: ScThisType) {
      handler.foreach(_.visit("visitThisType - ok"))
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
      else {
        val inner = handler.map(_.inner)
        result = conformsInner(res.get, r, visited, subst, checkWeak, handler = inner)
        handler.foreach(_ + ConformanceCondition.Transitive(t, res.get, r,
          Relation.Conformance(t, res.get, Seq(ConformanceCondition.Equivalent(Relation.Equivalence(t, res.get, satisfy = true)))),
          Relation.Conformance(res.get, r, inner.get.conditions)
        ))
      }
    }

    override def visitDesignatorType(des: ScDesignatorType) {
      handler.foreach(_.visit("visitDesignatorType - ok"))
      des.getValType match {
        case Some(v) =>
          val inner = handler.map(_.inner)
          result = conformsInner(v, r, visited, subst, checkWeak, handler = inner)
          handler.foreach { h =>
            h + ConformanceCondition.Transitive(l, v, r,
              Relation.Conformance(l, v, Seq(ConformanceCondition.Equivalent(Relation.Equivalence(l, v, satisfy = true)))),
              Relation.Conformance(v, r, inner.get.conditions)
            )
          }
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
          val inner = handler.map(_.inner)
          result = conformsInner(lower.get, r, visited, undefinedSubst, handler = inner)
          handler.foreach { h =>
            val m = lower.get
            h + ConformanceCondition.Transitive(l, m, r,
              Relation.Conformance(l, m, Seq(ConformanceCondition.TypeLower(l, m, satisfy = true))),
              Relation.Conformance(m, r, inner.get.conditions)
            )
          }
          return
        case _ =>
      }

      rightVisitor = new CompoundTypeVisitor with ExistentialVisitor {}
      r.visitType(rightVisitor)
      if (result != null) return
    }

    override def visitTypeParameterType(tpt1: TypeParameterType) {
      handler.foreach(_.visit("visitTypeParameterType - ok"))
      var rightVisitor: ScalaTypeVisitor =
        new ValDesignatorSimplification with UndefinedSubstVisitor with AbstractVisitor
          with ParameterizedAbstractVisitor {}
      r.visitType(rightVisitor)
      if (result != null) return

      checkEquiv()
      if (result != null) return

      trait TypeParameterTypeNothingNullVisitor extends NothingNullVisitor {
        override def visitStdType(x: StdType) {
          handler.foreach(_.rvisit("TypeParameterTypeNothingNullVisitor - ok (multi)"))
          if (x eq Nothing) {
            handler.foreach(_ + ConformanceCondition.Transitive(l, Nothing, x,
              Relation.Conformance(l, Nothing, Seq(ConformanceCondition.FromNothing(l))),
              Relation.Conformance(Nothing, x, Seq(ConformanceCondition.Equivalent(Relation.Equivalence(Nothing, x, satisfy = true))))
            ))
            result = (true, undefinedSubst)
          }
          else if (x eq Null) {
            val inner = handler.map(_.inner)
            result = conformsInner(tpt1.lowerType.v, r, HashSet.empty, undefinedSubst, handler = inner)
            handler.foreach { h =>
              val m = tpt1.lowerType.v
              h + ConformanceCondition.Transitive(l, m, r,
                Relation.Conformance(l, m, Seq(ConformanceCondition.TypeLower(l, m, satisfy = true))),
                Relation.Conformance(m, r, inner.get.conditions)
              )
            }
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
          val inner = handler.map(_.inner)
          val res = conformsInner(tpt1.lowerType.v, r, HashSet.empty, undefinedSubst, handler = inner)
          handler.foreach { h =>
            val m = tpt1.lowerType.v
            h + ConformanceCondition.Transitive(l, m, r,
              Relation.Conformance(l, m, Seq(ConformanceCondition.TypeLower(l, m, satisfy = true))),
              Relation.Conformance(m, r, inner.get.conditions)
            )
          }
          if (res._1) {
            result = res
            return
          }
          inner.foreach(_.clean())
          result = conformsInner(l, tpt2.upperType.v, HashSet.empty, undefinedSubst, handler = inner)
          handler.foreach { h =>
            val m = tpt2.upperType.v
            h + ConformanceCondition.Transitive(l, m, r,
              Relation.Conformance(l, m, inner.get.conditions),
              Relation.Conformance(m, r, Seq(ConformanceCondition.TypeUpper(m, r, satisfy = true)))
            )
          }
          return
        case _ =>
      }

      val inner = handler.map(_.inner)
      val t = conformsInner(tpt1.lowerType.v, r, HashSet.empty, undefinedSubst, handler = inner)
      handler.foreach { h =>
        val m = tpt1.lowerType.v
        h + ConformanceCondition.Transitive(l, m, r,
          Relation.Conformance(l, m, Seq(ConformanceCondition.TypeLower(l, m, satisfy = true))),
          Relation.Conformance(m, r, inner.get.conditions)
        )
      }
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
      handler.foreach(_.visit("visitExistentialArgument - ok"))
      var rightVisitor: ScalaTypeVisitor =
        new ValDesignatorSimplification with UndefinedSubstVisitor
          with AbstractVisitor
          with ParameterizedAbstractVisitor {}
      r.visitType(rightVisitor)
      if (result != null) return

      checkEquiv()
      if (result != null) return

      val inner = handler.map(_.inner)
      val t = conformsInner(s.lower, r, HashSet.empty, undefinedSubst, handler = inner)
      handler.foreach(_ + ConformanceCondition.Transitive(s, s.lower, r,
        Relation.Conformance(s, s.lower, Seq(ConformanceCondition.TypeLower(s, s.lower, satisfy = true))),
        Relation.Conformance(s.lower, r, inner.get.conditions)
      ))

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
      handler.foreach(_.visit("visitUndefinedType - skip"))
      val rightVisitor = new ValDesignatorSimplification {
        override def visitUndefinedType(u2: UndefinedType) {
          val name = u2.parameterType.nameAndId
          result = (true, if (u2.level > u.level) {
            handler.foreach(_ + ConformanceCondition.Undefined(u2, u, u2)) // TODO?
            undefinedSubst.addUpper(name, u)
          } else if (u.level > u2.level) {
            handler.foreach(_ + ConformanceCondition.Undefined(u2, u, u2)) // TODO?
            undefinedSubst.addUpper(name, u) // TODO? really?
          } else {
            handler.foreach(_ + ConformanceCondition.Undefined(u2, u, u2)) // TODO?
            undefinedSubst
          })
        }
      }
      r.visitType(rightVisitor)
      if (result == null) {
        handler.foreach(_ + ConformanceCondition.Undefined(r, u, r)) // TODO?
        result = (true, undefinedSubst.addLower(u.parameterType.nameAndId, r))
      }
    }

    override def visitMethodType(m1: ScMethodType) {
      handler.foreach(_.visit("visitMethodType - ok"))
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
            handler.foreach(_ + ConformanceCondition.Method(m1, m2, sameLen = false, None, Seq()))
            result = (false, undefinedSubst)
            return
          }

          val inner = handler.map(_.inner)
          var t = conformsInner(returnType1, returnType2, HashSet.empty, undefinedSubst, handler = inner)
          if (!t._1) {
            handler.foreach(_ + ConformanceCondition.Method(m1, m2, sameLen = true,
              Some(Relation.Conformance(returnType1, returnType2, inner.get.conditions)), Seq()))
            result = (false, undefinedSubst)
            return
          }
          undefinedSubst = t._2
          var i = 0
          while (i < params1.length) {
            if (params1(i).isRepeated != params2(i).isRepeated) {
              result = (false, undefinedSubst)
              if (handler.nonEmpty) handler.foreach(_.corrupt())
              else return
            }
            t = params1(i).paramType.equiv(params2(i).paramType, undefinedSubst, falseUndef = false)
            handler.foreach { h =>
              val p1 = params1(i)
              val p2 = params2(i)
              h + ConformanceCondition.Invariant(p1.name,
                Relation.Equivalence(p1.paramType, p2.paramType, t._1 && p1.isRepeated != p2.isRepeated))
            }
            if (!t._1) {
              result = (false, undefinedSubst)
              if (handler.nonEmpty) handler.foreach(_.corrupt())
              else return
            }
            undefinedSubst = t._2
            i = i + 1
          }
          handler.foreach(h => h + ConformanceCondition.Method(m1, m2, sameLen = true,
            Some(Relation.Conformance(returnType1, returnType2, inner.get.conditions)),
            h.relations.collect { case cc: ConformanceCondition.Invariant => cc }
          ))
          if (handler.nonEmpty) if (handler.exists(_.corrupted)) { // TODO? interesting construction, need to change macros
            result = (false, undefinedSubst)
            return
          }
          result = (true, undefinedSubst)
        case _ =>
          result = (false, undefinedSubst)
      }
    }

    override def visitAbstractType(a: ScAbstractType) {
      handler.foreach(_.visit(s"visitAbstractType - ??? ($a, ${a.upper} ${a.lower})"))
      val rightVisitor = new ValDesignatorSimplification with UndefinedSubstVisitor {}
      r.visitType(rightVisitor)
      if (result != null) return
      val right =
        if (a.parameterType.arguments.nonEmpty && !r.isInstanceOf[ScParameterizedType])
          ScParameterizedType(r, a.parameterType.arguments)
        else r

      val inner = handler.map(_.inner)
      result = conformsInner(a.upper, right, visited, undefinedSubst, checkWeak, handler = inner) // TODO? has opposite analog but much simplier
//      handler.foreach { h => ???
////        h + ConformanceCondition.AbstractLeft(a, right, satisfy = result._1)
//      }
      if (result._1) {
        val t = conformsInner(right, a.lower, visited, result._2, checkWeak, handler = handler.map(_.inner))
        if (t._1) result = t // TODO? why is optional?
      }
    }

    override def visitTypePolymorphicType(t1: ScTypePolymorphicType) {
      handler.foreach(_.visit("visitTypePolymorphicType - ok"))
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
            handler.foreach(_ + ConformanceCondition.Polymorphic(internalType1, internalType2, sameLength = false, Seq(), None))
            return
          }
          var i = 0
          var argPairs: Option[Seq[(Relation.Conformance, Relation.Conformance)]] = handler.map(_ => Seq.empty)
          while (i < typeParameters1.length) {
            val inner1 = handler.map(_.inner)
            var t = conformsInner(typeParameters1(i).lowerType.v, typeParameters2(i).lowerType.v, HashSet.empty, undefinedSubst, handler = inner1)
            if (!t._1) {
              result = (false, undefinedSubst)
              if (handler.nonEmpty) handler.foreach(_.corrupt())
              else return
            }
            undefinedSubst = t._2
            val inner2 = handler.map(_.inner)
            t = conformsInner(typeParameters2(i).upperType.v, typeParameters1(i).lowerType.v, HashSet.empty, undefinedSubst, handler = inner2)
            if (!t._1) {
              result = (false, undefinedSubst)
              if (handler.nonEmpty) handler.foreach(_.corrupt())
              else return
            }
            handler.foreach(_ => argPairs = argPairs.map(_ :+
              (Relation.Conformance(typeParameters1(i).lowerType.v, typeParameters2(i).lowerType.v, inner1.get.conditions),
              Relation.Conformance(typeParameters2(i).upperType.v, typeParameters1(i).lowerType.v, inner2.get.conditions))))
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
          val inner = handler.map(_.inner)
          val t = conformsInner(subst.subst(internalType1), internalType2, HashSet.empty, undefinedSubst, handler = inner)
          handler.foreach(_ + ConformanceCondition.Polymorphic(internalType1, internalType2, sameLength = true, argPairs.get,
            Some(Relation.Conformance(subst.subst(internalType1), internalType2, inner.get.conditions))))
          if (!t._1) {
            result = (false, undefinedSubst)
            return
          }
          undefinedSubst = t._2
          if (handler.nonEmpty) if (handler.exists(_.corrupted)) { // TODO? interesting construction, need to change macros
            result = (false, undefinedSubst)
            return
          }
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

  @uninstrumental("handler")
  def addParam(parameterType: TypeParameterType, bound: ScType, undefinedSubst: ScUndefinedSubstitutor,
               defArgs: Seq[ScType], undefArgs: Seq[ScType], handler: Option[DCHandler.Conformance] = None): (Boolean, ScUndefinedSubstitutor) =
    addArgedBound(parameterType, bound, undefinedSubst, defArgs, undefArgs, variance = 0, addUpper = true, addLower = true, handler)

  @uninstrumental("handler")
  def addArgedBound(parameterType: TypeParameterType, bound: ScType, undefinedSubst: ScUndefinedSubstitutor,
                    defArgs: Seq[ScType], undefArgs: Seq[ScType], variance: Int = 1,
                    addUpper: Boolean = false, addLower: Boolean = false, handler: Option[DCHandler.Conformance]): (Boolean, ScUndefinedSubstitutor) = {
    handler.foreach(_.logn("addArgedBound - skip"))
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
