package org.jetbrains.plugins.scala.lang.psi.types

import org.jetbrains.plugins.dotty.lang.psi.types.DottyTypeSystem
import org.jetbrains.plugins.scala.actions.{DCHandler, DebugConformanceAction}
import org.jetbrains.plugins.scala.lang.psi.types.api._
import org.jetbrains.plugins.scala.macroAnnotations.uninstrumental

sealed trait ScUndefinedSubstitutor {

  type Name = (String, Long)

  case class SubstitutorWithBounds(subst: ScSubstitutor, lowers: Map[Name, ScType], upper: Map[Name, ScType])

  def addLower(name: Name, _lower: ScType, additional: Boolean = false, variance: Int = -1): ScUndefinedSubstitutor
  def addUpper(name: Name, _upper: ScType, additional: Boolean = false, variance: Int = 1): ScUndefinedSubstitutor

  //@uninstrumental("handler")
  def getSubstitutor(notNonable: Boolean, handler: Option[DCHandler.Substitutor] = None): Option[ScSubstitutor] =
    getSubstitutorWithBounds(notNonable, handler = handler).map(_._1)
  def getSubstitutor: Option[ScSubstitutor] = getSubstitutor(notNonable = false)
  def filter(fun: (((String, Long), Set[ScType])) => Boolean): ScUndefinedSubstitutor
  def addSubst(added: ScUndefinedSubstitutor): ScUndefinedSubstitutor
  def +(subst: ScUndefinedSubstitutor): ScUndefinedSubstitutor = addSubst(subst)
  def isEmpty: Boolean
  def names: Set[Name]

  //subst, lowers, uppers
  //@uninstrumental("handler")
  def getSubstitutorWithBounds(notNonable: Boolean, handler: Option[DCHandler.Substitutor] = None): Option[(ScSubstitutor, Map[Name, ScType], Map[Name, ScType])]
}

object ScUndefinedSubstitutor {
  def apply(upperMap: Map[(String, Long), Set[ScType]] = Map.empty,
            lowerMap: Map[(String, Long), Set[ScType]] = Map.empty,
            upperAdditionalMap: Map[(String, Long), Set[ScType]] = Map.empty,
            lowerAdditionalMap: Map[(String, Long), Set[ScType]] = Map.empty)
           (implicit typeSystem: TypeSystem): ScUndefinedSubstitutor = {

    new ScUndefinedSubstitutorImpl(upperMap, lowerMap, upperAdditionalMap, lowerAdditionalMap)(typeSystem)
  }

  def apply()(implicit typeSystem: TypeSystem): ScUndefinedSubstitutor = {
    if (typeSystem eq ScalaTypeSystem) emptyScala
    else if (typeSystem eq DottyTypeSystem) emptyDotty
    else new ScUndefinedSubstitutorImpl()
  }

  def multi(subs: Seq[ScUndefinedSubstitutor]) = new ScMultiUndefinedSubstitutor(subs)

  private val emptyScala = new ScUndefinedSubstitutorImpl()(ScalaTypeSystem)
  private val emptyDotty = new ScUndefinedSubstitutorImpl()(DottyTypeSystem)
}

private class ScUndefinedSubstitutorImpl(val upperMap: Map[(String, Long), Set[ScType]] = Map.empty,
                                         val lowerMap: Map[(String, Long), Set[ScType]] = Map.empty,
                                         val upperAdditionalMap: Map[(String, Long), Set[ScType]] = Map.empty,
                                         val lowerAdditionalMap: Map[(String, Long), Set[ScType]] = Map.empty)
                                        (implicit typeSystem: TypeSystem)
  extends ScUndefinedSubstitutor {


  override def toString: String = upperMap.toString() + lowerMap.toString() + upperAdditionalMap.toString() + lowerAdditionalMap

  def copy(upperMap: Map[(String, Long), Set[ScType]] = upperMap,
           lowerMap: Map[(String, Long), Set[ScType]] = lowerMap,
           upperAdditionalMap: Map[(String, Long), Set[ScType]] = upperAdditionalMap,
           lowerAdditionalMap: Map[(String, Long), Set[ScType]] = lowerAdditionalMap): ScUndefinedSubstitutor = {
    ScUndefinedSubstitutor(upperMap, lowerMap, upperAdditionalMap, lowerAdditionalMap)
  }

  def isEmpty: Boolean = upperMap.isEmpty && lowerMap.isEmpty && upperAdditionalMap.isEmpty && lowerAdditionalMap.isEmpty

  //todo: this is can be rewritten in more fast way
  def addSubst(added: ScUndefinedSubstitutor): ScUndefinedSubstitutor = {
    added match {
      case subst: ScUndefinedSubstitutorImpl =>
        var res: ScUndefinedSubstitutor = this
        for ((name, seq) <- subst.upperMap) {
          for (upper <- seq) {
            res = res.addUpper(name, upper, variance = 0)
          }
        }
        for ((name, seq) <- subst.lowerMap) {
          for (lower <- seq) {
            res = res.addLower(name, lower, variance = 0)
          }
        }

        for ((name, seq) <- subst.upperAdditionalMap) {
          for (upper <- seq) {
            res = res.addUpper(name, upper, additional = true, variance = 0)
          }
        }
        for ((name, seq) <- subst.lowerAdditionalMap) {
          for (lower <- seq) {
            res = res.addLower(name, lower, additional = true, variance = 0)
          }
        }

        res
      case subst: ScMultiUndefinedSubstitutor =>
        subst.addSubst(this)
    }
  }

  def addLower(name: Name, _lower: ScType, additional: Boolean = false, variance: Int = -1): ScUndefinedSubstitutor = {
    var index = 0
    val lower = (_lower match {
      case ScAbstractType(_, absLower, _) =>
        if (absLower.equiv(Nothing)) return this
        absLower //upper will be added separately
      case _ =>
        _lower.recursiveVarianceUpdateModifiable[Set[String]](Set.empty, {
          case (ScAbstractType(_, absLower, upper), i, data) =>
            i match {
              case -1 => (true, absLower, data)
              case 1 => (true, upper, data)
              case 0 => (true, absLower/*ScExistentialArgument(s"_$$${index += 1; index}", Nil, absLower, upper)*/, data) //todo: why this is right?
            }
          case (ScExistentialArgument(nm, _, skoLower, upper), i, data) if !data.contains(nm) =>
            i match {
              case -1 => (true, skoLower, data)
              case 1 => (true, upper, data)
              case 0 => (true, ScExistentialArgument(s"_$$${index += 1; index}", Nil, skoLower, upper), data)
            }
          case (ex: ScExistentialType, _, data) => (false, ex, data ++ ex.boundNames)
          case (tp, _, data) => (false, tp, data)
        }, variance)
    }).unpackedType
    val lMap = if (additional) lowerAdditionalMap else lowerMap
    lMap.get(name) match {
      case Some(set: Set[ScType]) =>
        if (additional) copy(lowerAdditionalMap = lMap.updated(name, set + lower))
        else copy(lowerMap = lMap.updated(name, set + lower))
      case None =>
        if (additional) copy(lowerAdditionalMap = lMap + ((name, Set(lower))))
        else copy(lowerMap = lMap + ((name, Set(lower))))
    }
  }

  def addUpper(name: Name, _upper: ScType, additional: Boolean = false, variance: Int = 1): ScUndefinedSubstitutor = {
    var index = 0
    val upper =
      (_upper match {
        case ScAbstractType(_, _, absUpper) if variance == 0 =>
          if (absUpper.equiv(Any)) return this
          absUpper // lower will be added separately
        case ScAbstractType(_, _, absUpper) if variance == 1 && absUpper.equiv(Any) => return this
        case _ =>
          _upper.recursiveVarianceUpdateModifiable[Set[String]](Set.empty, {
            case (ScAbstractType(_, lower, absUpper), i, data) =>
              i match {
                case -1 => (true, lower, data)
                case 1 => (true, absUpper, data)
                case 0 => (true, ScExistentialArgument(s"_$$${index += 1; index}", Nil, lower, absUpper), data) //todo: why this is right?
              }
            case (ScExistentialArgument(nm, _, lower, skoUpper), i, data) if !data.contains(nm) =>
              i match {
                case -1 => (true, lower, data)
                case 1 => (true, skoUpper, data)
                case 0 => (true, ScExistentialArgument(s"_$$${index += 1; index}", Nil, lower, skoUpper), data)
              }
            case (ex: ScExistentialType, _, data) => (false, ex, data ++ ex.boundNames)
            case (tp, _, data) => (false, tp, data)
          }, variance)
      }).unpackedType
    val uMap = if (additional) upperAdditionalMap else upperMap
    uMap.get(name) match {
      case Some(set: Set[ScType]) =>
        if (additional) copy(upperAdditionalMap = uMap.updated(name, set + upper))
        else copy(upperMap = uMap.updated(name, set + upper))
      case None =>
        if (additional) copy(upperAdditionalMap = uMap + ((name, Set(upper))))
        else copy(upperMap = uMap + ((name, Set(upper))))
    }
  }

  lazy val additionalNames: Set[Name] = {
    //We need to exclude Nothing names from this set, see SCL-5736
    lowerAdditionalMap.filter(_._2.exists(!_.equiv(Nothing))).keySet ++ upperAdditionalMap.keySet
  }

  lazy val names: Set[Name] = {
    //We need to exclude Nothing names from this set, see SCL-5736
    upperMap.keySet ++ lowerMap.filter(_._2.exists(!_.equiv(Nothing))).keySet ++ additionalNames
  }

  //@uninstrumental("handler")
  def getSubstitutorWithBounds(notNonable: Boolean, handler: Option[DCHandler.Substitutor] = None): Option[(ScSubstitutor, Map[Name, ScType], Map[Name, ScType])] = {
    var tvMap = Map.empty[Name, ScType]
    var lMap = Map.empty[Name, ScType]
    var uMap = Map.empty[Name, ScType]

    handler.foreach { h =>
      h.log("getSubstitutorWithBounds for:")
      h.logn(names.mkString(", "))
    }

    def solve(name: Name, visited: Set[Name]): Option[ScType] = {
      if (visited.contains(name)) {
        tvMap += ((name, Nothing))
        return None
      }
      handler.foreach { h =>
        h.log(s"find solution fore type variable $name")
        h + name
      }
      tvMap.get(name) match {
        case Some(tp) => Some(tp)
        case _ =>
          (lowerMap.get(name).map(set => lowerAdditionalMap.get(name) match {
            case Some(set1) => set ++ set1
            case _ => set
          }) match {
            case Some(set) => Some(set)
            case _ => lowerAdditionalMap.get(name)
          }) match {
            case Some(set) =>
              handler.foreach { h =>
                h.log(s"it should be <: $set")
                h.addLowers(set)
              }
              var res = false
              def checkRecursive(tp: ScType): Boolean = {
                tp.recursiveUpdate {
                  case tpt: TypeParameterType =>
                    handler.foreach { h =>
                      h.log("checkRecursive - typePatameterType - skip")
                    }
                    val otherName = tpt.nameAndId
                    if (additionalNames.contains(otherName)) {
                      res = true
                      solve(otherName, visited + name) match {
                        case None if !notNonable => return false
                        case _ =>
                      }
                    }
                    (false, tpt)
                  case UndefinedType(tpt, _) =>
                    handler.foreach { h =>
                      h.log("checkRecursive - undefinedType - skip")
                    }
                    val otherName = tpt.nameAndId
                    if (names.contains(otherName)) {
                      res = true
                      solve(otherName, visited + name) match {
                        case None if !notNonable => return false
                        case _ =>
                      }
                    }
                    (false, tpt)
                  case tp: ScType => (false, tp)
                }
                true
              }
              val seqIterator = set.iterator
              while (seqIterator.hasNext) {
                val p = seqIterator.next()
                if (!checkRecursive(p)) {
                  handler.foreach { h =>
                    h.log("!checkRecursive")
                  }
                  tvMap += ((name, Nothing))
                  return None
                }
              }
              if (set.nonEmpty) { // TODO? in lower more cases
                val subst = if (res) ScSubstitutor(tvMap) else ScSubstitutor.empty
                var lower: ScType = Nothing
                val setIterator = set.iterator
                while (setIterator.hasNext) {
                  lower = lower.lub(subst.subst(setIterator.next()), checkWeak = true) // TODO? where is dependence on previous substitutions?
                }
                handler.foreach { h =>
                  h.log(s"lower type is $lower")
                }
                lMap += ((name, lower))
                tvMap += ((name, lower))
              }
            case None =>
          }
          (upperMap.get(name).map(set => upperAdditionalMap.get(name) match {
            case Some(set1) => set ++ set1
            case _ => set
          }) match {
            case Some(set) => Some(set)
            case _ => upperAdditionalMap.get(name)
          }) match {
            case Some(set) =>
              handler.foreach { h =>
                h.log(s"it should be >: $set")
                h.addUppers(set)
              }
              var res = false
              def checkRecursive(tp: ScType): Boolean = {
                tp.recursiveUpdate {
                  case tpt: TypeParameterType =>
                    handler.foreach { h =>
                      h.log("checkRecursive - typeParameterType - skip")
                    }
                    val otherName = tpt.nameAndId
                    if (additionalNames.contains(otherName)) {
                      res = true
                      solve(otherName, visited + name) match {
                        case None if !notNonable => return false
                        case _ =>
                      }
                    }
                    (false, tpt)
                  case UndefinedType(tpt, _) =>
                    handler.foreach { h =>
                      h.log("checkRecursive - undefinedType - skip")
                    }
                    val otherName = tpt.nameAndId
                    if (names.contains(otherName)) {
                      res = true
                      solve(otherName, visited + name) match {
                        case None if !notNonable => return false
                        case _ =>
                      }
                    }
                    (false, tpt)
                  case tp: ScType => (false, tp)
                }
                true
              }
              val seqIterator = set.iterator
              while (seqIterator.hasNext) {
                val p = seqIterator.next()
                if (!checkRecursive(p)) {
                  handler.foreach { h =>
                    h.log("!checkRecursive")
                  }
                  tvMap += ((name, Nothing))
                  return None
                }
              }
              if (set.nonEmpty) {
                var uType: ScType = Nothing
                val subst = if (res) ScSubstitutor(tvMap) else ScSubstitutor.empty
                val size: Int = set.size
                if (size == 1) {
                  uType = subst.subst(set.iterator.next())
                  handler.foreach { h =>
                    h.log(s"upper type is $uType")
                  }
                  uMap += ((name, uType))
                } else if (size > 1) {
                  var upper: ScType = Any
                  val setIterator = set.iterator
                  while (setIterator.hasNext) {
                    upper = upper.glb(subst.subst(setIterator.next()), checkWeak = false)
                  }
                  handler.foreach { h =>
                    h.log(s"upper type is $upper")
                  }
                  uType = upper
                  uMap += ((name, uType))
                }
                tvMap.get(name) match {
                  case Some(lower) =>
                    if (!notNonable) {
                      val seqIterator = set.iterator
                      while (seqIterator.hasNext) {
                        val upper = seqIterator.next()
                        if (!lower.conforms(subst.subst(upper))) { // TODO? it is good that we calculated uType for this case
                          handler.foreach(_.logn("!(lower <: uppers)"))
                          return None
                        }
                      }
                    }
                  case None =>
                    handler.foreach(_.addType(uType))
                    handler.foreach(_.logn(s"took lowest of upers $uType"))
                    tvMap += ((name, uType))
                }
              }
            case None =>
          }

          if (tvMap.get(name).isEmpty) {
            handler.foreach(_.logn(s"no restrictions - `Nothing` instead"))
            handler.foreach(_.addType(Nothing))
            tvMap += ((name, Nothing))
          } else {
            handler.foreach(_.addType(tvMap(name)))
            handler.foreach(_.logn(s"took ${tvMap(name)}"))
            () // TODO? bug in uninstrumental
          }
          tvMap.get(name)
      }
    }
    val namesIterator = names.iterator
    while (namesIterator.hasNext) {
      val name = namesIterator.next()
      solve(name, Set.empty) match {
        case Some(_) => // do nothing
        case None if !notNonable => return None
        case _ =>
      }
    }
    val subst = ScSubstitutor(tvMap)
    Some((subst, lMap, uMap))
  }

  def filter(fun: (((String, Long), Set[ScType])) => Boolean): ScUndefinedSubstitutor = {
    ScUndefinedSubstitutor(
      upperMap.filter(fun),
      lowerMap.filter(fun),
      upperAdditionalMap.filter(fun),
      lowerAdditionalMap.filter(fun))
  }
}

class ScMultiUndefinedSubstitutor(val subs: Seq[ScUndefinedSubstitutor]) extends ScUndefinedSubstitutor {
  def copy(subs: Seq[ScUndefinedSubstitutor]) = new ScMultiUndefinedSubstitutor(subs)

  override def addLower(name: (String, Long), _lower: ScType, additional: Boolean, variance: Int): ScUndefinedSubstitutor =
    copy(subs.map(_.addLower(name, _lower, additional, variance)))

  override def addUpper(name: (String, Long), _upper: ScType, additional: Boolean, variance: Int): ScUndefinedSubstitutor =
    copy(subs.map(_.addUpper(name, _upper, additional, variance)))

  //@uninstrumental("handler")
  override def getSubstitutorWithBounds(notNonable: Boolean, handler: Option[DCHandler.Substitutor] = None): Option[(ScSubstitutor, Map[Name, ScType], Map[Name, ScType])] =
    subs.map(_.getSubstitutorWithBounds(notNonable)).find(_.isDefined).getOrElse(None)

  override def filter(fun: (((String, Long), Set[ScType])) => Boolean): ScUndefinedSubstitutor =
    copy(subs.map(_.filter(fun)))

  override def addSubst(added: ScUndefinedSubstitutor): ScUndefinedSubstitutor = copy(subs.map(_.addSubst(added)))

  override def isEmpty: Boolean = subs.forall(_.isEmpty)

  override def names: Set[(String, Long)] = if (subs.isEmpty) Set.empty else subs.tail.map(_.names).
    foldLeft(subs.head.names){case (a, b) => a.intersect(b)}
}