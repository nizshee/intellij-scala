package org.jetbrains.plugins.scala.actions.debug_types

import com.intellij.psi.PsiNamedElement
import org.jetbrains.plugins.scala.actions._
import org.jetbrains.plugins.scala.lang.psi.types.api.{Any, Nothing}
import org.jetbrains.plugins.scala.lang.psi.types.{ScCompoundType, ScType, ScUndefinedSubstitutor, ScalaTypeSystem, Signature, TypeAliasSignature}
import org.jetbrains.plugins.scala.lang.resolve.ScalaResolveResult

/**
  * Created by user on 4/10/17.
  */
protected class DTHandler(delimeter: String, debug: Boolean) {
  private var _corrupted: Boolean = false

  def corrupt(): Unit = _corrupted = true

  def corrupted: Boolean = _corrupted

  def clean(): Unit = _corrupted = false

  def log(any: Any): Unit = if (debug) println(delimeter + any)
  def logn(any: Any): Unit = if (debug) {
    println(delimeter + any)
    println()
  }
}

object DTHandler {

  class Conformance(delimeter: String, debug: Boolean) extends DTHandler(delimeter, debug) {

    private var _compound: Option[CCondition.CompoundLeft] = None
    private var _conditions: Seq[CCondition] = Seq()
    private var _variances: Seq[CCondition.Variance] = Seq()

    def addCompound(compound: ScCompoundType, right: ScType): Unit = _compound =
      Some(CCondition.CompoundLeft(compound, right, Map(), Map(), Seq()))

    def addAlias(name: String, sign: TypeAliasSignature, el: PsiNamedElement): Unit = _compound match {
      case Some(x) => _compound = Some(x.copy(aliases = x.aliases.updated(name -> sign, el)))
      case None =>
    }

    def addSignature(sign: Signature, ty: ScType, el: PsiNamedElement): Unit = _compound match {
      case Some(x) => _compound = Some(x.copy(signatures = x.signatures.updated(sign -> ty, el)))
      case None =>
    }

    def addRelation(conformance: Relation.Conformance): Unit = _compound match {
      case Some(x) => _compound = Some(x.copy(relations = x.relations :+ conformance))
      case None =>
    }

    def commitCompound(): Unit = _compound match {
      case Some(x) => this + x
      case None =>
    }

    def +(condition: CCondition): CCondition = {
      _conditions :+= condition
      condition
    }

    def +(variance: CCondition.Variance): Unit = {
      _variances :+= variance
    }

    def conditions: Seq[CCondition] = _conditions

    def relations: Seq[CCondition.Variance] = _variances

    def logt(left: ScType, right: ScType): Unit = {
      log(s"left: ${left.presentableText}")
      log(s"right: ${right.presentableText}")
    }

    def logtn(left: ScType, right: ScType): Unit = {
      log(s"left: ${left.presentableText}")
      logn(s"right: ${right.presentableText}")
    }

    def visit(any: Any): Unit = {
      logn("visit " + any)
    }

    def rvisit(any: Any): Unit = {
      logn("right visit " + any)
    }

    override def clean(): Unit = {
      super.clean()
      _compound = None
      _conditions = Seq.empty
      _variances = Seq.empty
    }


    def inner: Conformance = new Conformance(delimeter + "|", debug)

    def substitutor: Substitutor = new Substitutor(delimeter + "s|", debug)
  }


  class Compatibility(delimeter: String, debug: Boolean) extends DTHandler(delimeter, debug) {
    case class Arg(name: String,
                   expectedType: ScType,
                   actualType: ScType,
                   conditions: Seq[CCondition]) {
      def satisfy: Boolean = conditions.exists(_.satisfy)
    }


    private var _args: Seq[Arg] = Seq()
    def +(arg: Arg): Arg = {
      _args :+= arg
      arg
    }

    def handler: DTHandler.Conformance = new DTHandler.Conformance(delimeter + "r|", debug)

    def args: Seq[Arg] = _args

    def logCase(any: Any): Unit = {
      logn("case - " + any)
    }
  }

  class Substitutor(delimeter: String, debug: Boolean) extends DTHandler(delimeter, debug) {
    case class Restriction(name: (String, Long),
                           `type`: Option[ScType],
                           uppers: Set[ScType],
                           lowers: Set[ScType])

    private var _restrictions: Seq[Restriction] = Seq.empty
    private var _follows: Seq[Seq[Substitutor#Restriction]] = Seq.empty

    private var _upperBound: ScType = Any
    private var _lowerBound: ScType = Nothing

    def addUpperBound(bound: ScType): Unit = _upperBound = bound
    def addLowerBound(bound: ScType): Unit = _lowerBound = bound
    def upperBound: ScType = _upperBound
    def lowerBound: ScType = _lowerBound

    def +(follow: Seq[Substitutor#Restriction]): Unit = {
      _follows :+= follow
    }

    def +(name: (String, Long)): Restriction = {
      val restriction = Restriction(name, None, Set.empty, Set.empty)
      _restrictions = restriction +: _restrictions
      restriction
    }

    def addLowers(lowers: Set[ScType]): Unit = {
      _restrictions.headOption match {
        case Some(restriction) =>
          _restrictions = restriction.copy(lowers = lowers) +: _restrictions.tail
        case _ =>
      }
    }

    def addUppers(uppers: Set[ScType]): Unit = {
      _restrictions.headOption match {
        case Some(restriction) =>
          _restrictions = restriction.copy(uppers = uppers) +: _restrictions.tail
        case _ =>
      }
    }

    def addType(`type`: ScType): Unit = {
      _restrictions.headOption match {
        case Some(restriction) =>
          _restrictions = restriction.copy(`type` = Some(`type`)) +: _restrictions.tail
        case _ =>
      }
    }

    def inner: Substitutor = new Substitutor(delimeter + "|", debug)

    def result: Seq[Seq[Substitutor#Restriction]] =
      if (_follows.nonEmpty) _follows else Seq(_restrictions)
  }

  class Resolver(delimter: String, debug: Boolean) extends DTHandler(delimter, debug) {

    case class Weight(opposite: Int, asSpecificAs: Option[AsSpecificAsCondition], derived: Option[Derived.type]) {
      def wins: Boolean = opposite < v
      def v: Int = asSpecificAs.map(v => if (v.satisfy) 1 else 0).getOrElse(0) + derived.map(_ => 1).getOrElse(0)
    }
    case class Candidate(rr: Option[ScalaResolveResult],
                         weights: Map[PsiNamedElement, Weight],
                         args: Seq[Compatibility#Arg],
                         restrictions: Seq[Seq[Substitutor#Restriction]],
                         defaultInterfere: Boolean = false,
                         wrongNameArguments: Set[String] = Set.empty)
    case class Ret(expextedType: ScType,
                   actualType: ScType,
                   conditions: Seq[CCondition],
                   subs: ScUndefinedSubstitutor)

    private var _last: Option[PsiNamedElement] = None
    private var _candidates: Map[PsiNamedElement, Candidate] = Map.empty
    private var _elementMap: Map[PsiNamedElement, PsiNamedElement] = Map.empty
    private var _ret: Option[Ret] = None

    def +(ret: Ret): Unit = _ret = Some(ret)

    def ret: Option[Ret] = _ret

    def subst: ScUndefinedSubstitutor = _ret match {
      case Some(x) => x.subs
      case None => ScUndefinedSubstitutor()(ScalaTypeSystem)
    }

    private def resolve(el: PsiNamedElement) = _elementMap.getOrElse(el, el)

    def addMapping(el1: PsiNamedElement, el2: PsiNamedElement): Unit = _elementMap += el1 -> el2

    def +(el: PsiNamedElement): Candidate = {
      val candidate = Candidate(None, Map.empty, Seq.empty, Seq.empty)
      _last = Some(el)
      _candidates += el -> candidate
      candidate
    }

    def +(rr: ScalaResolveResult): Unit = {
      _last.flatMap(el => _candidates.get(el).map(el -> _)) match {
        case Some((el, candidate)) =>
          _candidates += el -> candidate.copy(rr = Some(rr))
        case _ =>
      }
    }

    def defaultInterfere(element: PsiNamedElement): Unit = {
      _candidates.get(element).map(element -> _) match {
        case Some((el, candidate)) =>
          _candidates += el -> candidate.copy(defaultInterfere = true)
        case _ =>
      }
    }

    def wrongArgument(element: PsiNamedElement, paramter: String): Unit = {
      _candidates.get(element).map(element -> _) match {
        case Some((el, candidate)) =>
          _candidates += el -> candidate.copy(wrongNameArguments = candidate.wrongNameArguments + paramter)
        case _ =>
      }
    }

    def addRestrictions(restrictions: Seq[Seq[Substitutor#Restriction]]): Unit = {
      _last.flatMap(el => _candidates.get(el).map(el -> _)) match {
        case Some((el, candidate)) =>
          _candidates += el -> candidate.copy(restrictions = restrictions)
        case None =>
      }
    }

    def +(args: Seq[DTHandler.Compatibility#Arg]): Unit = {
      _last.flatMap(el => _candidates.get(el).map(el -> _)) match {
        case Some((el, candidate)) =>
          _candidates += el -> candidate.copy(args = args)
        case None =>
      }
    }

    def addWeight(left: PsiNamedElement, right: PsiNamedElement, asSpecificAs: AsSpecificAsCondition): Unit = {
      val _left = resolve(left)
      val _right = resolve(right)
      val candidate = _candidates.getOrElse(_left, Candidate(None, Map.empty, Seq.empty, Seq.empty))
      val weight = candidate.weights.getOrElse(_right, Weight(0, None, None))
      _candidates += _left -> candidate.copy(
        weights = candidate.weights.updated(_right, weight.copy(asSpecificAs = Some(asSpecificAs)))
      )
    }

    def addDerived(left: PsiNamedElement, right: PsiNamedElement): Unit = {
      val _left = resolve(left)
      val _right = resolve(right)
      val candidate = _candidates.getOrElse(_left, Candidate(None, Map.empty, Seq.empty, Seq.empty))
      val weight = candidate.weights.getOrElse(_right, Weight(0, None, None))
      _candidates += _left -> candidate.copy(
        weights = candidate.weights.updated(_right, weight.copy(derived = Some(Derived)))
      )

      val rCandidate = _candidates.getOrElse(_right, Candidate(None, Map.empty, Seq.empty, Seq.empty))
      val rWeight = rCandidate.weights.getOrElse(_left, Weight(0, None, None))
      _candidates += _right -> rCandidate.copy(
        weights = rCandidate.weights.updated(_left, rWeight.copy(opposite = rWeight.opposite + 1))
      )
    }

    def compatibility: Compatibility = new Compatibility(delimter + "c|", debug)

    def substitutor: Substitutor = new Substitutor(delimter + "s|", debug)

    def conformance: Conformance = new Conformance(delimter + "r|", debug)

    def clear(): Unit = {
      _last = None
      _elementMap = Map.empty
      _ret = None
      _candidates = Map.empty
    }

    def candidates: List[(PsiNamedElement, Candidate)] =
      _candidates.map { case (name1, v) =>
        name1 -> v.copy(
          weights = v.weights.map { case (name2, weight) =>
            name2 -> weight.copy(opposite = _candidates.get(name2).flatMap(_.weights.get(name1)).map(_.v).getOrElse(0))
          }
        )
      }.toList
  }

  type Args = Seq[DTHandler.Compatibility#Arg]
  type Conditions = Seq[CCondition]
}
