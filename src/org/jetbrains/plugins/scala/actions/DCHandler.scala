package org.jetbrains.plugins.scala.actions

import com.intellij.psi.PsiNamedElement
import org.jetbrains.plugins.scala.lang.psi.types.api.{Any, Nothing, UndefinedType}
import org.jetbrains.plugins.scala.lang.psi.types.{ScCompoundType, ScType, ScUndefinedSubstitutor, Signature, TypeAliasSignature}
import org.jetbrains.plugins.scala.lang.resolve.ScalaResolveResult

/**
  * Created by user on 4/10/17.
  */
class DCHandler(delimeter: String, debug: Boolean) {
  def log(any: Any): Unit = if (debug) println(delimeter + any)
  def logn(any: Any): Unit = if (debug) {
    println(delimeter + any)
    println()
  }
}

object DCHandler {

  class Conformance(delimeter: String, debug: Boolean) extends DCHandler(delimeter, debug) {

    private var _compound: Option[ConformanceCondition.CompoundLeft] = None
    private var _conditions: Seq[ConformanceCondition] = Seq()
    private var _variances: Seq[ConformanceCondition.Variance] = Seq()

    def addCompound(compound: ScCompoundType, right: ScType): Unit = _compound =
      Some(ConformanceCondition.CompoundLeft(compound, right, Map(), Map(), Seq()))

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

    def +(condition: ConformanceCondition): ConformanceCondition = {
      _conditions :+= condition
      condition
    }

    def +(variance: ConformanceCondition.Variance): Unit = _variances :+= variance

    def conditions: Seq[ConformanceCondition] = _conditions

    def relations: Seq[ConformanceCondition.Variance] = _variances

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


    def inner: Conformance =  new Conformance(delimeter + "|", debug)
  }


  class Compatibility(delimeter: String, debug: Boolean) extends DCHandler(delimeter, debug) {
    case class Arg(name: String,
                   expectedType: ScType,
                   actualType: ScType,
                   undefinedSubstitutor: ScUndefinedSubstitutor,
                   conditions: Seq[ConformanceCondition]) {
      def satisfy: Boolean = conditions.exists(_.satisfy)
    }

    private var _args: Seq[Arg] = Seq()

    def +(arg: Arg): Arg = {
      _args :+= arg
      arg
    }

    def handler: DCHandler.Conformance = new DCHandler.Conformance(delimeter + "r|", debug)

    def args: Seq[Arg] = _args

    def logCase(any: Any): Unit = {
      logn("case - " + any)
    }
  }

  class Substitutor(delimeter: String, debug: Boolean) extends DCHandler(delimeter, debug) {
    case class Restriction(name: (String, Long),
                           `type`: Option[ScType],
                           uppers: Set[ScType],
                           lowers: Set[ScType])

    private var _restrictions: Seq[Restriction] = Seq.empty

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

    def restictions: Seq[Restriction] = _restrictions
  }

  class Resolver(delimter: String, debug: Boolean) extends DCHandler(delimter, debug) {

    case class Weight(v: Int, opposite: Int, asSpecificAs: Option[AsSpecificAsCondition], derived: Option[Nothing])
    case class Candidate(rr: Option[ScalaResolveResult],
                         weights: Map[PsiNamedElement, Weight],
                         args: Seq[DCHandler.Compatibility#Arg],
                         restrictions: Seq[DCHandler.Substitutor#Restriction])

    private var _last: Option[PsiNamedElement] = None
    private var _candidates: Map[PsiNamedElement, Candidate] = Map.empty
    private var _elementMap: Map[PsiNamedElement, PsiNamedElement] = Map.empty

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

    def addRestrictions(restrictions: Seq[Substitutor#Restriction]): Unit = {
      _last.flatMap(el => _candidates.get(el).map(el -> _)) match {
        case Some((el, candidate)) =>
          _candidates += el -> candidate.copy(restrictions = restrictions)
        case None =>
      }
    }

    def +(args: Seq[DCHandler.Compatibility#Arg]): Unit = {
      _last.flatMap(el => _candidates.get(el).map(el -> _)) match {
        case Some((el, candidate)) =>
          _candidates += el -> candidate.copy(args = args)
        case None =>
      }
    }

    def addWeight(left: PsiNamedElement, right: PsiNamedElement, v: Int): Unit = { // TODO? remove
      val _left = resolve(left)
      val _right = resolve(right)
      val candidate = _candidates.getOrElse(_left, Candidate(None, Map.empty, Seq.empty, Seq.empty))
      val weight = candidate.weights.getOrElse(_right, Weight(0, 0, None, None))
      _candidates += _left -> candidate.copy(
        weights = candidate.weights.updated(_right, weight.copy(v = v))
      )

      val rCandidate = _candidates.getOrElse(_right, Candidate(None, Map.empty, Seq.empty, Seq.empty))
      val rWeight = rCandidate.weights.getOrElse(_left, Weight(0, 0, None, None))
      _candidates += _right -> rCandidate.copy(
        weights = rCandidate.weights.updated(_left, rWeight.copy(opposite = v))
      )
    }

    def addWeight(left: PsiNamedElement, right: PsiNamedElement, asSpecificAs: AsSpecificAsCondition): Unit = {
      val _left = resolve(left)
      val _right = resolve(right)
      val candidate = _candidates.getOrElse(_left, Candidate(None, Map.empty, Seq.empty, Seq.empty))
      val weight = candidate.weights.getOrElse(_right, Weight(0, 0, None, None))
      _candidates += _left -> candidate.copy(
        weights = candidate.weights.updated(_right, weight.copy(asSpecificAs = Some(asSpecificAs)))
      )

      val rCandidate = _candidates.getOrElse(_right, Candidate(None, Map.empty, Seq.empty, Seq.empty))
      val rWeight = rCandidate.weights.getOrElse(_left, Weight(0, 0, None, None))
      _candidates += _right -> rCandidate.copy(
        weights = rCandidate.weights.updated(_left, rWeight.copy(/*opposite = rWeight.opposite + 1*/))
      )
    }

    def clear(): Unit = {
      _candidates = Map.empty
    }

    def compatibility: Compatibility = new Compatibility(delimter + "c|", debug)

    def substitutor: Substitutor = new Substitutor(delimter + "s|", debug)

    def conforemance: Conformance = new Conformance(delimter + "r|", debug)

    def candidates: List[(PsiNamedElement, Candidate)] = _candidates.toList
  }

  type Args = Seq[DCHandler.Compatibility#Arg]
  type Conditions = Seq[ConformanceCondition]
}
