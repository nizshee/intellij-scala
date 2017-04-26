package org.jetbrains.plugins.scala.actions

import com.intellij.psi.PsiNamedElement
import org.jetbrains.plugins.scala.lang.psi.types.api.{Any, Nothing, UndefinedType}
import org.jetbrains.plugins.scala.lang.psi.types.{ScType, ScUndefinedSubstitutor}
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

//    private val offset = nesting * 1
//    private val delimeter = if (offset < 1) "" else "|" * (offset - 1) + "|"

    private var _conditions: Seq[ConformanceCondition] = Seq()
    private var _variances: Seq[ConformanceCondition.Variance] = Seq()

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

    private var last: Option[PsiNamedElement] = None
    private var _candidates: Map[PsiNamedElement, Candidate] = Map.empty

    def +(el: PsiNamedElement): Candidate = {
      val candidate = Candidate(None, Map.empty, Seq.empty, Seq.empty)
      last = Some(el)
      _candidates += el -> candidate
      candidate
    }

    def +(rr: ScalaResolveResult): Unit = {
      last.flatMap(el => _candidates.get(el).map(el -> _)) match {
        case Some((el, candidate)) =>
          _candidates += el -> candidate.copy(rr = Some(rr))
        case _ =>
      }
    }

    def addRestrictions(restrictions: Seq[Substitutor#Restriction]): Unit = {
      last.flatMap(el => _candidates.get(el).map(el -> _)) match {
        case Some((el, candidate)) =>
          _candidates += el -> candidate.copy(restrictions = restrictions)
        case None =>
      }
    }

    def +(args: Seq[DCHandler.Compatibility#Arg]): Unit = {
      last.flatMap(el => _candidates.get(el).map(el -> _)) match {
        case Some((el, candidate)) =>
          _candidates += el -> candidate.copy(args = args)
        case None =>
      }
    }

    def addWeight(left: PsiNamedElement, right: PsiNamedElement, weight: Weight): Unit = {
      _candidates.get(left) match {
        case Some(candidate) =>
          _candidates += left -> candidate.copy(
            weights = candidate.weights.updated(right, weight)
          )
        case _ =>
      }
    }

    def addWeight(left: PsiNamedElement, right: PsiNamedElement, v: Int): Unit = {
      val candidate = _candidates.getOrElse(left, Candidate(None, Map.empty, Seq.empty, Seq.empty))
      val weight = candidate.weights.getOrElse(right, Weight(0, 0, None, None))
      _candidates += left -> candidate.copy(
        weights = candidate.weights.updated(right, weight.copy(v = v))
      )

      val rCandidate = _candidates.getOrElse(right, Candidate(None, Map.empty, Seq.empty, Seq.empty))
      val rWeight = rCandidate.weights.getOrElse(left, Weight(0, 0, None, None))
      _candidates += right -> rCandidate.copy(
        weights = rCandidate.weights.updated(left, rWeight.copy(opposite = v))
      )
    }

    def addWeight(left: PsiNamedElement, right: PsiNamedElement, asSpecificAs: AsSpecificAsCondition): Unit = {
      val candidate = _candidates.getOrElse(left, Candidate(None, Map.empty, Seq.empty, Seq.empty))
      val weight = candidate.weights.getOrElse(right, Weight(0, 0, None, None))
      _candidates += left -> candidate.copy(
        weights = candidate.weights.updated(right, weight.copy(asSpecificAs = Some(asSpecificAs)))
      )

      val rCandidate = _candidates.getOrElse(right, Candidate(None, Map.empty, Seq.empty, Seq.empty))
      val rWeight = rCandidate.weights.getOrElse(left, Weight(0, 0, None, None))
      _candidates += right -> rCandidate.copy(
        weights = rCandidate.weights.updated(left, rWeight.copy(/*opposite = rWeight.opposite + 1*/))
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
