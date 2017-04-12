package org.jetbrains.plugins.scala.actions

import com.intellij.psi.PsiNamedElement
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

    def logt(left: ScType, right: ScType): Unit = if (debug) {
      println(delimeter + s"left: ${left.presentableText}")
      println(delimeter + s"right: ${right.presentableText}")
    }

    def logtn(left: ScType, right: ScType): Unit = if (debug) {
      println(delimeter + s"left: ${left.presentableText}")
      println(delimeter + s"right: ${right.presentableText}")
      println(delimeter)
    }

    def visit(any: Any): Unit = if (debug) {
      println(delimeter + "visit " + any)
      println(delimeter)
    }

    def rvisit(any: Any): Unit = if (debug) {
      println(delimeter + "right visit " + any)
      println(delimeter)
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
      println(delimeter + "case - " + any)
      println(delimeter)
    }
  }

  class Substitutor(delimeter: String, debug: Boolean) extends DCHandler(delimeter, debug)

  class Resolver(delimter: String, debug: Boolean) extends DCHandler(delimter, debug) {
    case class Weight(v: Int, opposite: Int)
    case class Candidate(rr: Option[ScalaResolveResult], weights: Map[PsiNamedElement, Weight], args: Seq[DCHandler.Compatibility#Arg])
    private var last: Option[PsiNamedElement] = None
    private var _candidates: Map[PsiNamedElement, Candidate] = Map.empty

    def +(el: PsiNamedElement): Candidate = {
      val candidate = Candidate(None, Map.empty, Seq())
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

    def clear(): Unit = {
      _candidates = Map.empty
    }

    def compatibility: Compatibility = new Compatibility(delimter + "c|", debug)

    def candidates: List[(PsiNamedElement, Candidate)] = _candidates.toList
  }
}
