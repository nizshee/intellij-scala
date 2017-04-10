package org.jetbrains.plugins.scala.actions

import org.jetbrains.plugins.scala.lang.psi.types.{ScType, ScUndefinedSubstitutor}
import org.jetbrains.plugins.scala.lang.resolve.ScalaResolveResult

/**
  * Created by user on 4/10/17.
  */
object DCHandler {
  class Conformance(debug: Boolean, nesting: Int = 0) {

    private val offset = nesting * 1
    private val delimeter = if (offset < 1) "" else "|" * (offset - 1) + "|"

    private var _conditions: Seq[ConformanceCondition] = Seq()
    private var _variances: Seq[ConformanceCondition.Variance] = Seq()

    def +(condition: ConformanceCondition): ConformanceCondition = {
      _conditions :+= condition
      condition
    }

    def +(variance: ConformanceCondition.Variance): Unit = _variances :+= variance

    def conditions: Seq[ConformanceCondition] = _conditions

    def relations: Seq[ConformanceCondition.Variance] = _variances

    def log(any: Any): Unit = if (debug) println(delimeter + any)

    def logn(any: Any): Unit = if (debug) {
      println(delimeter + any)
      println(delimeter)
    }

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


    def inner: Conformance =  new Conformance(debug, nesting + 1)
  }


  class Compatibility {
    case class Arg(name: String, expectedType: ScType, actualType: ScType, undefinedSubstitutor: ScUndefinedSubstitutor)

    private var _args: Seq[Arg] = Seq()

    def +(name: String, expected: ScType, actual: ScType, undefinedSubstitutor: ScUndefinedSubstitutor): Arg = {
      val arg = Arg(name, expected, actual, undefinedSubstitutor)
      _args :+= arg
      arg
    }

    def handler: DCHandler.Conformance = new DCHandler.Conformance(false)

    def args: Seq[Arg] = _args

    def log(any: Any): Unit = println(any)
    def logn(any: Any): Unit = {
      println(any)
      println()
    }

    def logCase(any: Any): Unit = {
      println("case - " + any)
      println()
    }
  }

  class Substitutor {
    def log(any: Any): Unit = println(any)
    def logn(any: Any): Unit = {
      println(any)
      println()
    }
  }

  class Resolver {
    case class Candidate(rr: ScalaResolveResult)

    private var _candidates = Seq.empty[Candidate]

    def +(rr: ScalaResolveResult): Candidate = {
      val candidate = Candidate(rr)
      _candidates :+= candidate
      candidate
    }

    def candidates: Seq[Candidate] = _candidates

    def log(any: Any): Unit = println(any)
    def logn(any: Any): Unit = {
      println(any)
      println()
    }
  }
}
