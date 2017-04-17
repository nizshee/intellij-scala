import org.jetbrains.plugins.scala.actions.uninstrumental
import org.jetbrains.plugins.scala.actions.instrumentated
import org.jetbrains.plugins.scala.actions.DCHandler
import org.jetbrains.plugins.scala.actions


object a {
  val boolean = true
  val boolean1 = false
}


//@uninstrumental("handler")
def myMethod(handler: Option[DCHandler] = None): Int = {

  if (a.boolean && a.boolean1 && handler.isEmpty) {
    1 + 2
  }

  if (handler.nonEmpty || (a.boolean && a.boolean1 && handler.isEmpty)) {
    1 + 1
  }

//  class A(had: Int, var a: Int) {
//    println(had)
//    var handler = 1
//    handler += 1
//  }
//
//  handler.foreach { h =>
//    h.log("???")
//  }
//
//  def f() = {
//    handler.foreach(_.log("222"))
//    1
//  }
//
//  def g() = {
//    val handler = 1 // should remove after val
//    handler + 1
//  }
//
//  def h(handler: Int) = {
//    handler + 1
//  }
//
//  handler.foreach { h =>
//    h.log("???")
//  }

//  val inner = handler.map(h => h)
//  val i = inner.map(i => i)
//  myInnerMethod(1, handler = inner)
//  myInnerMethod(2, i)
  1
}

@uninstrumental("i")
def myInnerMethod(i: Int, handler: Option[DCHandler] = None): Int = {
  handler.foreach(_.log("!!!"))
  2
}

trait A {
  val a = 1
}


@uninstrumental("a")
class MyClass(i: Int, handler: Option[DCHandler]) extends A {

  handler.foreach { h =>
    h.log("???")
  }

  myInnerMethod(a, handler)

  override val a = 2
}

new MyClass$I(1, None)


myMethod()

//myMethod$I(handler = None)