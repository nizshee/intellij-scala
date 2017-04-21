
import org.jetbrains.plugins.scala.actions.DCHandler
import org.jetbrains.plugins.scala.actions
import org.jetbrains.plugins.scala.macroAnnotations.{identity, uninstrumental}


object a {
  val boolean = true
  val boolean1 = false
}
/*
@identity
class D1(var b: Int) {
  protected val a = 1
}

@identity
class D2(var b$: Int) extends D1(1) {
  override protected val a = 2

  b += 1
  b = b + 1
}*/

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


////@uninstrumental("handler")
//def myInnerMethod(i: Int, handler: Option[DCHandler] = None): Int = {
//  handler.foreach(_.log("!!!"))
//  new MyClass(i, handler)
//  2
//}trumental("handler")
//def myInnerMethod(i: Int, handler: Option[DCHandler] = None): Int = {
//  handler.foreach(_.log("!!!"))
//  new MyClass(i, handler)
//  2
//}

//@identity
//case class D(private var a: Int, b: Int)
//
//@identity
//class D1(a: Int, override val b: Int) extends D(a, b)

//@identity
class A(val a: Int)(b: Int) {
  private def f = 1

  val c: Int = 1

  var d: Int = 2

  def g: Int = f

  protected def h: Int = f + 1
}

class B(a: Int) extends A(a)(a) {
  private def f = 2

  d += 1

  override def g: Int = f

  override protected def h: Int = f + 1
}

class C(i1: Int)(i2: Int)

// case classes
// override methods

//@uninstrumental("handler")
class MyClass(override val a: Int, var b: Int, handler: Option[DCHandler]) extends A(a)(b) {

  val puba = 1
  var pubb = 2
  private val pa = 1
  private var pb = 1

//  val i1 = i + 1

//  MyClass.method(this, handler)

  handler.foreach(_.log("!!!"))

//  myInnerMethod(i, handler)
}

object MyClass {
//  @uninstrumental("handler")
  def method(c: MyClass, handler: Option[DCHandler]): Unit = {
    handler.foreach(_.log("companion"))

    println(c.b + 1)
    ()
  }
}

//new MyClass(1, 2, None)

//class I(i$: Int, handler: Option[DCHandler]) extends MyClass(i$, None) {
//
//  MyClass.method(this, handler)
//
//  handler.foreach(_.log("!!!"))
//}