import org.jetbrains.plugins.scala.actions.uninstrumental
import org.jetbrains.plugins.scala.actions.DCHandler
import org.jetbrains.plugins.scala.actions

//@identity
//class C
//
//@identity class D; object D
//
//new C
//
//new D
//
//def twice[@identity T](@identity x: Int) = x * 2


//@uninstrumental("handler")
def myMethod(handler: Option[DCHandler.Resolver] = None): Int = {

  class A(had: Int) {
    handler += 1
    var handler = 1
  }

//  handler.foreach { h =>
//    h.log("???")
//  }
//
//  object a {
//    var handler = 1
//  }
//
//  def f() = {
//    handler.foreach(_.log("111"))
////    1
//  }
//
//  def g() = {
//    val handler = 1 // should remove after val
//    handler + 1
//  }

  def h(handler: Int) = {
    handler + 1
  }

  2
}


myMethod()

//myMethod$I(handler = None)