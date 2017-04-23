import org.jetbrains.plugins.scala.actions.DCHandler
import org.jetbrains.plugins.scala.macroAnnotations.{identity, uninstrumental}

// @uninstrumental("handler")
case class A(a: Int, var b: Int, handler: Option[DCHandler] = None)(implicit c: Int) {
  def i: Int = {
    handler.foreach(_.log("method"))
    pi + c
  }
  private def pi: Int = {
    handler.foreach(_.log("premethod"))
    a + b
  }
}

class AB {
  def a: Int = 1
}

@identity
class BD extends AB {
  override def a = super.a
}

@identity
class B {
  A(a = 1, b = 2)(1)
}

val handler = Some(new DCHandler("", true))
val a = A.$I(a$I = 1, 2, handler)(3)

a.i
a.b