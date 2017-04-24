import org.jetbrains.plugins.scala.macroAnnotations.{identity, uninstrumental}



@uninstrumental("handler", debug = true)
def f(handler: Option[Int]): Int = {
  new C(handler = handler).get
}

@uninstrumental("handler")
class C(handler: Option[Int]) {
  def get: Int = 2
}