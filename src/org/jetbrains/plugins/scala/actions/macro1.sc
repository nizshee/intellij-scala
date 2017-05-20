import org.jetbrains.plugins.scala.macroAnnotations.{identity, uninstrumental}


class A(var a: Int) {
  def method(delta: Int): Unit = {
    a += delta
  }

  a += 1
}

@identity
class C(o: Option[Int]) {
  o.exists(_ > 0)
  o.contains(1)
}

// присвоение не позицонного оргумента

class B(var b: Int) extends A(b) {
  b = a
}

val b = new B(b = 1)
b.a
b.b


