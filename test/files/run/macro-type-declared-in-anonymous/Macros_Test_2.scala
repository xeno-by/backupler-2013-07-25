object Test extends App {
  import scala.language.reflectiveCalls
  val macros = new { type Foo(x: Int) = macro Impls.foo }
  class D extends macros.Foo(2)
  val x: macros.Foo(2) = new D
}