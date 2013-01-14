object Test extends App {
  import scala.language.existentials
  import Macros._
  val x: Foo(2) = 2
}