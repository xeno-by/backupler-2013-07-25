object Test extends App {
  trait Conv[T, U] { def apply(x: T): U }
  case class C(s: String)
  implicit val ConvStringC = new Conv[String, C]{ def apply(x: String) = new C(x) }
  implicit def foo[T, U](x: T)(implicit conv: Conv[T, U]): U = conv(x)
  println("x".s)
}