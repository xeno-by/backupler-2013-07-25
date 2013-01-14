import scala.language.experimental.macros
import scala.reflect.macros.Context

object TypeOf {
  type TypeOf[T](s: T) = macro impl[T]
  def impl[T: c.WeakTypeTag](c: Context)(s: c.Expr[T]): c.Tree = {
    import c.universe._
    TypeTree(weakTypeOf[T])
  }
}
