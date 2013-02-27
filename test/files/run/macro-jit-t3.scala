import scala.reflect.macros.Context
import language.experimental.macros

object Test extends App {
  def impl(c: Context) = {
    import c.universe._
    println(c.freshName())
    println(c.freshName("qwe"))
    println(c.freshName(TypeName("qwe")))
    c.abort(NoPosition, "blargh")
  }
  def foo = macro impl

  import scala.reflect.runtime.universe._
  import scala.reflect.runtime.{currentMirror => cm}
  import scala.tools.reflect.ToolBox
  val tree = Select(Ident(TermName("Test")), TermName("foo"))
  try cm.mkToolBox().eval(tree)
  catch { case ex: Throwable =>  println(ex.getMessage) }
}