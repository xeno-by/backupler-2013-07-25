package scala.tools.reflect
package quasiquotes

import scala.reflect.macros.contexts.Context

abstract class Quasiquotes extends Macros
                              with Parsers
                              with Reifiers  {
  val c: Context
  val global: c.universe.type = c.universe

  def debug(msg: String) =
    if (c.universe.settings.Yquasiquotedebug.value) println(msg)
}
