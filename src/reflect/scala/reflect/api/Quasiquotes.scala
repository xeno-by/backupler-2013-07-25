package scala.reflect
package api

import language.experimental.macros

trait Quasiquotes { self: Universe =>

  // implementation is hardwired to methods of `scala.tools.reflect.QuasiQuotes`
  // using the mechanism implemented in `scala.tools.reflect.FastTrack`
  implicit class Quasiquote(ctx: StringContext) {
    object q {
      def apply(args: Any*): Any = macro ???
      def unapply(subpatterns: Any*): Option[Any] = macro ???
    }
    object tq {
      def apply(args: Any*): Any = macro ???
      def unapply(subpatterns: Any*): Option[Any] = macro ???
    }
  }
}
