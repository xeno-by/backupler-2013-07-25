package scala.reflect.macros
package util

trait Traces {
  def globalSettings: scala.tools.nsc.Settings

  val macroDebugLite = globalSettings.YmacrodebugLite.value
  val macroDebugJit  = globalSettings.YmacrodebugJit.value
  val macroDebugVerbose = globalSettings.YmacrodebugVerbose.value
  @inline final def macroLogLite(msg: => Any) { if (macroDebugLite || macroDebugVerbose) println(msg) }
  @inline final def macroLogJit(msg: => Any) { if (macroDebugJit || macroDebugVerbose) println(msg) }
  @inline final def macroLogVerbose(msg: => Any) { if (macroDebugVerbose) println(msg) }
}
