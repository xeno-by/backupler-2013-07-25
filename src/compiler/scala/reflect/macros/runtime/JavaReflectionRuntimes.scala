package scala.reflect.macros
package runtime

import java.lang.reflect.Constructor
import scala.reflect.runtime.ReflectionUtils
import scala.reflect.macros.{Context => ApiContext}

trait JavaReflectionRuntimes {
  self: scala.tools.nsc.typechecker.Analyzer =>

  trait JavaReflectionResolvers {
    self: MacroRuntimeResolver =>

    import global._

    private def getBundleConstructor(clazz: Class[_]): Constructor[_] = {
      def isBundleConstructor(ctor: Constructor[_]): Boolean = ctor.getParameterTypes match {
        case Array(ctx) if classOf[ApiContext].isAssignableFrom(ctx) => true
        case _ => false
      }
      clazz.getDeclaredConstructors().filter(isBundleConstructor) match {
        case Array(ctor) => ctor
        case ctors => throw new Exception("cannot load the bundle constructor for $clazz from $ctors")
      }
    }

    def resolveJavaReflectionRuntime(classLoader: ClassLoader): MacroRuntime = {
      val implClass = Class.forName(className, true, classLoader)
      val implMeths = implClass.getDeclaredMethods.find(_.getName == methName)
      // relies on the fact that macro impls cannot be overloaded
      // so every methName can resolve to at maximum one method
      val implMeth = implMeths getOrElse { throw new NoSuchMethodException(s"$className.$methName") }
      macroLogVerbose(s"successfully loaded macro impl as ($implClass, $implMeth)")
      args => {
        val implObj =
          if (isBundle) getBundleConstructor(implClass).newInstance(args.c)
          else ReflectionUtils.staticSingletonInstance(implClass)
        val implArgs = if (isBundle) args.others else args.c +: args.others
        implMeth.invoke(implObj, implArgs.asInstanceOf[Seq[AnyRef]]: _*)
      }
    }
  }
}