package scala.reflect.macros
package compiler

import java.util.UUID.randomUUID
import scala.reflect.internal.Flags._
import scala.reflect.macros.TypecheckException

trait Validators {
  self: DefaultMacroCompiler =>

  import global._
  import analyzer._
  import definitions._
  import treeInfo._
  import typer.infer._

  def validateMacroImplRef() = {
    sanityCheck()
    if (macroImpl != Predef_???) checkMacroDefMacroImplCorrespondence()
  }

  private def sanityCheck() = {
    if (!macroImpl.isMethod) MacroImplReferenceWrongShapeError()
    if (!macroImpl.isPublic) MacroImplNotPublicError()
    if (macroImpl.isOverloaded) MacroImplOverloadedError()
    if (macroImpl.typeParams.length != targs.length) MacroImplWrongNumberOfTypeArgumentsError()
    val declaredInStaticObject = isImplMethod && (macroImplOwner.isStaticOwner || macroImplOwner.moduleClass.isStaticOwner)
    val declaredInTopLevelClass = isImplBundle && macroImplOwner.owner.isPackageClass
    if (!declaredInStaticObject && !declaredInTopLevelClass) MacroImplReferenceWrongShapeError()
  }

  private def checkMacroDefMacroImplCorrespondence() = {
    val atvars = atparams map freshVar
    def atpeToRtpe(atpe: Type) = atpe.substSym(aparamss.flatten, rparamss.flatten).instantiateTypeParams(atparams, atvars)

    // we only check strict correspondence between value parameterss
    // type parameters of macro defs and macro impls don't have to coincide with each other
    val implicitParams = aparamss.flatten filter (_.isImplicit)
    if (implicitParams.nonEmpty) MacroImplNonTagImplicitParameters(implicitParams)
    if (aparamss.length != rparamss.length) MacroImplParamssMismatchError()
    map2(aparamss, rparamss)((aparams, rparams) => {
      if (aparams.length < rparams.length) MacroImplMissingParamsError(aparams, rparams)
      if (rparams.length < aparams.length) MacroImplExtraParamsError(aparams, rparams)
    })

    try {
      // cannot fuse this map2 and the map2 above because if aparamss.flatten != rparamss.flatten
      // then `atpeToRtpe` is going to fail with an unsound substitution
      map2(aparamss.flatten, rparamss.flatten)((aparam, rparam) => {
        if (aparam.name != rparam.name && !rparam.isSynthetic) MacroImplParamNameMismatchError(aparam, rparam)
        if (isRepeated(aparam) ^ isRepeated(rparam)) MacroImplVarargMismatchError(aparam, rparam)
        val aparamtpe = aparam.tpe.dealias match {
          case RefinedType(List(tpe), Scope(sym)) if tpe =:= ctxTpe && sym.allOverriddenSymbols.contains(MacroContextPrefixType) => tpe
          case tpe => tpe
        }
        checkMacroImplParamTypeMismatch(atpeToRtpe(aparamtpe), rparam)
      })

      checkMacroImplResultTypeMismatch(atpeToRtpe(aret), rret)

      val maxLubDepth = lubDepth(aparamss.flatten map (_.tpe)) max lubDepth(rparamss.flatten map (_.tpe))
      val atargs = solvedTypes(atvars, atparams, atparams map varianceInType(aret), upper = false, depth = maxLubDepth)
      val boundsOk = typer.silent(_.infer.checkBounds(macroDdef, NoPrefix, NoSymbol, atparams, atargs, ""))
      boundsOk match {
        case SilentResultValue(true) => // do nothing, success
        case SilentResultValue(false) | SilentTypeError(_) => MacroImplTargMismatchError(atargs, atparams)
      }
    } catch {
      case ex: NoInstance => MacroImplTparamInstantiationError(atparams, ex)
    }
  }

  // aXXX (e.g. aparamss) => characteristics of the actual macro impl signature extracted from the macro impl ("a" stands for "actual")
  // rXXX (e.g. rparamss) => characteristics of the reference macro impl signature synthesized from the macro def ("r" stands for "reference")
  lazy val MacroImplSig(atparams, aparamss, aret) = macroImplSig
  lazy val MacroImplSig(_, rparamss, rret) = referenceMacroImplSig

  // Technically this can be just an alias to MethodType, but promoting it to a first-class entity
  // provides better encapsulation and convenient syntax for pattern matching.
  private case class MacroImplSig(tparams: List[Symbol], paramss: List[List[Symbol]], ret: Type)

  /** An actual macro implementation signature extracted from a macro implementation method.
   *
   *  For the following macro impl:
   *    def fooBar[T: c.WeakTypeTag]
   *           (c: scala.reflect.macros.Context)
   *           (xs: c.Expr[List[T]])
   *           : c.Expr[T] = ...
   *
   *  This function will return:
   *    (c: scala.reflect.macros.Context)(xs: c.Expr[List[T]])c.Expr[T]
   *
   *  Note that type tag evidence parameters are not included into the result.
   *  Type tag context bounds for macro impl tparams are optional.
   *  Therefore compatibility checks ignore such parameters, and we don't need to bother about them here.
   *
   *  This method cannot be reduced to just macroImpl.info, because macro implementations might
   *  come in different shapes. If the implementation is an apply method of a Macro-compatible object,
   *  then it won't have (c: Context) in its parameters, but will rather refer to Macro.c.
   *
   *  @param macroImpl The macro implementation symbol
   */
  private lazy val macroImplSig: MacroImplSig = {
    val tparams = macroImpl.typeParams
    val paramss = transformTypeTagEvidenceParams(macroImplRef, (param, tparam) => NoSymbol)
    val ret = macroImpl.info.finalResultType
    MacroImplSig(tparams, paramss, ret)
  }

  /** A reference macro implementation signature extracted from a given macro definition.
   *
   *  For the following macro def:
   *    def foo[T](xs: List[T]): T = macro fooBar
   *
   *  This function will return:
   *    (c: scala.reflect.macros.Context)(xs: c.Expr[List[T]])c.Expr[T]
   *
   *  Note that type tag evidence parameters are not included into the result.
   *  Type tag context bounds for macro impl tparams are optional.
   *  Therefore compatibility checks ignore such parameters, and we don't need to bother about them here.
   *
   *  Also note that we need a DefDef, not the corresponding MethodSymbol, because that symbol would be of no use for us.
   *  Macro signatures are verified when typechecking macro defs, which means that at that moment inspecting macroDef.info
   *  means asking for cyclic reference errors.
   *
   *  We need macro implementation symbol as well, because the return type of the macro definition might be omitted,
   *  and in that case we'd need to infer it from the return type of the macro implementation. Luckily for us, we can
   *  use that symbol without a risk of running into cycles.
   *
   *  @param typer     Typechecker of `macroDdef`
   *  @param macroDdef The macro definition tree
   *  @param macroImpl The macro implementation symbol
   */
  private lazy val referenceMacroImplSig: MacroImplSig = {
    // had to move method's body to an object because of the recursive dependencies between sigma and param
    object SigGenerator {
      val cache = scala.collection.mutable.Map[Symbol, Symbol]()
      val ctxPrefix =
        if (isImplMethod) singleType(NoPrefix, makeParam(nme.macroContext, macroDdef.pos, ctxTpe, SYNTHETIC))
        else singleType(ThisType(macroImpl.owner), macroImpl.owner.tpe.member(nme.c))
      var paramss =
        if (isImplMethod) List(ctxPrefix.termSymbol) :: mmap(macroDdef.vparamss)(param)
        else mmap(macroDdef.vparamss)(param)
      val macroDefRet =
        if (!macroDdef.tpt.isEmpty) typer.typedType(macroDdef.tpt).tpe
        else computeMacroDefTypeFromMacroImplRef(macroDdef, macroImplRef)
      val implReturnType = sigma(increaseMetalevel(ctxPrefix, macroDefRet))

      object SigmaTypeMap extends TypeMap {
        def mapPrefix(pre: Type) = pre match {
          case ThisType(sym) if sym == macroDef.owner =>
            singleType(singleType(ctxPrefix, MacroContextPrefix), ExprValue)
          case SingleType(NoPrefix, sym) =>
            mfind(macroDdef.vparamss)(_.symbol == sym).fold(pre)(p => singleType(singleType(NoPrefix, param(p)), ExprValue))
          case _ =>
            mapOver(pre)
        }
        def apply(tp: Type): Type = tp match {
          case TypeRef(pre, sym, args) =>
            val pre1  = mapPrefix(pre)
            val args1 = mapOverArgs(args, sym.typeParams)
            if ((pre eq pre1) && (args eq args1)) tp
            else typeRef(pre1, sym, args1)
          case _ =>
            mapOver(tp)
        }
      }
      def sigma(tpe: Type): Type = SigmaTypeMap(tpe)

      def makeParam(name: Name, pos: Position, tpe: Type, flags: Long) =
        macroDef.newValueParameter(name.toTermName, pos, flags) setInfo tpe
      def param(tree: Tree): Symbol = (
        cache.getOrElseUpdate(tree.symbol, {
          val sym = tree.symbol
          assert(sym.isTerm, s"sym = $sym, tree = $tree")
          makeParam(sym.name, sym.pos, sigma(increaseMetalevel(ctxPrefix, sym.tpe)), sym.flags)
        })
      )
    }

    import SigGenerator._
    macroLogVerbose(s"generating macroImplSigs for: $macroDdef")
    val result = MacroImplSig(macroDdef.tparams map (_.symbol), paramss, implReturnType)
    macroLogVerbose(s"result is: $result")
    result
  }
}
