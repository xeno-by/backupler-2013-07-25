package scala.tools.reflect
package quasiquotes

trait Compat { self: Quasiquotes =>
  import global._
  import global.Flag._

  object SyntacticClassDef {
    def apply(mods: Modifiers, name: TypeName, tparams: List[TypeDef],
              constrMods: Modifiers, vparamss: List[List[ValDef]], argss: List[List[Tree]],
              parents: List[Tree], selfdef: ValDef, body: List[Tree]): Tree =
      ClassDef(mods, name, tparams, Template(parents, selfdef, constrMods, vparamss, argss, body, NoPosition))

    def unapply(tree: Tree): Option[(Modifiers, TypeName, List[TypeDef], Modifiers,
                                     List[List[ValDef]], List[List[Tree]], List[Tree], ValDef, List[Tree])] = tree match {
      case ClassDef(mods, name, tparams, Template(parents, selfdef, tbody)) =>
        // extract generated fieldDefs and constructor
        val (defs, (DefDef(mods, _, _, vparamss0, _, Block(_ :+ treeInfo.Applied(_, _, argss), _))) :: otherDefs) = tbody.splitAt(tbody.indexWhere {
          case DefDef(_, nme.CONSTRUCTOR, _, _, _, _) => true
          case _ => false
        })
        val (earlyDefs, fieldDefs) = defs.span(treeInfo.isEarlyDef)

        // undo conversion from (implicit ... ) to ()(implicit ... ) when its the only parameter section
        val vparamss1 = vparamss0 match {
          case List() :: rest if !rest.isEmpty && !rest.head.isEmpty && rest.head.head.mods.isImplicit => rest
          case other => other
        }

        // undo flag modifications by mergeing flag info from constructor args and fieldDefs
        val modsMap = fieldDefs.map { case ValDef(mods, name, _, _) => name -> mods }.toMap
        val vparamss2 = vparamss1.map { _.map { vd =>
          val originalMods = modsMap(vd.name) | (vd.mods.flags & DEFAULTPARAM)
          atPos(vd.pos)(ValDef(originalMods, vd.name, vd.tpt, vd.rhs))
        }}

        Some((mods, name, tparams, mods, vparamss2, argss, parents, selfdef, earlyDefs ::: otherDefs))
      case _ =>
        None
    }
  }
}
