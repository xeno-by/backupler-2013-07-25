package scala.tools.reflect
package quasiquotes

import scala.tools.nsc.ast.parser.{Parsers => ScalaParser}
import scala.tools.nsc.ast.parser.Tokens._
import scala.compat.Platform.EOL
import scala.reflect.internal.util.{BatchSourceFile, SourceFile}
import scala.collection.mutable.ListBuffer

trait Parsers { self: Quasiquotes =>
  import global._

  abstract class Parser extends {

    val global: self.global.type = self.global

  } with ScalaParser {

    def wrapCode(code: String): String =
      s"object wrapper { $$wrapper$$self => $EOL $code $EOL }"

    def unwrapTree(wrappedTree: Tree): Tree = {
      val PackageDef(_, List(ModuleDef(_, _, Template(_, _, _ :: parsed)))) = wrappedTree
      parsed match {
        case tree :: Nil => tree
        case stats :+ tree => Block(stats, tree)
      }
    }

    def parse(code: String, placeholders: Set[String]): Tree = {
      try {
        val wrapped = wrapCode(code)
        debug(s"wrapped code\n=${wrapped}\n")
        val file = new BatchSourceFile("<quasiquotes>", wrapped)
        val tree = new QuasiquoteParser(file, placeholders).parse()
        unwrapTree(tree)
      } catch {
        case mi: MalformedInput => c.abort(c.macroApplication.pos, s"syntax error: ${mi.msg} at ${mi.offset}")
      }
    }

    class QuasiquoteParser(source0: SourceFile, placeholders: Set[String]) extends SourceFileParser(source0) {
      // q"def foo($x)"
      override def allowTypelessParams = true

      // q"{ $x }"
      override def block(): Tree = makeBlock(blockStatSeq())
      private def makeBlock(stats: List[Tree]): Tree =
        if (stats.isEmpty) Literal(Constant())
        else if (!stats.last.isTerm) Block(stats, Literal(Constant()))
        else if (stats.length == 1) stats match {
          case Ident(TermName(name)) :: Nil if placeholders(name) => Block(stats.init, stats.last)
          case _ => stats.head
        } else Block(stats.init, stats.last)

      // q"foo match { $x }"
      override def caseClauses(): List[CaseDef] = {
        val cases = caseSeparated { atPos(in.offset)(treeBuilder.makeCaseDef(pattern(), guard(), caseBlock())) }
        if (cases.isEmpty) {
          if (in.token == IDENTIFIER && placeholders(in.name.toString)) ???
          else accept(CASE) // trigger error if there are no cases and noone gets spliced
        }
        cases
      }

      private class PlainScannerData extends ScannerData {
        var ch: Char = _
        var charOffset: Int = 0
        var lineStartOffset: Int = 0
        var lastLineStartOffset: Int = 0
      }

      def peekingAhead[T](body: => T): T = {
        // peek ahead
        val curr = new PlainScannerData; curr.copyFrom(in)
        val prev = new PlainScannerData; prev.copyFrom(in.prev)
        val next = new PlainScannerData; next.copyFrom(in.next)
        in.nextToken()

        val res = body

        // push back
        in copyFrom curr
        in.prev copyFrom prev
        in.next copyFrom next

        res
      }

      override def isTemplateIntro: Boolean = {
        val nextTemplateIntro = peekingAhead { super.isTemplateIntro }
        super.isTemplateIntro || (isIdent && placeholders.contains(in.name.toString) && nextTemplateIntro)
      }

      override def isDclIntro: Boolean = {
        val nextDclIntro = peekingAhead { super.isDclIntro }
        super.isDclIntro || (isIdent && placeholders.contains(in.name.toString) && nextDclIntro)
      }

      def modsPlaceholderAnnot(name: TermName): Tree =
        q"new ${tpnme.QUASIQUOTE_MODS}(${name.toString})"

      // @ foo $quasiquote$1 def foo
      // $quasiquote$1 T
      def customReadAnnots(annot: => Tree): List[Tree] = {
        val annots = new ListBuffer[Tree]
        var break = false
        while (!break) {
          if (in.token == AT) {
            in.nextToken()
            annots += annot
          } else if(isIdent && placeholders.contains(in.name.toString) &&
                    peekingAhead { in.token == AT || isIdent || isModifier || isDefIntro }) {
            annots += modsPlaceholderAnnot(in.name)
            in.nextToken()
          } else {
            break = true
          }
        }
        annots.toList
      }

      override def annotations(skipNewLines: Boolean): List[Tree] = customReadAnnots {
        val t = annotationExpr()
        if (skipNewLines) newLineOpt()
        t
      }

      override def constructorAnnotations(): List[Tree] = customReadAnnots {
        atPos(in.offset)(New(exprSimpleType(allowDeptypes = false), List(argumentExprs())))
      }
    }
  }

  object TermParser extends Parser

  object TypeParser extends Parser {

    override def wrapCode(code: String) = super.wrapCode("type T = " + code)

    override def unwrapTree(wrappedTree: Tree): Tree = {
      val TypeDef(_, _, _, rhs) = super.unwrapTree(wrappedTree)
      rhs
    }
  }
}