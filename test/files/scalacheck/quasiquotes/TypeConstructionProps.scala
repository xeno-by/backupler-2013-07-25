import org.scalacheck._
import Prop._
import Gen._
import Arbitrary._

import scala.reflect.runtime.universe._
import Flag._

object TypeConstructionProps extends QuasiquoteProperties("type construction")  {

  property("bare idents contain type names") = test {
    tq"x" ≈ Ident(newTypeName("x"))
  }

  property("splice type names into AppliedTypeTree") = forAll { (name1: TypeName, name2: TypeName) =>
    tq"$name1[$name2]" ≈ AppliedTypeTree(Ident(name1), List(Ident(name2)))
  }
}