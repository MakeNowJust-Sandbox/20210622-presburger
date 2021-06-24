package codes.quine.labo.presburger

import codes.quine.labo.presburger.Term._

/** Term is an abstract syntax tree of Presburger arithmetic term.
  *
  * {{{
  * t ::= k      (* constant value *)
  *     | x      (* variable *)
  *     | t + t  (* addition *)
  *     | t - t  (* subtraction *)
  *     | k * t  (* multiplication *)
  * }}}
  */
sealed abstract class Term {

  /** Returns a linear form term of this. */
  def toLinTerm: LinTerm = this match {
    case Const(k)  => LinTerm.Const(k)
    case Var(x)    => LinTerm.Var(x)
    case Add(l, r) => l.toLinTerm + r.toLinTerm
    case Sub(l, r) => l.toLinTerm - r.toLinTerm
    case Mul(k, t) => k *: t.toLinTerm
  }
}

object Term {

  /** A constant value `k`. */
  final case class Const(value: Z) extends Term {
    override def toString: String = value.toString
  }

  /** A variable `x`. */
  final case class Var(name: Name) extends Term {
    override def toString: String = name
  }

  /** An addition term `t + t`. */
  final case class Add(left: Term, right: Term) extends Term {
    override def toString: String = s"$left + $right"
  }

  /** A subtraction term `t - t`. */
  final case class Sub(left: Term, right: Term) extends Term {
    override def toString: String = s"$left - $right"
  }

  /** A multiplication term `k * t`. */
  final case class Mul(const: Z, term: Term) extends Term {
    override def toString: String = {
      def wrap(term: Term): String = term match {
        case Add(_, _) | Sub(_, _) => s"(${term})"
        case _                     => term.toString
      }

      s"$const * ${wrap(term)}"
    }
  }
}
