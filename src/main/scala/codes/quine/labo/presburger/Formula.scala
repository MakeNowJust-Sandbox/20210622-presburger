package codes.quine.labo.presburger

import scala.annotation.tailrec

import codes.quine.labo.presburger.Formula._

/** Formula is an abstract syntax tree of Presburger arithmetic formula.
  *
  * {{{
  * F ::= ⊤       (* tautology *)
  *     | ⊥       (* contradiction *)
  *     | t < t   (* comparison *)
  *     | t ≤ t
  *     | t > t
  *     | t ≥ t
  *     | t = t
  *     | t ≠ t
  *     | k ∣ t   (* divisibility constraint *)
  *     | F ∧ F   (* logical conjunction *)
  *     | F ∨ F   (* logical disjunction *)
  *     | ¬F      (* logical negation *)
  *     | ∀ x. F  (* universal quantifier *)
  *     | ∃ x. F  (* existential quantifier *)
  * }}}
  */
sealed abstract class Formula extends Product with Serializable {

  /** Checks whether or not this formula is tautology after quantifier elimination. */
  def verify(): Boolean = toNNFFormula.verify()

  /** Eliminates quantifiers in this formula, then returns eliminated one.
    *
    * This method uses Cooper's theorem to eliminate quantifiers.
    */
  def toNNFFormula: NNFFormula = this match {
    case True  => NNFFormula.True
    case False => NNFFormula.False
    case Cmp(op, l0, r0) =>
      val l = l0.toLinTerm
      val r = r0.toLinTerm
      op match {
        // l < r <=> l - r < 0
        case LT => NNFFormula.LessThanZero(l - r)
        // l <= r <=> l < r + 1 <=> l - r - 1 < 0
        case LE => NNFFormula.LessThanZero(l - r - 1)
        // l > r <=> r < l <=> r - l < 0
        case GT => NNFFormula.LessThanZero(r - l)
        // l >= r <=> l + 1 > r <=> r < l + 1 <=> r - l - 1 < 0
        case GE => NNFFormula.LessThanZero(r - l - 1)
        // l == r <=> l < r + 1 && r < l + 1
        case EQ => NNFFormula.And(NNFFormula.LessThanZero(l - r - 1), NNFFormula.LessThanZero(r - l - 1))
        // l != r <=> l < r || r < l
        case NE => NNFFormula.Or(NNFFormula.LessThanZero(l - r), NNFFormula.LessThanZero(r - l))
      }
    case Div(k, t)    => NNFFormula.Div(k, t.toLinTerm)
    case And(l, r)    => NNFFormula.And(l.toNNFFormula, r.toNNFFormula)
    case Or(l, r)     => NNFFormula.Or(l.toNNFFormula, r.toNNFFormula)
    case Not(f)       => f.toNNFFormula.negate
    case ForAll(x, f) => Exist(x, Not(f)).toNNFFormula.negate
    case Exist(x, f0) =>
      val f1 = f0.toNNFFormula
      val ks = f1.coefficients(x)
      if (ks.isEmpty) f1
      else {
        @tailrec
        def gcd(a: Z, b: Z): Z =
          if (b == 0) a else gcd(b, a % b)
        def lcm(as: Set[Z]): Z =
          as.foldLeft(1: BigInt)((a, b) => a * b / gcd(a, b))

        val m = lcm(ks.map(_.abs))
        val f2 = NNFFormula.And(f1.normalize(x, m), NNFFormula.Div(m, LinTerm.Var(x)))
        val d = lcm(f2.divs(x).map(_.abs))
        val k31 = f2.assignMinInf(x)
        val bs = f2.bounds(x)
        if (bs.isEmpty) NNFFormula.BigOr(x, d, k31)
        else {
          val k32 = bs.map(b => f2.assign(x, b + LinTerm.Var(x))).reduceLeft(NNFFormula.Or(_, _))
          NNFFormula.BigOr(x, d, NNFFormula.Or(k31, k32))
        }
      }
  }
}

object Formula {

  /** A tautology formula `⊤`. */
  case object True extends Formula {
    override def toString: String = "⊤"
  }

  /** A contradiction formula `⊥`. */
  case object False extends Formula {
    override def toString: String = "⊥"
  }

  /** A comparison formula `t < t`, `t ≤ t`, `t > t`, `t ≥ t`, `t = t` or `t ≠ t`. */
  final case class Cmp(op: CmpOp, left: Term, right: Term) extends Formula {
    override def toString: String = s"$left $op $right"
  }

  /** A divisibility constraint formula `k ∣ t`. */
  final case class Div(const: Z, term: Term) extends Formula {
    override def toString: String = s"$const ∣ $term"
  }

  /** A logical conjunction formula `F ∧ F`. */
  final case class And(left: Formula, right: Formula) extends Formula {
    override def toString: String = {
      def wrap(formula: Formula): String = formula match {
        case True | False | Cmp(_, _, _) | Div(_, _) | And(_, _) => formula.toString
        case _                                                   => s"($formula)"
      }

      s"${wrap(left)} ∧ ${wrap(right)}"
    }
  }

  /** A logical disjunction formula `F ∨ F`. */
  final case class Or(left: Formula, right: Formula) extends Formula {
    override def toString: String = {
      def wrap(formula: Formula): String = formula match {
        case True | False | Cmp(_, _, _) | Div(_, _) | And(_, _) | Or(_, _) => formula.toString
        case _                                                              => s"($formula)"
      }

      s"${wrap(left)} ∨ ${wrap(right)}"
    }
  }

  /** A logical negation formula `¬F`. */
  final case class Not(formula: Formula) extends Formula {
    override def toString: String = {
      def wrap(formula: Formula): String = formula match {
        case True | False | Not(_) => formula.toString
        case _                     => s"($formula)"
      }

      s"¬${wrap(formula)}"
    }
  }

  /** A universal quantifier formula `∀ x. F`. */
  final case class ForAll(name: Name, formula: Formula) extends Formula {
    override def toString: String = s"∀ $name. $formula"
  }

  /** An existential quantifier formula `∃ x. F`. */
  final case class Exist(name: Name, formula: Formula) extends Formula {
    override def toString: String = s"∃ $name. $formula"
  }

  /** CmpOp is a kind of comparison operators. */
  sealed abstract class CmpOp extends Product with Serializable

  /** A less-than operator. */
  case object LT extends CmpOp {
    override def toString: String = "<"
  }

  /** A less-than or equal operator. */
  case object LE extends CmpOp {
    override def toString: String = "≤"
  }

  /** A greater-than operator. */
  case object GT extends CmpOp {
    override def toString: String = ">"
  }

  /** A greater-than or equal operator. */
  case object GE extends CmpOp {
    override def toString: String = "≥"
  }

  /** An equal operator. */
  case object EQ extends CmpOp {
    override def toString: String = "="
  }

  /** A not-equal operator. */
  case object NE extends CmpOp {
    override def toString: String = "≠"
  }
}
