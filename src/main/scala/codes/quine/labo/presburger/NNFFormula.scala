package codes.quine.labo.presburger

/** NNFFormula is a quantifier-free negation normal form formula.
  *
  * {{{
  * F ::= ⊤              (* tautology *)
  *     | ⊥              (* contradiction *)
  *     | t < 0          (* less-than-zero constraint *)
  *     | k ∣ t          (* divisibility constraint *)
  *     | k ∤ t          (* negated divisibility constraint *)
  *     | F ∧ F          (* logical disjunction *)
  *     | F ∨ F          (* logical conjunction *)
  *     | ⋀ x ∈ [1,k]. F (* logical conjunction over a range *)
  *     | ⋁ x ∈ [1,k]. F (* logical disjunction over a range *)
  * }}}
  */
sealed abstract class NNFFormula {

  /** Returns a negated formula. */
  def negate: NNFFormula

  /** Collects coefficient values of the given named variable. */
  def coefficients(name: Name): Set[Z]

  /** Collects left-hand-side values of divisible constraints on the given named variable. */
  def divs(name: Name): Set[Z]

  /** Returns a normalized formula on the given named variable. */
  def normalize(name: Name, lcm: Z): NNFFormula

  /** Returns a new formula in which negative infinity is assigned to the given named variable. */
  def assignMinInf(name: Name): NNFFormula

  /** Collects lower bounds expressions on the given named variable. */
  def bounds(name: Name): Set[LinTerm]

  /** Returns a new formula in which the given term is assigned to the given named variable. */
  def assign(name: Name, term: LinTerm): NNFFormula

  /** Checks whether or not this formula is tautology on the given environment. */
  def verify(env: Map[Name, Z]): Boolean

  /** Checks whether or not this formula is tautology. */
  def verify(): Boolean = verify(Map.empty)
}

object NNFFormula {

  /** A tautology formula `⊤`. */
  case object True extends NNFFormula {
    def negate: NNFFormula = False
    def coefficients(name: Name): Set[Z] = Set.empty
    def divs(name: Name): Set[Z] = Set.empty
    def normalize(name: Name, lcm: Z): NNFFormula = True
    def assignMinInf(name: Name): NNFFormula = True
    def bounds(name: Name): Set[LinTerm] = Set.empty
    def assign(name: Name, term: LinTerm): NNFFormula = True
    def verify(env: Map[Name, Z]): Boolean = true

    override def toString: String = "⊤"
  }

  /** A contradiction formula `⊥`. */
  case object False extends NNFFormula {
    def negate: NNFFormula = True
    def coefficients(name: Name): Set[Z] = Set.empty
    def divs(name: Name): Set[Z] = Set.empty
    def normalize(name: Name, lcm: Z): NNFFormula = False
    def assignMinInf(name: Name): NNFFormula = False
    def bounds(name: Name): Set[LinTerm] = Set.empty
    def assign(name: Name, term: LinTerm): NNFFormula = False
    def verify(env: Map[Name, Z]): Boolean = false

    override def toString: String = "⊥"
  }

  /** A less-than-zero constraint formula `t < 0`. */
  final case class LessThanZero(term: LinTerm) extends NNFFormula {
    def negate: NNFFormula = LessThanZero(-1 *: term - 1) // not (t < 0) <=> t >= 0 <=> -1 < t && -t - 1 < 0
    def coefficients(name: Name): Set[Z] = term.coefficients.get(name).toSet
    def divs(name: Name): Set[Z] = Set.empty
    def normalize(name: Name, lcm: Z): NNFFormula = LessThanZero(term.normalize(name, lcm)._2)
    def assignMinInf(name: Name): NNFFormula = {
      val k = term.coefficient(name)
      if (k > 0) True
      else if (k < 0) False
      else this
    }
    def bounds(name: Name): Set[LinTerm] = {
      val k = term.coefficient(name)
      if (k < 0) Set(term.removed(name))
      else Set.empty
    }
    def assign(name: Name, term: LinTerm): NNFFormula = LessThanZero(this.term.assign(name, term))
    def verify(env: Map[Name, Z]): Boolean = term.evaluate(env) < 0

    override def toString: String = s"$term < 0"
  }

  object LessThanZero {
    def apply(term: LinTerm): NNFFormula =
      if (term.isConst) {
        if (term.const < 0) True else False
      } else new LessThanZero(term)
  }

  /** A divisibility constraint formula `k ∣ t`. */
  final case class Div(const: Z, term: LinTerm) extends NNFFormula {
    def negate: NNFFormula = NotDiv(const, term)
    def coefficients(name: Name): Set[Z] = term.coefficients.get(name).toSet
    def divs(name: Name): Set[Z] =
      if (term.coefficients.contains(name)) Set(const) else Set.empty
    def normalize(name: Name, lcm: Z): NNFFormula = {
      val (n, term) = this.term.normalize(name, lcm)
      Div(const * n, term)
    }
    def assignMinInf(name: Name): NNFFormula = this
    def bounds(name: Name): Set[LinTerm] = Set.empty
    def assign(name: Name, term: LinTerm): NNFFormula = Div(const, this.term.assign(name, term))
    def verify(env: Map[Name, Z]): Boolean = term.evaluate(env) % const == 0

    override def toString: String = s"$const ∣ $term"
  }

  object Div {
    def apply(const: Z, term: LinTerm): NNFFormula =
      if (const == 1 || const == -1) True
      else if (const == 0) And(LessThanZero(term - 1), LessThanZero(term - 1))
      else new Div(const, term)
  }

  /** A negated divisibility constraint formula `k ∤ t`. */
  final case class NotDiv(const: Z, term: LinTerm) extends NNFFormula {
    def negate: NNFFormula = Div(const, term)
    def coefficients(name: Name): Set[Z] = term.coefficients.get(name).toSet
    def divs(name: Name): Set[Z] =
      if (term.coefficients.contains(name)) Set(const) else Set.empty
    def normalize(name: Name, lcm: Z): NNFFormula = {
      val (n, term) = this.term.normalize(name, lcm)
      NotDiv(const * n, term)
    }
    def assignMinInf(name: Name): NNFFormula = this
    def bounds(name: Name): Set[LinTerm] = Set.empty
    def assign(name: Name, term: LinTerm): NNFFormula = NotDiv(const, this.term.assign(name, term))
    def verify(env: Map[Name, Z]): Boolean = term.evaluate(env) % const != 0

    override def toString: String = s"$const ∤ $term"
  }

  /** A logical conjunction formula `F ∧ F`. */
  final case class And(left: NNFFormula, right: NNFFormula) extends NNFFormula {
    def negate: NNFFormula = Or(left.negate, right.negate)
    def coefficients(name: Name): Set[Z] = left.coefficients(name) | right.coefficients(name)
    def divs(name: Name): Set[Z] = left.divs(name) | right.divs(name)
    def normalize(name: Name, lcm: Z): NNFFormula = And(left.normalize(name, lcm), right.normalize(name, lcm))
    def assignMinInf(name: Name): NNFFormula = And(left.assignMinInf(name), right.assignMinInf(name))
    def bounds(name: Name): Set[LinTerm] = left.bounds(name) | right.bounds(name)
    def assign(name: Name, term: LinTerm): NNFFormula = And(left.assign(name, term), right.assign(name, term))
    def verify(env: Map[Name, Z]): Boolean = left.verify(env) && right.verify(env)

    override def toString: String = {
      def wrap(formula: NNFFormula): String = formula match {
        case True | False | LessThanZero(_) | Div(_, _) | NotDiv(_, _) | And(_, _) => formula.toString
        case _                                                                     => s"($formula)"
      }

      s"${wrap(left)} ∧ ${wrap(right)}"
    }
  }

  object And {
    def apply(left: NNFFormula, right: NNFFormula): NNFFormula = (left, right) match {
      case (False, _) => False
      case (_, False) => False
      case (True, r)  => r
      case (l, True)  => l
      case (l, r)     => new And(l, r)
    }
  }

  /** A logical disjunction formula `F ∨ F`. */
  final case class Or(left: NNFFormula, right: NNFFormula) extends NNFFormula {
    def negate: NNFFormula = And(left.negate, right.negate)
    def coefficients(name: Name): Set[Z] = left.coefficients(name) | right.coefficients(name)
    def divs(name: Name): Set[Z] = left.divs(name) | right.divs(name)
    def normalize(name: Name, lcm: Z): NNFFormula = Or(left.normalize(name, lcm), right.normalize(name, lcm))
    def assignMinInf(name: Name): NNFFormula = Or(left.assignMinInf(name), right.assignMinInf(name))
    def bounds(name: Name): Set[LinTerm] = left.bounds(name) | right.bounds(name)
    def assign(name: Name, term: LinTerm): NNFFormula = Or(left.assign(name, term), right.assign(name, term))
    def verify(env: Map[Name, Z]): Boolean = left.verify(env) || right.verify(env)

    override def toString: String = {
      def wrap(formula: NNFFormula): String = formula match {
        case True | False | LessThanZero(_) | Div(_, _) | NotDiv(_, _) | And(_, _) | Or(_, _) => formula.toString
        case _                                                                                => s"($formula)"
      }

      s"${wrap(left)} ∨ ${wrap(right)}"
    }
  }

  object Or {
    def apply(left: NNFFormula, right: NNFFormula): NNFFormula = (left, right) match {
      case (True, _)  => True
      case (_, True)  => True
      case (False, r) => r
      case (l, False) => l
      case (l, r)     => new Or(l, r)
    }
  }

  /** A logical conjunction formula over a range `⋀ x ∈ [1,k]. F`. */
  final case class BigAnd(name: Name, max: Z, formula: NNFFormula) extends NNFFormula {
    def negate: NNFFormula = BigOr(name, max, formula.negate)
    def coefficients(name: Name): Set[Z] =
      if (name == this.name) Set.empty else formula.coefficients(name)
    def divs(name: Name): Set[Z] =
      if (name == this.name) Set.empty else formula.divs(name)
    def normalize(name: Name, lcm: Z): NNFFormula = BigAnd(this.name, max, formula.normalize(name, lcm))
    def assignMinInf(name: Name): NNFFormula =
      if (name == this.name) this else BigAnd(this.name, max, formula.assignMinInf(name))
    def bounds(name: Name): Set[LinTerm] =
      if (name == this.name) Set.empty else formula.bounds(name)
    def assign(name: Name, term: LinTerm): NNFFormula =
      if (name == this.name) this else BigAnd(this.name, max, formula.assign(name, term))
    def verify(env: Map[Name, Z]): Boolean =
      Iterator.iterate(1: BigInt)(_ + 1).takeWhile(_ <= max).forall(i => formula.verify(env.updated(name, i)))

    override def toString: Name = s"⋀ $name ∈ [1,$max]. $formula"
  }

  /** A logical disjunction formula over a range `⋁ x ∈ [1,k]. F`. */
  final case class BigOr(name: Name, max: Z, formula: NNFFormula) extends NNFFormula {
    def negate: NNFFormula = BigAnd(name, max, formula.negate)
    def coefficients(name: Name): Set[Z] =
      if (name == this.name) Set.empty else formula.coefficients(name)
    def divs(name: Name): Set[Z] =
      if (name == this.name) Set.empty else formula.divs(name)
    def normalize(name: Name, lcm: Z): NNFFormula = BigOr(this.name, max, formula.normalize(name, lcm))
    def assignMinInf(name: Name): NNFFormula =
      if (name == this.name) this else BigOr(this.name, max, formula.assignMinInf(name))
    def bounds(name: Name): Set[LinTerm] =
      if (name == this.name) Set.empty else formula.bounds(name)
    def assign(name: Name, term: LinTerm): NNFFormula =
      if (name == this.name) this else BigOr(this.name, max, formula.assign(name, term))
    def verify(env: Map[Name, Z]): Boolean =
      Iterator.iterate(1: BigInt)(_ + 1).takeWhile(_ <= max).exists(i => formula.verify(env.updated(name, i)))

    override def toString: Name = s"⋁ $name ∈ [1,$max]. $formula"
  }
}
