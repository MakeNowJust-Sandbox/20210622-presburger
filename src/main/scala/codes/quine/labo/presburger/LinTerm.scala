package codes.quine.labo.presburger

import scala.collection.immutable.SortedMap

/** LinTerm is a linear form term. */
final case class LinTerm(const: Z, coefficients: SortedMap[Name, Z]) {

  /** Checks whether or not this term contains a constant value only. */
  def isConst: Boolean = coefficients.isEmpty

  /** Returns a coefficient value of the given named variable. */
  def coefficient(name: Name): Z = coefficients.getOrElse(name, 0)

  /** Checks the given named variable is contained in this term. */
  def contains(name: Name): Boolean = coefficients.contains(name)

  /** Returns a new linear form term in which coefficient of the given variable is `0`. */
  def removed(name: Name): LinTerm = LinTerm(const, coefficients.removed(name))

  /** Returns a new linear form term which is addition between the two terms. */
  def +(that: LinTerm): LinTerm = {
    val const = this.const + that.const
    val names = this.coefficients.keySet | that.coefficients.keySet
    val coefficients = SortedMap.from {
      names.iterator
        .map { name => name -> (this.coefficient(name) + that.coefficient(name)) }
        .filter(_._2 != 0)
    }
    LinTerm(const, coefficients)
  }

  /** Returns a new linear form term which is addition between this term and the integer value. */
  def +(value: Z): LinTerm = LinTerm(const + value, coefficients)

  /** Returns a new linear form term which is subtraction between the two terms. */
  def -(that: LinTerm): LinTerm = this + (-1 *: that)

  /** Returns a new linear form term which is subtraction between this term and the integer value. */
  def -(value: Z): LinTerm = LinTerm(const - value, coefficients)

  /** Returns a new linear form term which is multiplication between the integer value and this term. */
  def *:(value: Z): LinTerm = {
    val const = value * this.const
    val coefficients = SortedMap.from(this.coefficients.view.mapValues(value * _))
    LinTerm(const, coefficients)
  }

  /** Returns a pair of a correction coefficient and a normalized linear form on the given named variable.
    *
    * The named variable's coefficient in the result formula is corrected to `1` or `-1`,
    * and other coefficients and the constant value are also corrected.
    *
    * When this formula does not contains the given variable, it returns `(1, this)` instead.
    */
  def normalize(name: Name, lcm: Z): (Z, LinTerm) =
    if (contains(name)) {
      val k = coefficients(name)
      val n = lcm / k.abs
      (n, n *: removed(name) + k.sign *: LinTerm.Var(name))
    } else (1, this)

  /** Returns a new linear form term in which the given term is assigned to the given named variable. */
  def assign(name: Name, term: LinTerm): LinTerm =
    if (contains(name)) removed(name) + coefficient(name) *: term else this

  /** Evaluated this term on the given environment. */
  def evaluate(env: Map[Name, Z]): Z = {
    val sum = coefficients.map { case (x, k) =>
      val v = env.getOrElse(x, throw new IllegalArgumentException(s"Found free variable: $x"))
      k * v
    }.sum
    const + sum
  }

  override def toString: String =
    if (const == 0 && coefficients.isEmpty) "0"
    else {
      val const = if (this.const == 0) "" else s"${this.const} "
      val coefficients = this.coefficients.iterator
        .map {
          case (x, k) if k == 1  => s"+ $x"
          case (x, k) if k == -1 => s"- $x"
          case (x, k) if k > 0   => s"+ $k$x"
          case (x, k) if k < 0   => s"- ${k.abs}$x"
        }
        .mkString(" ")
      val s = s"$const$coefficients"
      if (s.startsWith("+ ")) s.slice(2, s.length) else if (s.endsWith(" ")) s.slice(0, s.length - 1) else s
    }
}

object LinTerm {

  /** Returns a linear form term having the given value. */
  def Const(value: Z): LinTerm = LinTerm(value, SortedMap.empty)

  /** Returns a linear form term having a variable of the given name. */
  def Var(name: Name): LinTerm = LinTerm(0, SortedMap(name -> 1))
}
