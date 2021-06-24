package codes.quine.labo.presburger

import codes.quine.labo.presburger.Formula._
import codes.quine.labo.presburger.Term._

class FormulaSuite extends munit.FunSuite {
  // `exist x. (3x + 1 < 10 \/ 7x - 6 > 7) /\ 2 | x`
  // From http://www2.imm.dtu.dk/courses/02917/Presburger1.pdf.
  val f1: Exist = Exist(
    "x",
    And(
      Or(Cmp(LT, Add(Mul(3, Var("x")), Const(1)), Const(10)), Cmp(GT, Sub(Mul(7, Var("x")), Const(6)), Const(7))),
      Div(2, Var("x"))
    )
  )
  // `exist x. 256 | 6x + 10 /\ x < 0 /\ (forall y. 9x < 4y \/ 5y < 461)`
  // When `x == 41`, this formula is satisfied.
  val f2: Exist = Exist(
    "x",
    And(
      And(Div(256, Add(Mul(6, Var("x")), Const(10))), Cmp(LE, Const(0), Var("x"))),
      ForAll("y", Or(Cmp(LT, Mul(9, Var("x")), Mul(4, Var("y"))), Cmp(LT, Mul(5, Var("y")), Const(461))))
    )
  )
  // `exist x. 256 | 6x + 10 /\ x < 0 /\ (forall y. 9x < 4y \/ 5y < 460)`
  val f3: Exist = Exist(
    "x",
    And(
      And(Div(256, Add(Mul(6, Var("x")), Const(10))), Cmp(LE, Const(0), Var("x"))),
      ForAll("y", Or(Cmp(LT, Mul(9, Var("x")), Mul(4, Var("y"))), Cmp(LT, Mul(5, Var("y")), Const(460))))
    )
  )

  test("Formula#toNNFFormula") {
    assertEquals(
      f1.toNNFFormula,
      NNFFormula.BigOr(
        "x",
        42,
        NNFFormula.Or(
          NNFFormula.And(NNFFormula.Div(42, LinTerm.Var("x")), NNFFormula.Div(21, LinTerm.Var("x"))),
          NNFFormula.And(
            NNFFormula.And(
              NNFFormula.Or(
                NNFFormula.LessThanZero(LinTerm.Var("x") - 24),
                NNFFormula.LessThanZero(-1 *: LinTerm.Var("x"))
              ),
              NNFFormula.Div(42, LinTerm.Var("x") + 39)
            ),
            NNFFormula.Div(21, LinTerm.Var("x") + 39)
          )
        )
      )
    )
  }

  test("Formula#verify") {
    assertEquals(f1.verify(), true)
    assertEquals(f2.verify(), true)
    assertEquals(f3.verify(), false)
  }
}
