import Pell.BinaryQuadraticLinearEliminant
import Pell.DyadicComparableCostPolynomialMeshActualCell
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Literal raw Pell surface and its existing tuple coordinates

The source vector is (d,e) and the target vector is (v,u), so the fixed
quadratic-linear form is v*e²-u*d². Its eliminant is exactly
h*(y₀*A²-y₁*B²). The natural tuple embedding is the accepted raw
pair-coordinate embedding followed by the product of the installed
pair/vector equivalences. This is not a reduced-basis coordinate change,
a primitivity theorem, or a square-count estimate.
-/

namespace PellPaper

noncomputable section

/-- The six literal Pell-surface coefficients, with the first index giving
the exponent of the second source coordinate and the second the target index. -/
def rawPellQuadraticLinearCoefficients : Fin 3 → Fin 2 → ℤ :=
  ![![0, -1], ![0, 0], ![1, 0]]

/-- Universal signed integral evaluation in raw source (d,e), target (v,u)
order. No positivity, primitivity or nonzero-norm assumption is used. -/
theorem quadraticLinearFormEval_rawPell (d e u v : ℤ) :
    quadraticLinearFormEval rawPellQuadraticLinearCoefficients ![d, e] ![v, u] =
      v * e ^ 2 - u * d ^ 2 := by
  simp [quadraticLinearFormEval, rawPellQuadraticLinearCoefficients, Fin.sum_univ_succ]
  ring

/-- Literal substitution (B,-A) into the raw surface. Zero level, zero
components and nonhomogeneous input polynomials are all allowed. -/
theorem quadraticLinearEliminant_rawPell (h : ℤ)
    (A B : MvPolynomial (Fin 2) ℤ) :
    quadraticLinearEliminant rawPellQuadraticLinearCoefficients h A B =
      MvPolynomial.C h * (MvPolynomial.X 0 * A ^ 2 - MvPolynomial.X 1 * B ^ 2) := by
  unfold quadraticLinearEliminant
  congr 1
  simp [rawPellQuadraticLinearCoefficients, Fin.sum_univ_succ]
  ring

/-- Convert the already embedded raw pair-of-pairs to a pair of Fin-2
vectors. Injectivity is inherited by composition, not proved again for tuples. -/
def dyadicFactorTupleToRawPellVectorPointEmbedding :
    (ℕ × ℕ × ℕ × ℕ) ↪ ((Fin 2 → ℤ) × (Fin 2 → ℤ)) :=
  dyadicFactorTupleToGeneralBidegreeFormPointEmbedding.trans
    (Equiv.prodCongr (finTwoArrowEquiv ℤ).symm (finTwoArrowEquiv ℤ).symm).toEmbedding

/-- The composed embedding has the exact raw source and reversed-target
order used by the original two-layer coefficients. -/
@[simp] theorem dyadicFactorTupleToRawPellVectorPointEmbedding_apply
    (q : ℕ × ℕ × ℕ × ℕ) :
    dyadicFactorTupleToRawPellVectorPointEmbedding q =
      (![(q.1 : ℤ), (q.2.1 : ℤ)], ![(q.2.2.2 : ℤ), (q.2.2.1 : ℤ)]) := by
  rfl

/-- The surface value at the composed actual tuple embedding is the literal
integer signed norm; in particular no natural truncated subtraction appears. -/
theorem quadraticLinearFormEval_dyadicFactorTupleToRawPellVectorPoint
    (q : ℕ × ℕ × ℕ × ℕ) :
    quadraticLinearFormEval rawPellQuadraticLinearCoefficients
      (dyadicFactorTupleToRawPellVectorPointEmbedding q).1
      (dyadicFactorTupleToRawPellVectorPointEmbedding q).2 =
        (q.2.2.2 : ℤ) * (q.2.1 : ℤ) ^ 2 - (q.2.2.1 : ℤ) * (q.1 : ℤ) ^ 2 := by
  rw [dyadicFactorTupleToRawPellVectorPointEmbedding_apply]
  exact quadraticLinearFormEval_rawPell _ _ _ _

end
end PellPaper
