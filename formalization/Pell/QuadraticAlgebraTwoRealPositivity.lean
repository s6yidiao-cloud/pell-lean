import Pell.QuadraticOrderPellRealEmbedding

/-!
# Positivity at the two displayed real embeddings of a quadratic algebra

For a nonnegative radicand, this module fixes the two elementary maps from
`rationalQuadraticAlgebra d` to `ℝ` that send its distinguished root to
`sqrt d` and `-sqrt d`.  It packages strict positivity at those two maps in a
small predicate and proves only its elementary multiplicative closure.

The predicate is deliberately tied to these two displayed maps.  This module
does not define a narrow class group, an orientation quotient, or a
correspondence with binary quadratic forms.
-/

namespace PellPaper

noncomputable section

/-- The second displayed real embedding of the concrete rational quadratic
algebra, sending its distinguished root to `-sqrt d`. -/
noncomputable def rationalQuadraticAlgebraNegativeRealEmbedding (d : ℤ) (hd : 0 ≤ d) :
    rationalQuadraticAlgebra d →ₐ[ℚ] ℝ :=
  QuadraticAlgebra.lift ⟨-Real.sqrt (d : ℝ), by
    rw [zero_smul, add_zero]
    simp only [Algebra.smul_def, mul_one, neg_mul_neg]
    exact Real.mul_self_sqrt (by exact_mod_cast hd)⟩

/-- The negative displayed embedding sends the distinguished root to
`-sqrt d`. -/
@[simp]
theorem rationalQuadraticAlgebraNegativeRealEmbedding_omega (d : ℤ) (hd : 0 ≤ d) :
    rationalQuadraticAlgebraNegativeRealEmbedding d hd QuadraticAlgebra.omega =
      -Real.sqrt (d : ℝ) := by
  simp [rationalQuadraticAlgebraNegativeRealEmbedding]

/-- Strict positivity at the two explicitly displayed real embeddings of the
concrete quadratic algebra.  It is a local sign predicate, not a definition
of a narrow class or orientation quotient. -/
def rationalQuadraticAlgebraPositiveAtBothRealEmbeddings
    (d : ℤ) (hd : 0 ≤ d) (x : rationalQuadraticAlgebra d) : Prop :=
  0 < rationalQuadraticAlgebraRealEmbedding d hd x ∧
    0 < rationalQuadraticAlgebraNegativeRealEmbedding d hd x

/-- One is positive at both displayed real embeddings. -/
theorem rationalQuadraticAlgebraPositiveAtBothRealEmbeddings_one
    (d : ℤ) (hd : 0 ≤ d) :
    rationalQuadraticAlgebraPositiveAtBothRealEmbeddings d hd 1 := by
  simp [rationalQuadraticAlgebraPositiveAtBothRealEmbeddings]

/-- Positivity at both displayed real embeddings is closed under products. -/
theorem rationalQuadraticAlgebraPositiveAtBothRealEmbeddings_mul
    {d : ℤ} {hd : 0 ≤ d} {x y : rationalQuadraticAlgebra d}
    (hx : rationalQuadraticAlgebraPositiveAtBothRealEmbeddings d hd x)
    (hy : rationalQuadraticAlgebraPositiveAtBothRealEmbeddings d hd y) :
    rationalQuadraticAlgebraPositiveAtBothRealEmbeddings d hd (x * y) := by
  exact ⟨by
      simpa only [map_mul] using mul_pos hx.1 hy.1,
    by
      simpa only [map_mul] using mul_pos hx.2 hy.2⟩

/-- A negative value at the second displayed real embedding excludes
positivity at both displayed real embeddings. -/
theorem not_rationalQuadraticAlgebraPositiveAtBothRealEmbeddings_of_negativeEmbedding
    {d : ℤ} {hd : 0 ≤ d} {x : rationalQuadraticAlgebra d}
    (hx : rationalQuadraticAlgebraNegativeRealEmbedding d hd x < 0) :
    ¬ rationalQuadraticAlgebraPositiveAtBothRealEmbeddings d hd x := by
  intro hpositive
  exact (not_lt_of_ge hpositive.2.le) hx

end

end PellPaper
