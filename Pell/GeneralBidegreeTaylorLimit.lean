import Pell.GeneralBidegreeFiniteTaylorSelection
import Pell.FiniteDeterminantConvergence
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Analytic limit of rectangular Taylor truncations

This module starts the analytic bridge omitted by the finite Taylor-selection
argument for `L:sheared` in `main.tex`.  It records the standard convergence
of the one-variable exponential Taylor sums, in the exact `Finset.range`
normalization used by finite determinant expansions.  Subsequent lemmas can
use it entrywise for the rectangular two-variable truncations.

No determinant decay estimate is claimed here.
-/

namespace PellPaper

open scoped BigOperators Topology

/-- The degree-`N-1` Taylor approximation to the real exponential. -/
noncomputable def partialExp (z : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, z ^ n / (Nat.factorial n : ℝ)

/-- The finite Taylor sums converge to the real exponential. -/
theorem tendsto_partialExp (z : ℝ) :
    Filter.Tendsto (partialExp z) Filter.atTop (𝓝 (Real.exp z)) := by
  rw [Real.exp_eq_exp_ℝ]
  change Filter.Tendsto
    (fun N : ℕ => ∑ n ∈ Finset.range N, z ^ n / (Nat.factorial n : ℝ))
    Filter.atTop (𝓝 (NormedSpace.exp z))
  exact
    (NormedSpace.expSeries_div_hasSum_exp z).tendsto_sum_nat

/-- The rectangular two-variable Taylor sum through degrees `< N` in both
variables. -/
noncomputable def rectangularPartialExp (x y : ℝ) (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
    (x ^ i / (Nat.factorial i : ℝ)) * (y ^ j / (Nat.factorial j : ℝ))

/-- A rectangular Taylor sum separates into the two one-variable partial
exponential sums. -/
theorem rectangularPartialExp_eq_mul_partialExp (x y : ℝ) (N : ℕ) :
    rectangularPartialExp x y N = partialExp x N * partialExp y N := by
  simp only [rectangularPartialExp, partialExp, Finset.sum_mul_sum]

/-- Rectangular finite Taylor sums converge to the product of their two
exponential limits. -/
theorem tendsto_rectangularPartialExp (x y : ℝ) :
    Filter.Tendsto (rectangularPartialExp x y) Filter.atTop
      (𝓝 (Real.exp x * Real.exp y)) := by
  rw [show rectangularPartialExp x y = fun N => partialExp x N * partialExp y N by
    funext N
    exact rectangularPartialExp_eq_mul_partialExp x y N]
  exact (tendsto_partialExp x).mul (tendsto_partialExp y)

/-- The rectangular analytic Taylor truncation at one row/column pair of the
sheared coefficient grid.  The two variables are truncated to the same degree
bound, as in the square finite determinant approximation. -/
noncomputable def generalBidegreeRectangularTaylorEvaluationMatrix
    (A B : ℕ) (α β : generalBidegreeGrid A B → ℝ) (N : ℕ) :
    Matrix (generalBidegreeGrid A B) (generalBidegreeGrid A B) ℝ :=
  fun r p => rectangularPartialExp
    (α r * (p.1.1 : ℝ)) (β r * (p.1.2 : ℝ)) N

/-- The limiting exponential evaluation matrix corresponding to the
rectangular Taylor truncations. -/
noncomputable def generalBidegreeExponentialEvaluationMatrix
    (A B : ℕ) (α β : generalBidegreeGrid A B → ℝ) :
    Matrix (generalBidegreeGrid A B) (generalBidegreeGrid A B) ℝ :=
  fun r p => Real.exp (α r * (p.1.1 : ℝ)) *
    Real.exp (β r * (p.1.2 : ℝ))

/-- The same limiting matrix in the literal sheared-exponential form from
`L:sheared`: `exp(N₁ α + N₂ β)`. -/
noncomputable def generalBidegreeShearedExponentialEvaluationMatrix
    (A B : ℕ) (α β : generalBidegreeGrid A B → ℝ) :
    Matrix (generalBidegreeGrid A B) (generalBidegreeGrid A B) ℝ :=
  fun r p => Real.exp ((p.1.1 : ℝ) * α r + (p.1.2 : ℝ) * β r)

/-- The product exponential limit is exactly the sheared column exponential
used in the manuscript. -/
theorem generalBidegreeExponentialEvaluationMatrix_eq_sheared
    (A B : ℕ) (α β : generalBidegreeGrid A B → ℝ) :
    generalBidegreeExponentialEvaluationMatrix A B α β =
      generalBidegreeShearedExponentialEvaluationMatrix A B α β := by
  ext r p
  simp only [generalBidegreeExponentialEvaluationMatrix,
    generalBidegreeShearedExponentialEvaluationMatrix]
  rw [← Real.exp_add]
  congr 1
  ring

/-- Entrywise, the rectangular finite Taylor evaluation matrices converge to
the exponential evaluation matrix.  This is the analytic approximation fact
needed before a determinant-continuity argument can transfer a nonzero
exponential determinant to a finite truncation. -/
theorem tendsto_generalBidegreeRectangularTaylorEvaluationMatrix
    (A B : ℕ) (α β : generalBidegreeGrid A B → ℝ) :
    Filter.Tendsto
      (generalBidegreeRectangularTaylorEvaluationMatrix A B α β)
      Filter.atTop
      (𝓝 (generalBidegreeExponentialEvaluationMatrix A B α β)) := by
  apply tendsto_matrix_of_tendsto_entries
  intro r p
  exact tendsto_rectangularPartialExp
    (α r * (p.1.1 : ℝ)) (β r * (p.1.2 : ℝ))

/-- The determinants of the rectangular finite Taylor matrices converge to
the determinant of the sheared exponential evaluation matrix.  This is the
exact “remove the truncation” continuity statement before any quantitative
Hadamard bound is supplied. -/
theorem tendsto_det_generalBidegreeRectangularTaylorEvaluationMatrix
    (A B : ℕ) (α β : generalBidegreeGrid A B → ℝ) :
    Filter.Tendsto
      (fun N =>
        (generalBidegreeRectangularTaylorEvaluationMatrix A B α β N).det)
      Filter.atTop
      (𝓝 ((generalBidegreeExponentialEvaluationMatrix A B α β).det)) := by
  apply tendsto_det_of_tendsto_matrix
  exact tendsto_generalBidegreeRectangularTaylorEvaluationMatrix A B α β

/-- If the limiting exponential evaluation determinant is nonzero, then all
sufficiently long rectangular Taylor truncations have nonzero determinants.
This closes the topological half of the finite-truncation handoff for
`L:sheared`; proving nonvanishing of the limiting determinant remains a
separate source-specific task. -/
theorem exists_tail_det_ne_zero_generalBidegreeRectangularTaylorEvaluationMatrix
    (A B : ℕ) (α β : generalBidegreeGrid A B → ℝ)
    (hdet : (generalBidegreeExponentialEvaluationMatrix A B α β).det ≠ 0) :
    ∃ N : ℕ, ∀ k ≥ N,
      (generalBidegreeRectangularTaylorEvaluationMatrix A B α β k).det ≠ 0 := by
  apply exists_tail_det_ne_zero_of_tendsto_entries_atTop
    (generalBidegreeRectangularTaylorEvaluationMatrix A B α β)
    (generalBidegreeExponentialEvaluationMatrix A B α β)
  · intro r p
    exact tendsto_rectangularPartialExp
      (α r * (p.1.1 : ℝ)) (β r * (p.1.2 : ℝ))
  · exact hdet

end PellPaper
