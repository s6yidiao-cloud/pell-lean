import Pell.FullColumnMinorRankDefect
import Pell.IntegralRankDefectHadamardKernel
import Pell.IntegralDeterminantVanishing

/-!
# Bounded integral kernels from vanishing full minors

This module joins the final two finite-linear-algebra steps of the
approximate determinant method.  If all full-column integral minors vanish,
the rationalized matrix has strict column-rank defect; the automatic cofactor
construction then produces a nonzero integral right kernel with its sharp
Hadamard coefficient bound.

The second theorem accepts the usual strict real determinant bound below one
and invokes integrality to obtain the vanishing-minor premise.  Neither
theorem estimates those determinants, chooses a source-specific coordinate
matrix, or counts points.
-/

namespace PellPaper

open scoped EuclideanSpace

/-- Vanishing of every full-column integral minor of a finite matrix, together
with an entrywise bound by a nonnegative integer `K`, produces a nonzero
integral right-kernel vector.  Its coefficient bound is the exact real
Hadamard scale `(sqrt r * K)^r` for some `r` strictly smaller than the number
of columns.

This is a finite algebraic bridge only: the all-minors premise is retained
explicitly and no determinant-decay or point-counting assertion is made. -/
theorem exists_nonzero_real_bounded_integral_kernel_of_forall_fullIntegralColumnMinors_eq_zero_hadamard
    {ι κ : Type*} [Finite ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℤ) {K : ℤ}
    (hminor : ∀ s : κ ↪ ι, (A.submatrix s id).det = 0)
    (hK : 0 ≤ K) (hbound : ∀ i j, |A i j| ≤ K) :
    ∃ r : ℕ, r < Fintype.card κ ∧ ∃ z : κ → ℤ, z ≠ 0 ∧ A.mulVec z = 0 ∧
      ∀ j, (|z j| : ℝ) ≤ (√(r : ℝ) * (K : ℝ)) ^ r := by
  apply exists_nonzero_real_bounded_integral_kernel_of_rationalRank_lt_card_hadamard
    A (rationalRank_lt_card_of_forall_fullIntegralColumnMinors_eq_zero A hminor)
    hK hbound

/-- The determinant-method version of the bounded-kernel bridge.  If every
full-column integral minor has real absolute value strictly below one, then
all those integer determinants vanish, so the preceding theorem supplies a
nonzero integral kernel at sharp Hadamard scale.

The strict minor bounds remain hypotheses: this theorem does not establish
their analytic decay. -/
theorem exists_nonzero_real_bounded_integral_kernel_of_forall_fullIntegralColumnMinors_abs_cast_lt_one_hadamard
    {ι κ : Type*} [Finite ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℤ) {K : ℤ}
    (hminor : ∀ s : κ ↪ ι, |(((A.submatrix s id).det : ℝ))| < 1)
    (hK : 0 ≤ K) (hbound : ∀ i j, |A i j| ≤ K) :
    ∃ r : ℕ, r < Fintype.card κ ∧ ∃ z : κ → ℤ, z ≠ 0 ∧ A.mulVec z = 0 ∧
      ∀ j, (|z j| : ℝ) ≤ (√(r : ℝ) * (K : ℝ)) ^ r := by
  apply
    exists_nonzero_real_bounded_integral_kernel_of_forall_fullIntegralColumnMinors_eq_zero_hadamard
      A (fun s => integral_det_eq_zero_of_abs_cast_lt_one _ (hminor s)) hK hbound

end PellPaper
