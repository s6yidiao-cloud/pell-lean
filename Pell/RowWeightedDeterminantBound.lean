import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# A row-weighted Leibniz determinant bound

For the Taylor coefficient matrix, all entries in one exponent row have the
same decay scale, while different rows have different scales.  This elementary
Leibniz estimate preserves the product of those row scales instead of
discarding it for a uniform maximum.
-/

namespace PellPaper

open scoped BigOperators

/-- If every entry in row `i` of a real square matrix is bounded by a
nonnegative scale `K i`, then the determinant is bounded by `n!` times the
product of the row scales. -/
theorem abs_det_le_factorial_mul_prod_rowBounds
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (K : ι → ℝ)
    (hbound : ∀ i j, |A i j| ≤ K i) :
    |A.det| ≤ (Nat.factorial (Fintype.card ι) : ℝ) * ∏ i, K i := by
  rw [Matrix.det_apply']
  calc
    |∑ σ : Equiv.Perm ι, ((σ.sign : ℤ) : ℝ) * ∏ i, A (σ i) i| ≤
        ∑ σ : Equiv.Perm ι, |((σ.sign : ℤ) : ℝ) * ∏ i, A (σ i) i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ σ : Equiv.Perm ι, ∏ i, |A (σ i) i| := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [abs_mul, ← Int.cast_abs,
        Equiv.Perm.sign_abs, Int.cast_one, one_mul, Finset.abs_prod]
    _ ≤ ∑ σ : Equiv.Perm ι, ∏ i, K (σ i) := by
      apply Finset.sum_le_sum
      intro σ _
      apply Finset.prod_le_prod
      · intro i _
        exact abs_nonneg _
      intro i _
      exact hbound (σ i) i
    _ = ∑ σ : Equiv.Perm ι, ∏ i, K i := by
      apply Finset.sum_congr rfl
      intro σ _
      exact Function.Bijective.prod_comp σ.bijective K
    _ = (Fintype.card (Equiv.Perm ι) : ℝ) * ∏ i, K i := by
      simp [nsmul_eq_mul]
    _ = (Nat.factorial (Fintype.card ι) : ℝ) * ∏ i, K i := by
      rw [Fintype.card_perm]

end PellPaper
