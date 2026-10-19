import Pell.IntegralCofactorKernelHadamard
import Pell.IntegralSelectedCofactorKernel
import Pell.IntegralRowSpanKernelTransport

/-!
# Sharp Hadamard bounds on a selected-column cofactor kernel

This module transports the sharp real-valued Hadamard coefficient bound from
`IntegralCofactorKernelHadamard` through the zero extension along an explicitly
given injective family of selected columns.  The selected columns must already
be the augmented block `[M | b]`; no theorem here chooses them from a
rectangular matrix.  The optional row transport likewise requires an explicit
integral row-combination certificate.

The bound remains real-valued so that the exact factor `sqrt r` is preserved:
`(|z j| : ℝ) ≤ (sqrt r * K)^r`.
-/

namespace PellPaper

open scoped BigOperators EuclideanSpace

/-- Every coordinate of the cofactor vector extended by zero outside an
injectively selected column family satisfies the sharp Hadamard bound for the
underlying selected block. -/
theorem abs_selectedCofactorKernel_le_hadamard {r : ℕ} {κ : Type*}
    (M : Matrix (Fin r) (Fin r) ℤ) (b : Fin r → ℤ) (e : Fin r.succ ↪ κ) {K : ℤ}
    (hK : 0 ≤ K) (hM : ∀ i j, |M i j| ≤ K) (hb : ∀ i, |b i| ≤ K)
    (j : κ) :
    (|selectedCofactorKernel M b e j| : ℝ) ≤ (√(r : ℝ) * (K : ℝ)) ^ r := by
  classical
  by_cases hj : j ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hj
    rw [selectedCofactorKernel_apply_selected]
    exact abs_cofactorKernelVector_le_hadamard M b hK hM hb i
  · simp only [selectedCofactorKernel_apply_not_mem_range M b e j hj, Int.cast_zero,
      abs_zero]
    exact pow_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (by exact_mod_cast hK)) _

/-- A nonsingular selected integral cofactor block has a nonzero ambient
right-kernel vector whose coefficients obey the exact real-valued Hadamard
bound.  This transports only through the displayed selected columns; it makes
no pivot-selection, rank, determinant-decay, or counting assertion. -/
theorem exists_nonzero_real_bounded_integral_kernel_of_selectedCofactorBlock_hadamard
    {r : ℕ} {κ : Type*} [Fintype κ]
    (A : Matrix (Fin r) κ ℤ) (M : Matrix (Fin r) (Fin r) ℤ) (b : Fin r → ℤ)
    (e : Fin r.succ ↪ κ) {K : ℤ}
    (hselected : A.submatrix id e = cofactorAugmentedMatrix M b)
    (hdet : M.det ≠ 0) (hK : 0 ≤ K)
    (hM : ∀ i j, |M i j| ≤ K) (hb : ∀ i, |b i| ≤ K) :
    ∃ z : κ → ℤ, z ≠ 0 ∧ A.mulVec z = 0 ∧
      ∀ j, (|z j| : ℝ) ≤ (√(r : ℝ) * (K : ℝ)) ^ r := by
  classical
  refine ⟨selectedCofactorKernel M b e, selectedCofactorKernel_ne_zero M b e hdet,
    mulVec_selectedCofactorKernel_eq_zero A M b e hselected, ?_⟩
  exact abs_selectedCofactorKernel_le_hadamard M b e hK hM hb

/-- The selected-column Hadamard kernel also propagates to all rows when an
explicit integral row-combination certificate is supplied.  The certificate
is an assumption, not a consequence of a rank or minor-selection theorem. -/
theorem exists_nonzero_real_bounded_integral_kernel_of_selectedCofactorBlock_of_integerRowCombination_hadamard
    {ι κ : Type*} [Fintype κ] {r : ℕ}
    (A : Matrix ι κ ℤ) (s : Fin r → ι) (c : ι → Fin r → ℤ)
    (M : Matrix (Fin r) (Fin r) ℤ) (b : Fin r → ℤ) (e : Fin r.succ ↪ κ)
    {K : ℤ} (hcombination : HasIntegerRowCombination A s c)
    (hblock : A.submatrix s e = cofactorAugmentedMatrix M b)
    (hdet : M.det ≠ 0) (hK : 0 ≤ K)
    (hM : ∀ i j, |M i j| ≤ K) (hb : ∀ i, |b i| ≤ K) :
    ∃ z : κ → ℤ, z ≠ 0 ∧ A.mulVec z = 0 ∧
      ∀ j, (|z j| : ℝ) ≤ (√(r : ℝ) * (K : ℝ)) ^ r := by
  classical
  refine ⟨selectedCofactorKernel M b e, selectedCofactorKernel_ne_zero M b e hdet,
    mulVec_selectedCofactorKernel_eq_zero_of_integerRowCombination
      A s c M b e hcombination hblock, ?_⟩
  exact abs_selectedCofactorKernel_le_hadamard M b e hK hM hb

end PellPaper
