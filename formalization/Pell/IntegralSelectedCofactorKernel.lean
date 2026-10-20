import Pell.IntegralCofactorKernelBound

/-!
# A bounded integral kernel supported on selected columns

This module transports the explicit cofactor kernel for `[M | b]` to an
ambient finite column type by extending it by zero outside an injectively
selected family of columns. It requires the selected columns, in the order
of the embedding, to be exactly `[M | b]`.

The coefficient estimate remains the factorial (Leibniz) determinant bound
from `IntegralCofactorKernelBound`; this is not the sharper Hadamard bound in
the manuscript. The module deliberately neither chooses a cofactor block
from a rectangular matrix nor propagates a relation through a row span.
-/

namespace PellPaper

open scoped BigOperators

/-- Extend the explicit cofactor vector for `[M | b]` by zero to an ambient
column type, along the injective selected-column map `e`. -/
noncomputable def selectedCofactorKernel {r : ℕ} {κ : Type*}
    (M : Matrix (Fin r) (Fin r) ℤ) (b : Fin r → ℤ) (e : Fin r.succ ↪ κ) : κ → ℤ :=
  by
    classical
    exact ∑ i : Fin r.succ, Pi.single (e i) (cofactorKernelVector M b i)

/-- On every selected column, zero extension recovers the original cofactor
coordinate. -/
theorem selectedCofactorKernel_apply_selected {r : ℕ} {κ : Type*}
    (M : Matrix (Fin r) (Fin r) ℤ) (b : Fin r → ℤ) (e : Fin r.succ ↪ κ)
    (j : Fin r.succ) :
    selectedCofactorKernel M b e (e j) = cofactorKernelVector M b j := by
  classical
  unfold selectedCofactorKernel
  simp only [Finset.sum_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    rw [Pi.single_apply]
    exact if_neg (fun hke => hkj (e.injective hke.symm))
  · simp

/-- The extended cofactor vector vanishes away from the selected columns. -/
theorem selectedCofactorKernel_apply_not_mem_range {r : ℕ} {κ : Type*}
    (M : Matrix (Fin r) (Fin r) ℤ) (b : Fin r → ℤ) (e : Fin r.succ ↪ κ)
    (j : κ) (hj : j ∉ Set.range e) :
    selectedCofactorKernel M b e j = 0 := by
  classical
  unfold selectedCofactorKernel
  simp only [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [Pi.single_apply]
  exact if_neg (fun hij => hj ⟨i, hij.symm⟩)

/-- A nonsingular square block makes its zero-extended cofactor vector
nonzero. -/
theorem selectedCofactorKernel_ne_zero {r : ℕ} {κ : Type*}
    (M : Matrix (Fin r) (Fin r) ℤ) (b : Fin r → ℤ) (e : Fin r.succ ↪ κ)
    (hdet : M.det ≠ 0) : selectedCofactorKernel M b e ≠ 0 := by
  classical
  intro hzero
  apply cofactorKernelVector_ne_zero M b hdet
  funext j
  have h := congr_fun hzero (e j)
  simpa only [selectedCofactorKernel_apply_selected, Pi.zero_apply] using h

/-- Matrix multiplication by the ambient zero extension is exactly matrix
multiplication by the selected-column submatrix and the original cofactor
vector. -/
theorem mulVec_selectedCofactorKernel_eq_submatrix_mulVec {r : ℕ} {ι κ : Type*}
    [Fintype κ] (A : Matrix ι κ ℤ) (M : Matrix (Fin r) (Fin r) ℤ)
    (b : Fin r → ℤ) (e : Fin r.succ ↪ κ) :
    A.mulVec (selectedCofactorKernel M b e) =
      (A.submatrix id e).mulVec (cofactorKernelVector M b) := by
  classical
  rw [selectedCofactorKernel, Matrix.mulVec_sum]
  ext x
  simp [Matrix.mulVec, dotProduct, mul_comm]

/-- Every ambient coordinate of the zero-extended cofactor vector satisfies
the same factorial/Leibniz bound as the corresponding block coordinate. -/
theorem abs_selectedCofactorKernel_le_factorial_mul_pow {r : ℕ} {κ : Type*}
    (M : Matrix (Fin r) (Fin r) ℤ) (b : Fin r → ℤ) (e : Fin r.succ ↪ κ) {K : ℤ}
    (hK : 0 ≤ K) (hM : ∀ i j, |M i j| ≤ K) (hb : ∀ i, |b i| ≤ K)
    (j : κ) :
    |selectedCofactorKernel M b e j| ≤ (r.factorial : ℤ) * K ^ r := by
  classical
  by_cases hj : j ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hj
    rw [selectedCofactorKernel_apply_selected]
    exact abs_cofactorKernelVector_le_factorial_mul_pow M b hK hM hb i
  · rw [selectedCofactorKernel_apply_not_mem_range M b e j hj, abs_zero]
    exact mul_nonneg (by exact_mod_cast Nat.zero_le r.factorial) (pow_nonneg hK _)

/-- If the selected `r + 1` columns of an ambient integral matrix are exactly
the augmented cofactor block `[M | b]`, their zero-extended cofactor vector
is a right-kernel vector of the ambient matrix. The rows are indexed by
`Fin r`: this theorem does not assert row-span transport to an additional
family of rows. -/
theorem mulVec_selectedCofactorKernel_eq_zero {r : ℕ} {κ : Type*} [Fintype κ]
    (A : Matrix (Fin r) κ ℤ) (M : Matrix (Fin r) (Fin r) ℤ) (b : Fin r → ℤ)
    (e : Fin r.succ ↪ κ)
    (hselected : A.submatrix id e = cofactorAugmentedMatrix M b) :
    A.mulVec (selectedCofactorKernel M b e) = 0 := by
  classical
  rw [mulVec_selectedCofactorKernel_eq_submatrix_mulVec, hselected]
  exact cofactorAugmentedMatrix_mulVec_cofactorKernelVector M b

/-- A selected nonsingular integral cofactor block with entries bounded by
`K` supplies a nonzero bounded integral right-kernel vector of the ambient
matrix. This is only the selected-column zero-extension step; it makes no
claim about selecting such a block or about propagating to further rows. -/
theorem exists_nonzero_bounded_integral_kernel_of_selectedCofactorBlock
    {r : ℕ} {κ : Type*} [Fintype κ]
    (A : Matrix (Fin r) κ ℤ) (M : Matrix (Fin r) (Fin r) ℤ) (b : Fin r → ℤ)
    (e : Fin r.succ ↪ κ) {K : ℤ}
    (hselected : A.submatrix id e = cofactorAugmentedMatrix M b)
    (hdet : M.det ≠ 0) (hK : 0 ≤ K)
    (hM : ∀ i j, |M i j| ≤ K) (hb : ∀ i, |b i| ≤ K) :
    ∃ z : κ → ℤ, z ≠ 0 ∧ A.mulVec z = 0 ∧
      ∀ j, |z j| ≤ (r.factorial : ℤ) * K ^ r := by
  classical
  refine ⟨selectedCofactorKernel M b e, selectedCofactorKernel_ne_zero M b e hdet,
    mulVec_selectedCofactorKernel_eq_zero A M b e hselected, ?_⟩
  exact abs_selectedCofactorKernel_le_factorial_mul_pow M b e hK hM hb

end PellPaper
