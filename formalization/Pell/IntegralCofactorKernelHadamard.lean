import Pell.IntegralCofactorKernelBound
import Mathlib.Analysis.InnerProductSpace.Orientation

/-!
# Sharp Hadamard bounds for the integral cofactor kernel

This module upgrades the entrywise factorial/Leibniz estimate in
`IntegralCofactorKernelBound` to Hadamard's sharp row-norm estimate.  It uses
Mathlib's kernel-checked oriented-volume inequality over `ℝ`, then transports
the result to integral determinants and the explicit Cramer/cofactor kernel.

The final coefficient estimate is deliberately real-valued:
`(|det M| : ℝ) ≤ (sqrt r * K)^r`.  This preserves the exact square-root
factor without a rounding convention.  It is still only a bound for an
already selected square cofactor block; it does not supply the paper's
rectangular pivot selection, determinant decay, or counting estimate.
-/

namespace PellPaper

open scoped BigOperators EuclideanSpace

noncomputable def realRowVector {r : ℕ}
    (A : Matrix (Fin r) (Fin r) ℝ) (i : Fin r) :
    EuclideanSpace ℝ (Fin r) :=
  WithLp.toLp 2 (fun j => A i j)

/-- The determinant in the standard Euclidean coordinate basis is the usual
matrix determinant of the row family. -/
theorem euclideanBasis_det_realRowVector {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ) :
    (EuclideanSpace.basisFun (Fin r) ℝ).toBasis.det (realRowVector A) = A.det := by
  rw [Module.Basis.det_apply]
  have hmatrix : (EuclideanSpace.basisFun (Fin r) ℝ).toBasis.toMatrix (realRowVector A) =
      A.transpose := by
    ext i j
    change (EuclideanSpace.basisFun (Fin r) ℝ).repr (realRowVector A j) i = A j i
    simp [realRowVector]
  rw [hmatrix, Matrix.det_transpose]

theorem abs_real_det_le_prod_row_norm {r : ℕ}
    (A : Matrix (Fin r) (Fin r) ℝ) :
    |A.det| ≤ ∏ i : Fin r, ‖realRowVector A i‖ := by
  let b : OrthonormalBasis (Fin r) ℝ (EuclideanSpace ℝ (Fin r)) :=
    EuclideanSpace.basisFun (Fin r) ℝ
  let o : Orientation ℝ (EuclideanSpace ℝ (Fin r)) (Fin r) := b.toBasis.orientation
  have hdet : b.toBasis.det (realRowVector A) = A.det := by
    simpa [b] using euclideanBasis_det_realRowVector A
  calc
    |A.det| = |o.volumeForm (realRowVector A)| := by
      rw [Orientation.volumeForm_robust o b rfl, hdet]
    _ ≤ ∏ i : Fin r, ‖realRowVector A i‖ := o.abs_volumeForm_apply_le _

theorem realRowVector_norm_sq {r : ℕ}
    (A : Matrix (Fin r) (Fin r) ℝ) (i : Fin r) :
    ‖realRowVector A i‖ ^ 2 = ∑ j : Fin r, A i j ^ 2 := by
  simpa [realRowVector] using
    (EuclideanSpace.real_norm_sq_eq (realRowVector A i))

theorem realRowVector_norm_le_sqrt_card_mul {r : ℕ}
    (A : Matrix (Fin r) (Fin r) ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ i j, |A i j| ≤ K) (i : Fin r) :
    ‖realRowVector A i‖ ≤ √(r : ℝ) * K := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hK)).mp
  rw [realRowVector_norm_sq]
  calc
    (∑ j : Fin r, A i j ^ 2) ≤ ∑ _j : Fin r, K ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      apply (sq_le_sq).mpr
      simpa [abs_of_nonneg hK] using hbound i j
    _ = (r : ℝ) * K ^ 2 := by simp [nsmul_eq_mul]
    _ = (√(r : ℝ) * K) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg r)]

theorem abs_real_det_le_sqrt_card_mul_pow {r : ℕ}
    (A : Matrix (Fin r) (Fin r) ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ i j, |A i j| ≤ K) :
    |A.det| ≤ (√(r : ℝ) * K) ^ r := by
  calc
    |A.det| ≤ ∏ i : Fin r, ‖realRowVector A i‖ := abs_real_det_le_prod_row_norm A
    _ ≤ ∏ _i : Fin r, √(r : ℝ) * K := by
      apply Finset.prod_le_prod
      · intro i _
        exact norm_nonneg _
      intro i _
      exact realRowVector_norm_le_sqrt_card_mul A hK hbound i
    _ = (√(r : ℝ) * K) ^ r := by simp

/-- The sharp Hadamard bound for an integral square matrix, expressed in
`ℝ` so that the square-root factor is exact. -/
theorem abs_int_det_le_hadamard {r : ℕ}
    (M : Matrix (Fin r) (Fin r) ℤ) {K : ℤ} (hK : 0 ≤ K)
    (hbound : ∀ i j, |M i j| ≤ K) :
    (|M.det| : ℝ) ≤ (√(r : ℝ) * (K : ℝ)) ^ r := by
  let A : Matrix (Fin r) (Fin r) ℝ := M.map (Int.castRingHom ℝ)
  have hboundReal : ∀ i j, |A i j| ≤ (K : ℝ) := by
    intro i j
    change |(M i j : ℝ)| ≤ (K : ℝ)
    rw [← Int.cast_abs]
    exact_mod_cast hbound i j
  have hreal := abs_real_det_le_sqrt_card_mul_pow A
    (show (0 : ℝ) ≤ (K : ℝ) by exact_mod_cast hK) hboundReal
  have hdet : A.det = (M.det : ℝ) := by
    exact (RingHom.map_det (Int.castRingHom ℝ) M).symm
  simpa [hdet, Int.cast_abs] using hreal

/-- Replacing one column by another integral bounded column preserves the
sharp real-valued Hadamard bound. -/
theorem abs_int_det_updateCol_le_hadamard {r : ℕ}
    (M : Matrix (Fin r) (Fin r) ℤ) (b : Fin r → ℤ) {K : ℤ}
    (hK : 0 ≤ K) (hM : ∀ i j, |M i j| ≤ K) (hb : ∀ i, |b i| ≤ K)
    (j : Fin r) :
    (|(M.updateCol j b).det| : ℝ) ≤ (√(r : ℝ) * (K : ℝ)) ^ r := by
  apply abs_int_det_le_hadamard (M.updateCol j b) hK
  intro i k
  by_cases hkj : k = j
  · subst k
    simpa using hb i
  · simpa [Matrix.updateCol_ne hkj] using hM i k

/-- Every coordinate of the cofactor kernel obeys the sharp Hadamard
coefficient bound when its block and extra column are entrywise bounded. -/
theorem abs_cofactorKernelVector_le_hadamard {r : ℕ}
    (M : Matrix (Fin r) (Fin r) ℤ) (b : Fin r → ℤ) {K : ℤ}
    (hK : 0 ≤ K) (hM : ∀ i j, |M i j| ≤ K) (hb : ∀ i, |b i| ≤ K)
    (j : Fin r.succ) :
    (|cofactorKernelVector M b j| : ℝ) ≤ (√(r : ℝ) * (K : ℝ)) ^ r := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simpa only [cofactorKernelVector_last, Int.cast_abs, Int.cast_neg, abs_neg] using
      abs_int_det_le_hadamard M hK hM
  · rw [cofactorKernelVector_castSucc_eq_det_updateCol]
    exact abs_int_det_updateCol_le_hadamard M b hK hM hb i

/-- A nonsingular integral cofactor block has a nonzero integral kernel vector
whose coordinates satisfy the sharp Hadamard bound in `ℝ`. This remains a
local cofactor construction: it does not select a cofactor block from a
general rectangular matrix. -/
theorem exists_nonzero_real_bounded_integral_kernel_of_cofactorBlock_hadamard {r : ℕ}
    (M : Matrix (Fin r) (Fin r) ℤ) (b : Fin r → ℤ) {K : ℤ}
    (hdet : M.det ≠ 0) (hK : 0 ≤ K)
    (hM : ∀ i j, |M i j| ≤ K) (hb : ∀ i, |b i| ≤ K) :
    ∃ z : Fin r.succ → ℤ, z ≠ 0 ∧
      (cofactorAugmentedMatrix M b).mulVec z = 0 ∧
        ∀ j, (|z j| : ℝ) ≤ (√(r : ℝ) * (K : ℝ)) ^ r := by
  refine ⟨cofactorKernelVector M b, cofactorKernelVector_ne_zero M b hdet,
    cofactorAugmentedMatrix_mulVec_cofactorKernelVector M b, ?_⟩
  intro j
  exact abs_cofactorKernelVector_le_hadamard M b hK hM hb j

end PellPaper
