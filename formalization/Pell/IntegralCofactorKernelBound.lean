import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# A bounded integral kernel from one cofactor block

This module formalizes the finite algebraic step behind the cofactor argument:
an invertible `r × r` integral block together with one extra column gives a
nonzero integral kernel vector for the resulting `r × (r + 1)` matrix.
The coefficient estimate is the entrywise factorial (Leibniz) determinant
bound supplied by Mathlib, not the sharper Hadamard estimate in the paper.
It intentionally does not select pivot rows or columns from a general
rectangular rank-deficient matrix.
-/

namespace PellPaper

open scoped BigOperators

/-- Append the column `b` after the square block `M`. -/
def cofactorAugmentedMatrix {r : ℕ}
    (M : Matrix (Fin r) (Fin r) ℤ) (b : Fin r → ℤ) :
    Matrix (Fin r) (Fin r.succ) ℤ :=
  fun i j => Fin.lastCases (b i) (fun k => M i k) j

/-- The Cramer/cofactor vector for the augmented matrix: its first `r`
coordinates are the Cramer determinants, and its final coordinate is minus
the determinant of the square block. -/
def cofactorKernelVector {r : ℕ}
    (M : Matrix (Fin r) (Fin r) ℤ) (b : Fin r → ℤ) : Fin r.succ → ℤ :=
  Fin.lastCases (-M.det) (M.cramer b)

@[simp]
theorem cofactorAugmentedMatrix_castSucc {r : ℕ}
    (M : Matrix (Fin r) (Fin r) ℤ) (b : Fin r → ℤ) (i j : Fin r) :
    cofactorAugmentedMatrix M b i j.castSucc = M i j := by
  simp [cofactorAugmentedMatrix]

@[simp]
theorem cofactorAugmentedMatrix_last {r : ℕ}
    (M : Matrix (Fin r) (Fin r) ℤ) (b : Fin r → ℤ) (i : Fin r) :
    cofactorAugmentedMatrix M b i (Fin.last r) = b i := by
  simp [cofactorAugmentedMatrix]

@[simp]
theorem cofactorKernelVector_castSucc {r : ℕ}
    (M : Matrix (Fin r) (Fin r) ℤ) (b : Fin r → ℤ) (i : Fin r) :
    cofactorKernelVector M b i.castSucc = M.cramer b i := by
  simp [cofactorKernelVector]

@[simp]
theorem cofactorKernelVector_last {r : ℕ}
    (M : Matrix (Fin r) (Fin r) ℤ) (b : Fin r → ℤ) :
    cofactorKernelVector M b (Fin.last r) = -M.det := by
  simp [cofactorKernelVector]

/-- Each non-final coordinate is exactly the determinant obtained by replacing
the corresponding column of `M` by `b`. -/
theorem cofactorKernelVector_castSucc_eq_det_updateCol {r : ℕ}
    (M : Matrix (Fin r) (Fin r) ℤ) (b : Fin r → ℤ) (i : Fin r) :
    cofactorKernelVector M b i.castSucc = (M.updateCol i b).det := by
  rw [cofactorKernelVector_castSucc, Matrix.cramer_apply]

/-- Cramer's-rule vector is an integral right-kernel vector of the augmented
block. -/
theorem cofactorAugmentedMatrix_mulVec_cofactorKernelVector {r : ℕ}
    (M : Matrix (Fin r) (Fin r) ℤ) (b : Fin r → ℤ) :
    (cofactorAugmentedMatrix M b).mulVec (cofactorKernelVector M b) = 0 := by
  funext i
  change (∑ j : Fin r.succ,
    cofactorAugmentedMatrix M b i j * cofactorKernelVector M b j) = 0
  rw [Fin.sum_univ_castSucc]
  simp only [cofactorAugmentedMatrix, cofactorKernelVector,
    Fin.lastCases_castSucc, Fin.lastCases_last]
  calc
    (∑ j : Fin r, M i j * M.cramer b j) + b i * (-M.det) =
        (M.mulVec (M.cramer b)) i - M.det * b i := by
      simp [Matrix.mulVec, dotProduct]
      ring
    _ = 0 := by
      rw [Matrix.mulVec_cramer]
      simp

/-- The Cramer/cofactor vector is nonzero when its square block has nonzero
determinant. -/
theorem cofactorKernelVector_ne_zero {r : ℕ}
    (M : Matrix (Fin r) (Fin r) ℤ) (b : Fin r → ℤ) (hdet : M.det ≠ 0) :
    cofactorKernelVector M b ≠ 0 := by
  intro hzero
  have hlast : -M.det = 0 := by
    simpa using congr_fun hzero (Fin.last r)
  exact hdet (neg_eq_zero.mp hlast)

/-- The factorial/Leibniz determinant bound from an entrywise integral
absolute-value bound.  This is deliberately weaker than Hadamard's
`r^(r/2)` bound. -/
theorem abs_det_le_factorial_mul_pow {r : ℕ}
    (M : Matrix (Fin r) (Fin r) ℤ) {K : ℤ}
    (_hK : 0 ≤ K) (hbound : ∀ i j, |M i j| ≤ K) :
    |M.det| ≤ (r.factorial : ℤ) * K ^ r := by
  have h := Matrix.det_le (A := M) (abv := (AbsoluteValue.abs : AbsoluteValue ℤ ℤ)) hbound
  simpa [nsmul_eq_mul] using h

/-- Replacing a column by another bounded column preserves the same
factorial/Leibniz determinant bound. -/
theorem abs_det_updateCol_le_factorial_mul_pow {r : ℕ}
    (M : Matrix (Fin r) (Fin r) ℤ) (b : Fin r → ℤ) {K : ℤ}
    (hK : 0 ≤ K) (hM : ∀ i j, |M i j| ≤ K) (hb : ∀ i, |b i| ≤ K)
    (j : Fin r) :
    |(M.updateCol j b).det| ≤ (r.factorial : ℤ) * K ^ r := by
  apply abs_det_le_factorial_mul_pow (M.updateCol j b) hK
  intro i k
  by_cases hkj : k = j
  · subst k
    simpa using hb i
  · simpa [Matrix.updateCol_ne hkj] using hM i k

/-- Every coordinate of the explicit cofactor vector has the factorial
(Leibniz) bound when the square block and extra column have entries bounded
by `K`. -/
theorem abs_cofactorKernelVector_le_factorial_mul_pow {r : ℕ}
    (M : Matrix (Fin r) (Fin r) ℤ) (b : Fin r → ℤ) {K : ℤ}
    (hK : 0 ≤ K) (hM : ∀ i j, |M i j| ≤ K) (hb : ∀ i, |b i| ≤ K)
    (j : Fin r.succ) :
    |cofactorKernelVector M b j| ≤ (r.factorial : ℤ) * K ^ r := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simpa only [cofactorKernelVector_last, abs_neg] using
      abs_det_le_factorial_mul_pow M hK hM
  · rw [cofactorKernelVector_castSucc_eq_det_updateCol]
    exact abs_det_updateCol_le_factorial_mul_pow M b hK hM hb i

/-- A nonsingular integral cofactor block with bounded entries supplies a
nonzero bounded integral right-kernel vector for its one-column augmentation.
This is a local cofactor construction only; no rectangular pivot-selection or
sharp Hadamard estimate is asserted here. -/
theorem exists_nonzero_bounded_integral_kernel_of_cofactorBlock {r : ℕ}
    (M : Matrix (Fin r) (Fin r) ℤ) (b : Fin r → ℤ) {K : ℤ}
    (hdet : M.det ≠ 0) (hK : 0 ≤ K)
    (hM : ∀ i j, |M i j| ≤ K) (hb : ∀ i, |b i| ≤ K) :
    ∃ z : Fin r.succ → ℤ, z ≠ 0 ∧
      (cofactorAugmentedMatrix M b).mulVec z = 0 ∧
        ∀ j, |z j| ≤ (r.factorial : ℤ) * K ^ r := by
  refine ⟨cofactorKernelVector M b, cofactorKernelVector_ne_zero M b hdet,
    cofactorAugmentedMatrix_mulVec_cofactorKernelVector M b, ?_⟩
  intro j
  exact abs_cofactorKernelVector_le_factorial_mul_pow M b hK hM hb j

end PellPaper
