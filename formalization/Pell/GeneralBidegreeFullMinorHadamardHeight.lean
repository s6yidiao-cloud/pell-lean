import Pell.TwoLayerEvaluationEntryBounds
import Pell.IntegralFullMinorHadamardKernel

/-!
# Hadamard-height bidegree forms from full minor vanishing

This module is the finite endpoint after an approximate determinant estimate
for the literal integral general-bidegree evaluation matrix.  Once all of its
full integral minors vanish--or, equivalently here, have strict real absolute
value below one--a nonzero integral form vanishing on every listed point is
constructed automatically with the sharp Hadamard coefficient scale.

It does not prove a determinant bound, identify a transformed evaluation
matrix with this literal one, control factors of the form, or count points.
-/

namespace PellPaper

/-- The separate source/target-coordinate version of the full-minor
general-bidegree endpoint.  If source coordinates are bounded by `S ≥ 0`,
target coordinates by `T ≥ 0`, and all full integral minors vanish, the
resulting form has coefficient scale `(sqrt r * (S^A * T^B))^r` for some
`r < (A+1)(B+1)`.

This retains the literal entry height instead of replacing the two scales by
a common maximum. -/
theorem exists_nonzero_real_bounded_integral_generalBidegreeForm_of_forall_fullIntegralEvaluationMinors_eq_zero_hadamard_separateBounds
    {ι : Type*} [Fintype ι] (A B : ℕ)
    (points : ι → GeneralBidegreeFormPoint) {S T : ℤ}
    (hminor : ∀ s : generalBidegreeFormIndex A B ↪ ι,
      ((generalBidegreeFormEvaluationMatrix A B points).submatrix s id).det = 0)
    (hS : 0 ≤ S) (hT : 0 ≤ T)
    (hpoints : ∀ row,
      generalBidegreeFormPointCoordinatesBounded S T (points row)) :
    ∃ r : ℕ, r < (A + 1) * (B + 1) ∧
      ∃ z : generalBidegreeFormIndex A B → ℤ, z ≠ 0 ∧
        (∀ row, generalBidegreeFormEval A B z (points row) = 0) ∧
          ∀ j, (|z j| : ℝ) ≤
            (√(r : ℝ) * ((S ^ A * T ^ B : ℤ) : ℝ)) ^ r := by
  obtain ⟨r, hr, z, hzne, hkernel, hbound⟩ :=
    exists_nonzero_real_bounded_integral_kernel_of_forall_fullIntegralColumnMinors_eq_zero_hadamard
      (generalBidegreeFormEvaluationMatrix A B points) hminor
      (mul_nonneg (pow_nonneg hS _) (pow_nonneg hT _)) (fun row j =>
        abs_generalBidegreeFormEvaluationMatrix_apply_le_source_pow_mul_target_pow
          A B points hS hT hpoints row j)
  refine ⟨r, ?_, z, hzne, ?_, hbound⟩
  · simpa only [card_generalBidegreeFormIndex] using hr
  · intro row
    rw [← generalBidegreeFormEvaluationMatrix_mulVec_apply]
    exact congr_fun hkernel row

/-- The determinant-method separate-bounds version: strict real absolute
value below one for every full integral evaluation minor gives the same
bounded form at scale `(sqrt r * (S^A * T^B))^r`.  The strict minor estimate
remains an explicit analytic input. -/
theorem exists_nonzero_real_bounded_integral_generalBidegreeForm_of_forall_fullIntegralEvaluationMinors_abs_cast_lt_one_hadamard_separateBounds
    {ι : Type*} [Fintype ι] (A B : ℕ)
    (points : ι → GeneralBidegreeFormPoint) {S T : ℤ}
    (hminor : ∀ s : generalBidegreeFormIndex A B ↪ ι,
      |(((generalBidegreeFormEvaluationMatrix A B points).submatrix s id).det : ℝ)| < 1)
    (hS : 0 ≤ S) (hT : 0 ≤ T)
    (hpoints : ∀ row,
      generalBidegreeFormPointCoordinatesBounded S T (points row)) :
    ∃ r : ℕ, r < (A + 1) * (B + 1) ∧
      ∃ z : generalBidegreeFormIndex A B → ℤ, z ≠ 0 ∧
        (∀ row, generalBidegreeFormEval A B z (points row) = 0) ∧
          ∀ j, (|z j| : ℝ) ≤
            (√(r : ℝ) * ((S ^ A * T ^ B : ℤ) : ℝ)) ^ r := by
  obtain ⟨r, hr, z, hzne, hkernel, hbound⟩ :=
    exists_nonzero_real_bounded_integral_kernel_of_forall_fullIntegralColumnMinors_abs_cast_lt_one_hadamard
      (generalBidegreeFormEvaluationMatrix A B points) hminor
      (mul_nonneg (pow_nonneg hS _) (pow_nonneg hT _)) (fun row j =>
        abs_generalBidegreeFormEvaluationMatrix_apply_le_source_pow_mul_target_pow
          A B points hS hT hpoints row j)
  refine ⟨r, ?_, z, hzne, ?_, hbound⟩
  · simpa only [card_generalBidegreeFormIndex] using hr
  · intro row
    rw [← generalBidegreeFormEvaluationMatrix_mulVec_apply]
    exact congr_fun hkernel row

/-- If every full integral minor of the literal general-bidegree evaluation
matrix vanishes, then bounded homogeneous coordinates give a nonzero integral
form vanishing on every displayed point.  Its coefficients obey the exact
real Hadamard scale `(sqrt r * K^(A+B))^r` for some
`r < (A+1)(B+1)`.

The all-minors hypothesis is explicit; no analytic determinant estimate is
asserted. -/
theorem exists_nonzero_real_bounded_integral_generalBidegreeForm_of_forall_fullIntegralEvaluationMinors_eq_zero_hadamard
    {ι : Type*} [Fintype ι] (A B : ℕ)
    (points : ι → GeneralBidegreeFormPoint) {K : ℤ}
    (hminor : ∀ s : generalBidegreeFormIndex A B ↪ ι,
      ((generalBidegreeFormEvaluationMatrix A B points).submatrix s id).det = 0)
    (hK : 0 ≤ K)
    (hpoints : ∀ row,
      generalBidegreeFormPointCoordinatesBounded K K (points row)) :
    ∃ r : ℕ, r < (A + 1) * (B + 1) ∧
      ∃ z : generalBidegreeFormIndex A B → ℤ, z ≠ 0 ∧
        (∀ row, generalBidegreeFormEval A B z (points row) = 0) ∧
          ∀ j, (|z j| : ℝ) ≤
            (√(r : ℝ) * ((K ^ (A + B) : ℤ) : ℝ)) ^ r := by
  obtain ⟨r, hr, z, hzne, hkernel, hbound⟩ :=
    exists_nonzero_real_bounded_integral_kernel_of_forall_fullIntegralColumnMinors_eq_zero_hadamard
      (generalBidegreeFormEvaluationMatrix A B points) hminor
      (pow_nonneg hK _) (fun row j =>
        abs_generalBidegreeFormEvaluationMatrix_apply_le_pow_add
          A B points hK hpoints row j)
  refine ⟨r, ?_, z, hzne, ?_, hbound⟩
  · simpa only [card_generalBidegreeFormIndex] using hr
  · intro row
    rw [← generalBidegreeFormEvaluationMatrix_mulVec_apply]
    exact congr_fun hkernel row

/-- The determinant-method form of the preceding endpoint.  Strict real
absolute value below one for every full integral evaluation minor forces all
such minors to vanish, yielding the same nonzero bounded integral form.

The strict minor estimate remains a hypothesis; this theorem does not supply
the Cauchy--Binet/Taylor decay from `L:sheared`. -/
theorem exists_nonzero_real_bounded_integral_generalBidegreeForm_of_forall_fullIntegralEvaluationMinors_abs_cast_lt_one_hadamard
    {ι : Type*} [Fintype ι] (A B : ℕ)
    (points : ι → GeneralBidegreeFormPoint) {K : ℤ}
    (hminor : ∀ s : generalBidegreeFormIndex A B ↪ ι,
      |(((generalBidegreeFormEvaluationMatrix A B points).submatrix s id).det : ℝ)| < 1)
    (hK : 0 ≤ K)
    (hpoints : ∀ row,
      generalBidegreeFormPointCoordinatesBounded K K (points row)) :
    ∃ r : ℕ, r < (A + 1) * (B + 1) ∧
      ∃ z : generalBidegreeFormIndex A B → ℤ, z ≠ 0 ∧
        (∀ row, generalBidegreeFormEval A B z (points row) = 0) ∧
          ∀ j, (|z j| : ℝ) ≤
            (√(r : ℝ) * ((K ^ (A + B) : ℤ) : ℝ)) ^ r := by
  obtain ⟨r, hr, z, hzne, hkernel, hbound⟩ :=
    exists_nonzero_real_bounded_integral_kernel_of_forall_fullIntegralColumnMinors_abs_cast_lt_one_hadamard
      (generalBidegreeFormEvaluationMatrix A B points) hminor
      (pow_nonneg hK _) (fun row j =>
        abs_generalBidegreeFormEvaluationMatrix_apply_le_pow_add
          A B points hK hpoints row j)
  refine ⟨r, ?_, z, hzne, ?_, hbound⟩
  · simpa only [card_generalBidegreeFormIndex] using hr
  · intro row
    rw [← generalBidegreeFormEvaluationMatrix_mulVec_apply]
    exact congr_fun hkernel row

end PellPaper
