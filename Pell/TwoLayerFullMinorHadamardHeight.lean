import Pell.GeneralBidegreeFullMinorHadamardHeight
import Pell.GeneralBidegreeOneSpecialization

/-!
# Hadamard-height two-layer forms from full minor vanishing

This is the degree-one source specialization of the full-minor bidegree
endpoint.  It is the literal finite post-determinant handoff for the
two-layer matrix used in the balanced route: every full integral minor being
zero, or having absolute value below one, gives one bounded integral form on
the whole finite sample.

The determinant estimates themselves, coordinate transport, factor control,
and point counts remain outside this module.
-/

namespace PellPaper

/-- A separate source/target-coordinate version of the two-layer full-minor
endpoint.  If source coordinates are bounded by `S ≥ 0`, target coordinates
by `T ≥ 0`, and all full integral minors vanish, the resulting form has the
sharp coefficient scale `(sqrt r * (S * T^B))^r` for some `r < 2(B+1)`.

This keeps the literal entry bound from `L:quantitative-two-layer-height`
instead of replacing both coordinate scales by one common maximum. -/
theorem exists_nonzero_real_bounded_integral_twoLayerForm_of_forall_fullIntegralEvaluationMinors_eq_zero_hadamard_separateBounds
    {ι : Type*} [Fintype ι] (B : ℕ)
    (points : ι → TwoLayerFormPoint) {S T : ℤ}
    (hminor : ∀ s : twoLayerFormIndex B ↪ ι,
      ((twoLayerFormEvaluationMatrix B points).submatrix s id).det = 0)
    (hS : 0 ≤ S) (hT : 0 ≤ T)
    (hpoints : ∀ row,
      twoLayerFormPointCoordinatesBounded S T (points row)) :
    ∃ r : ℕ, r < 2 * (B + 1) ∧
      ∃ z : twoLayerFormIndex B → ℤ, z ≠ 0 ∧
        (∀ row, twoLayerFormEval B z (points row) = 0) ∧
          ∀ j, (|z j| : ℝ) ≤
            (√(r : ℝ) * ((S * T ^ B : ℤ) : ℝ)) ^ r := by
  obtain ⟨r, hr, z, hzne, hkernel, hbound⟩ :=
    exists_nonzero_real_bounded_integral_kernel_of_forall_fullIntegralColumnMinors_eq_zero_hadamard
      (twoLayerFormEvaluationMatrix B points) hminor
      (mul_nonneg hS (pow_nonneg hT _)) (fun row j =>
        abs_twoLayerFormEvaluationMatrix_apply_le_source_mul_target_pow
          B points hS hT hpoints row j)
  refine ⟨r, ?_, z, hzne, ?_, hbound⟩
  · simpa only [card_twoLayerFormIndex] using hr
  · intro row
    rw [← twoLayerFormEvaluationMatrix_mulVec_apply]
    exact congr_fun hkernel row

/-- The determinant-method separate-bounds variant.  Strict real absolute
value below one for every full two-layer minor forces integral minor
vanishing, and then gives the same `(sqrt r * (S * T^B))^r` bound. -/
theorem exists_nonzero_real_bounded_integral_twoLayerForm_of_forall_fullIntegralEvaluationMinors_abs_cast_lt_one_hadamard_separateBounds
    {ι : Type*} [Fintype ι] (B : ℕ)
    (points : ι → TwoLayerFormPoint) {S T : ℤ}
    (hminor : ∀ s : twoLayerFormIndex B ↪ ι,
      |(((twoLayerFormEvaluationMatrix B points).submatrix s id).det : ℝ)| < 1)
    (hS : 0 ≤ S) (hT : 0 ≤ T)
    (hpoints : ∀ row,
      twoLayerFormPointCoordinatesBounded S T (points row)) :
    ∃ r : ℕ, r < 2 * (B + 1) ∧
      ∃ z : twoLayerFormIndex B → ℤ, z ≠ 0 ∧
        (∀ row, twoLayerFormEval B z (points row) = 0) ∧
          ∀ j, (|z j| : ℝ) ≤
            (√(r : ℝ) * ((S * T ^ B : ℤ) : ℝ)) ^ r := by
  obtain ⟨r, hr, z, hzne, hkernel, hbound⟩ :=
    exists_nonzero_real_bounded_integral_kernel_of_forall_fullIntegralColumnMinors_abs_cast_lt_one_hadamard
      (twoLayerFormEvaluationMatrix B points) hminor
      (mul_nonneg hS (pow_nonneg hT _)) (fun row j =>
        abs_twoLayerFormEvaluationMatrix_apply_le_source_mul_target_pow
          B points hS hT hpoints row j)
  refine ⟨r, ?_, z, hzne, ?_, hbound⟩
  · simpa only [card_twoLayerFormIndex] using hr
  · intro row
    rw [← twoLayerFormEvaluationMatrix_mulVec_apply]
    exact congr_fun hkernel row

/-- A uniform full-column-count version of the separate-bounds endpoint.
When `S,T ≥ 1`, the selected rank `r < 2(B+1)` can be absorbed into the
displayed full number of two-layer monomials.  Thus the returned form has the
single source-style coefficient bound
`(sqrt (2(B+1)) * (S*T^B))^(2(B+1))`.

This is still conditional on the strict full-minor determinant bounds. -/
theorem exists_nonzero_integral_twoLayerForm_of_forall_fullIntegralEvaluationMinors_abs_cast_lt_one_uniformHadamard_separateBounds
    {ι : Type*} [Fintype ι] (B : ℕ)
    (points : ι → TwoLayerFormPoint) {S T : ℤ}
    (hminor : ∀ s : twoLayerFormIndex B ↪ ι,
      |(((twoLayerFormEvaluationMatrix B points).submatrix s id).det : ℝ)| < 1)
    (hS : 1 ≤ S) (hT : 1 ≤ T)
    (hpoints : ∀ row,
      twoLayerFormPointCoordinatesBounded S T (points row)) :
    ∃ z : twoLayerFormIndex B → ℤ, z ≠ 0 ∧
      (∀ row, twoLayerFormEval B z (points row) = 0) ∧
        ∀ j, (|z j| : ℝ) ≤
          (√((2 * (B + 1) : ℕ) : ℝ) * ((S * T ^ B : ℤ) : ℝ)) ^
            (2 * (B + 1)) := by
  have hS0 : 0 ≤ S := zero_le_one.trans hS
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  obtain ⟨r, hr, z, hzne, hzero, hbound⟩ :=
    exists_nonzero_real_bounded_integral_twoLayerForm_of_forall_fullIntegralEvaluationMinors_abs_cast_lt_one_hadamard_separateBounds
      B points hminor hS0 hT0 hpoints
  have hrle : r ≤ 2 * (B + 1) := Nat.le_of_lt hr
  have hTpow : 1 ≤ T ^ B := one_le_pow₀ hT
  have hqInt : 1 ≤ S * T ^ B := by
    calc
      (1 : ℤ) = 1 * 1 := by ring
      _ ≤ S * T ^ B := mul_le_mul hS hTpow (by norm_num) hS0
  have hq : (1 : ℝ) ≤ ((S * T ^ B : ℤ) : ℝ) := by
    exact_mod_cast hqInt
  have hqnonneg : 0 ≤ ((S * T ^ B : ℤ) : ℝ) := hq.trans' (by norm_num)
  have hcardone : (1 : ℝ) ≤ (2 * (B + 1) : ℕ) := by
    push_cast
    have hB : 0 ≤ (B : ℝ) := Nat.cast_nonneg B
    nlinarith
  have hsqrtCardOne : 1 ≤ √((2 * (B + 1) : ℕ) : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hcardone
  have hsqrtrle : √(r : ℝ) ≤ √((2 * (B + 1) : ℕ) : ℝ) := by
    apply Real.sqrt_le_sqrt
    exact_mod_cast hrle
  have hbase :
      √(r : ℝ) * ((S * T ^ B : ℤ) : ℝ) ≤
        √((2 * (B + 1) : ℕ) : ℝ) * ((S * T ^ B : ℤ) : ℝ) :=
    mul_le_mul_of_nonneg_right hsqrtrle hqnonneg
  have hbaseOne : 1 ≤
      √((2 * (B + 1) : ℕ) : ℝ) * ((S * T ^ B : ℤ) : ℝ) := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ √((2 * (B + 1) : ℕ) : ℝ) * ((S * T ^ B : ℤ) : ℝ) :=
        mul_le_mul hsqrtCardOne hq (by norm_num) (Real.sqrt_nonneg _)
  refine ⟨z, hzne, hzero, ?_⟩
  intro j
  exact (hbound j).trans
    ((pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg _) hqnonneg) hbase r).trans
      (pow_le_pow_right₀ hbaseOne hrle))

/-- Vanishing of all full integral minors of the literal two-layer evaluation
matrix gives a nonzero integral bidegree-`(1,B)` form on every listed point.
Under a common coordinate bound `K ≥ 0`, its coefficients are bounded by
`(sqrt r * K^(B+1))^r` for some `r < 2(B+1)`.

No determinant-decay assertion is made: all minor vanishing is an explicit
premise. -/
theorem exists_nonzero_real_bounded_integral_twoLayerForm_of_forall_fullIntegralEvaluationMinors_eq_zero_hadamard
    {ι : Type*} [Fintype ι] (B : ℕ)
    (points : ι → TwoLayerFormPoint) {K : ℤ}
    (hminor : ∀ s : twoLayerFormIndex B ↪ ι,
      ((twoLayerFormEvaluationMatrix B points).submatrix s id).det = 0)
    (hK : 0 ≤ K)
    (hpoints : ∀ row,
      twoLayerFormPointCoordinatesBounded K K (points row)) :
    ∃ r : ℕ, r < 2 * (B + 1) ∧
      ∃ z : twoLayerFormIndex B → ℤ, z ≠ 0 ∧
        (∀ row, twoLayerFormEval B z (points row) = 0) ∧
          ∀ j, (|z j| : ℝ) ≤
            (√(r : ℝ) * ((K ^ (B + 1) : ℤ) : ℝ)) ^ r := by
  have hminor' : ∀ s : generalBidegreeFormIndex 1 B ↪ ι,
      ((generalBidegreeFormEvaluationMatrix 1 B points).submatrix s id).det = 0 := by
    intro s
    rw [generalBidegreeFormEvaluationMatrix_one_eq_twoLayerFormEvaluationMatrix]
    exact hminor s
  have hpoints' : ∀ row,
      generalBidegreeFormPointCoordinatesBounded K K (points row) := by
    intro row
    simpa only [generalBidegreeFormPointCoordinatesBounded,
      twoLayerFormPointCoordinatesBounded] using hpoints row
  obtain ⟨r, hr, z, hzne, hzero, hbound⟩ :=
    exists_nonzero_real_bounded_integral_generalBidegreeForm_of_forall_fullIntegralEvaluationMinors_eq_zero_hadamard
      1 B points hminor' hK hpoints'
  refine ⟨r, ?_, z, hzne, ?_, ?_⟩
  · simpa using hr
  · intro row
    simpa only [generalBidegreeFormEval_one_eq_twoLayerFormEval] using hzero row
  · intro j
    simpa [Nat.add_comm] using hbound j

/-- Strict real absolute value below one for every full integral two-layer
evaluation minor forces those minors to vanish and hence gives the same
nonzero bounded integral form.  The strict bounds themselves remain explicit
analytic hypotheses. -/
theorem exists_nonzero_real_bounded_integral_twoLayerForm_of_forall_fullIntegralEvaluationMinors_abs_cast_lt_one_hadamard
    {ι : Type*} [Fintype ι] (B : ℕ)
    (points : ι → TwoLayerFormPoint) {K : ℤ}
    (hminor : ∀ s : twoLayerFormIndex B ↪ ι,
      |(((twoLayerFormEvaluationMatrix B points).submatrix s id).det : ℝ)| < 1)
    (hK : 0 ≤ K)
    (hpoints : ∀ row,
      twoLayerFormPointCoordinatesBounded K K (points row)) :
    ∃ r : ℕ, r < 2 * (B + 1) ∧
      ∃ z : twoLayerFormIndex B → ℤ, z ≠ 0 ∧
        (∀ row, twoLayerFormEval B z (points row) = 0) ∧
          ∀ j, (|z j| : ℝ) ≤
            (√(r : ℝ) * ((K ^ (B + 1) : ℤ) : ℝ)) ^ r := by
  have hminor' : ∀ s : generalBidegreeFormIndex 1 B ↪ ι,
      |(((generalBidegreeFormEvaluationMatrix 1 B points).submatrix s id).det : ℝ)| < 1 := by
    intro s
    rw [generalBidegreeFormEvaluationMatrix_one_eq_twoLayerFormEvaluationMatrix]
    exact hminor s
  have hpoints' : ∀ row,
      generalBidegreeFormPointCoordinatesBounded K K (points row) := by
    intro row
    simpa only [generalBidegreeFormPointCoordinatesBounded,
      twoLayerFormPointCoordinatesBounded] using hpoints row
  obtain ⟨r, hr, z, hzne, hzero, hbound⟩ :=
    exists_nonzero_real_bounded_integral_generalBidegreeForm_of_forall_fullIntegralEvaluationMinors_abs_cast_lt_one_hadamard
      1 B points hminor' hK hpoints'
  refine ⟨r, ?_, z, hzne, ?_, ?_⟩
  · simpa using hr
  · intro row
    simpa only [generalBidegreeFormEval_one_eq_twoLayerFormEval] using hzero row
  · intro j
    simpa [Nat.add_comm] using hbound j

end PellPaper
