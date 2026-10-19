import Pell.IntegralAuxiliaryRelation

/-!
# Transport through nonzero row scaling

The determinant method often clears a different nonzero denominator in each
row of an evaluation matrix.  This file isolates the elementary algebraic
transport back to the unscaled matrix: row scaling by nonzero factors preserves
the right kernel, both directly over an integral domain and after rationalizing
an integral matrix.

No assertion here identifies a particular matrix from `main.tex` with a row
scaling of the two-layer evaluation matrix.  Establishing that coordinate and
denominator comparison remains a separate source-specific step.
-/

namespace PellPaper

open scoped BigOperators

/-- Scale row `i` of a matrix by the factor `d i`. -/
def rowScale {ι κ R : Type*} [Mul R] (d : ι → R)
    (A : Matrix ι κ R) : Matrix ι κ R :=
  fun i j => d i * A i j

@[simp]
theorem rowScale_apply {ι κ R : Type*} [Mul R] (d : ι → R)
    (A : Matrix ι κ R) (i : ι) (j : κ) :
    rowScale d A i j = d i * A i j := rfl

/-- Matrix mapping commutes with the pointwise row scaling used here. -/
theorem map_rowScale {ι κ R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (d : ι → R) (A : Matrix ι κ R) :
    (rowScale d A).map f = rowScale (fun i => f (d i)) (A.map f) := by
  ext i j
  simp [rowScale]

/-- Applying a row-scaled matrix to a column vector scales each resulting
coordinate by the corresponding row factor. -/
theorem rowScale_mulVec_apply {ι κ R : Type*} [Fintype κ] [Semiring R]
    (d : ι → R) (A : Matrix ι κ R) (c : κ → R) (i : ι) :
    (rowScale d A).mulVec c i = d i * (A.mulVec c i) := by
  simp [rowScale, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

/-- Over a domain, a right-kernel vector of a row-scaled matrix is already a
right-kernel vector of the original matrix when every row factor is nonzero. -/
theorem mulVec_eq_zero_of_rowScale_mulVec_eq_zero
    {ι κ R : Type*} [Fintype κ] [Semiring R] [NoZeroDivisors R]
    (d : ι → R) (hd : ∀ i, d i ≠ 0) (A : Matrix ι κ R) (c : κ → R)
    (h : (rowScale d A).mulVec c = 0) : A.mulVec c = 0 := by
  funext i
  have hi : d i * (A.mulVec c i) = 0 := by
    rw [← rowScale_mulVec_apply]
    exact congr_fun h i
  exact (mul_eq_zero.mp hi).resolve_left (hd i)

/-- The integral version of right-kernel transport through nonzero integral
row scaling. -/
theorem integral_mulVec_eq_zero_of_integral_rowScale_mulVec_eq_zero
    {ι κ : Type*} [Fintype κ] (d : ι → ℤ) (hd : ∀ i, d i ≠ 0)
    (A : Matrix ι κ ℤ) (c : κ → ℤ)
    (h : (rowScale d A).mulVec c = 0) : A.mulVec c = 0 :=
  mulVec_eq_zero_of_rowScale_mulVec_eq_zero d hd A c h

/-- The rational version of right-kernel transport after an integral matrix
has been row-scaled by nonzero integral factors. -/
theorem rational_mulVec_eq_zero_of_integral_rowScale_mulVec_eq_zero
    {ι κ : Type*} [Fintype κ] (d : ι → ℤ) (hd : ∀ i, d i ≠ 0)
    (A : Matrix ι κ ℤ) (q : κ → ℚ)
    (h : ((rowScale d A).map (algebraMap ℤ ℚ)).mulVec q = 0) :
    (A.map (algebraMap ℤ ℚ)).mulVec q = 0 := by
  refine mulVec_eq_zero_of_rowScale_mulVec_eq_zero
    (fun i => algebraMap ℤ ℚ (d i)) ?_ (A.map (algebraMap ℤ ℚ)) q ?_
  · intro i hzero
    apply hd i
    apply IsFractionRing.injective ℤ ℚ
    simpa using hzero
  · rw [← map_rowScale]
    exact h

/-- Row scaling commutes with selecting any square collection of rows.  The
selector need not be injective for this algebraic identity. -/
theorem submatrix_rowScale {ι κ ρ σ R : Type*} [Mul R]
    (d : ι → R) (A : Matrix ι κ R) (r : ρ → ι) (c : σ → κ) :
    (rowScale d A).submatrix r c =
      rowScale (fun i => d (r i)) (A.submatrix r c) := by
  rfl

/-- If all row factors are nonzero, vanishing of a selected square minor of a
row-scaled matrix forces vanishing of the corresponding minor of the original
matrix.  This is the exact minor-level transport; it does not supply the
analytic estimate which makes the scaled minors vanish. -/
theorem selectedSquareMinor_eq_zero_of_rowScale_selectedSquareMinor_eq_zero
    {ι κ R : Type*} [Fintype κ] [DecidableEq κ]
    [CommRing R] [NoZeroDivisors R] [Nontrivial R]
    (d : ι → R) (hd : ∀ i, d i ≠ 0) (A : Matrix ι κ R) (r : κ → ι)
    (h : ((rowScale d A).submatrix r id).det = 0) :
    (A.submatrix r id).det = 0 := by
  have hdet :
      (rowScale (fun i => d (r i)) (A.submatrix r id)).det =
        (∏ i, d (r i)) * (A.submatrix r id).det := by
    change (Matrix.of fun i j => d (r i) * A (r i) j).det =
      (∏ i, d (r i)) * (A.submatrix r id).det
    simpa using Matrix.det_mul_column (fun i => d (r i)) (A.submatrix r id)
  have hprod : (∏ i, d (r i)) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hd (r i))
  rw [submatrix_rowScale, hdet] at h
  exact (mul_eq_zero.mp h).resolve_left hprod

/-- Consequently, vanishing of every full-column minor of a row-scaled
integral matrix implies vanishing of every corresponding full-column minor of
the original integral matrix. -/
theorem forall_fullColumnMinors_eq_zero_of_integral_rowScale
    {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    (d : ι → ℤ) (hd : ∀ i, d i ≠ 0) (A : Matrix ι κ ℤ)
    (h : ∀ r : κ ↪ ι, ((rowScale d A).submatrix r id).det = 0) :
    ∀ r : κ ↪ ι, (A.submatrix r id).det = 0 := by
  intro r
  exact selectedSquareMinor_eq_zero_of_rowScale_selectedSquareMinor_eq_zero
    d hd A r (h r)

/-- A rational kernel of a nonzero integral row scaling of the two-layer
evaluation matrix produces the same nonzero integral auxiliary form as a
rational kernel of the unscaled evaluation matrix. -/
theorem exists_nonzero_integral_twoLayerForm_of_rational_rowScaleKernel
    {ι : Type*} (B : ℕ) (points : ι → TwoLayerFormPoint)
    (d : ι → ℤ) (hd : ∀ i, d i ≠ 0)
    (hkernel : ∃ q : twoLayerFormIndex B → ℚ, q ≠ 0 ∧
      ((rowScale d (twoLayerFormEvaluationMatrix B points)).map
        (algebraMap ℤ ℚ)).mulVec q = 0) :
    ∃ c : twoLayerFormIndex B → ℤ, c ≠ 0 ∧
      ∀ r : ι, twoLayerFormEval B c (points r) = 0 := by
  apply exists_nonzero_integral_twoLayerForm_of_rationalKernel B points
  obtain ⟨q, hqne, hqzero⟩ := hkernel
  refine ⟨q, hqne, ?_⟩
  exact rational_mulVec_eq_zero_of_integral_rowScale_mulVec_eq_zero
    d hd (twoLayerFormEvaluationMatrix B points) q hqzero

/-- An integral kernel of a nonzero integral row scaling of the two-layer
evaluation matrix gives literal vanishing of the original auxiliary form at
every listed point. -/
theorem twoLayerFormEval_eq_zero_of_integral_rowScale_kernel
    {ι : Type*} (B : ℕ) (points : ι → TwoLayerFormPoint)
    (d : ι → ℤ) (hd : ∀ i, d i ≠ 0)
    (c : twoLayerFormIndex B → ℤ)
    (h : (rowScale d (twoLayerFormEvaluationMatrix B points)).mulVec c = 0) :
    ∀ r : ι, twoLayerFormEval B c (points r) = 0 := by
  have hzero : (twoLayerFormEvaluationMatrix B points).mulVec c = 0 :=
    integral_mulVec_eq_zero_of_integral_rowScale_mulVec_eq_zero
      d hd (twoLayerFormEvaluationMatrix B points) c h
  intro r
  rw [← twoLayerFormEvaluationMatrix_mulVec_apply]
  exact congr_fun hzero r

end PellPaper
