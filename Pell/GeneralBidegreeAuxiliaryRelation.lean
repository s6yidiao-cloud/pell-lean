import Pell.IntegralAuxiliaryRelation
import Pell.FullColumnMinorKernel

/-!
# Integral auxiliary forms of general bihomogeneous bidegree

This is the finite algebraic end of the rectangular determinant argument in
`L:sheared` of `main.tex`.  A standard homogeneous form of bidegree `(A, B)`
has `(A + 1) * (B + 1)` coefficients.  If every integral full-column minor
of its evaluation matrix on a finite family of integral homogeneous points
vanishes, then the family has one common nonzero integral form.

The module deliberately starts *after* the determinant estimate and
denominator-clearing construction: it proves neither a minor bound, a height
bound, a point-counting result, nor transport from rational affine
coordinates.  It concerns one globally integral standard homogeneous
evaluation matrix on `((ℤ × ℤ) × (ℤ × ℤ))` only.
-/

namespace PellPaper

open scoped BigOperators

/-- The coefficient positions of a standard bihomogeneous form of bidegree
`(A, B)`.  The two indices select the exponents of the second source and
target homogeneous coordinates, respectively. -/
abbrev generalBidegreeFormIndex (A B : ℕ) := Fin (A + 1) × Fin (B + 1)

/-- A bidegree-`(A, B)` form has exactly `(A + 1) * (B + 1)` standard
homogeneous monomials. -/
@[simp] theorem card_generalBidegreeFormIndex (A B : ℕ) :
    Fintype.card (generalBidegreeFormIndex A B) = (A + 1) * (B + 1) := by
  simp

/-- An integral pair of source and target homogeneous coordinate pairs. -/
abbrev GeneralBidegreeFormPoint := (ℤ × ℤ) × (ℤ × ℤ)

/-- The degree-`A` source monomial selected by `a`. -/
def generalBidegreeFormSource (A : ℕ) (x : ℤ × ℤ) (a : Fin (A + 1)) : ℤ :=
  x.1 ^ (A - a.1) * x.2 ^ a.1

/-- The degree-`B` target monomial selected by `b`. -/
def generalBidegreeFormTarget (B : ℕ) (y : ℤ × ℤ) (b : Fin (B + 1)) : ℤ :=
  y.1 ^ (B - b.1) * y.2 ^ b.1

/-- A standard homogeneous bidegree-`(A, B)` monomial at an integral point. -/
def generalBidegreeFormMonomial (A B : ℕ) (p : GeneralBidegreeFormPoint)
    (ab : generalBidegreeFormIndex A B) : ℤ :=
  generalBidegreeFormSource A p.1 ab.1 *
    generalBidegreeFormTarget B p.2 ab.2

/-- Evaluation of an integral standard homogeneous bidegree-`(A, B)` form. -/
def generalBidegreeFormEval (A B : ℕ)
    (c : generalBidegreeFormIndex A B → ℤ)
    (p : GeneralBidegreeFormPoint) : ℤ :=
  ∑ ab, c ab * generalBidegreeFormMonomial A B p ab

/-- The integral evaluation matrix with one row for each homogeneous point
and one column for each standard bidegree-`(A, B)` monomial. -/
def generalBidegreeFormEvaluationMatrix {ι : Type*} (A B : ℕ)
    (points : ι → GeneralBidegreeFormPoint) :
    Matrix ι (generalBidegreeFormIndex A B) ℤ :=
  fun r ab => generalBidegreeFormMonomial A B (points r) ab

/-- Matrix multiplication by the integral evaluation matrix is literal
evaluation of the coefficient form. -/
theorem generalBidegreeFormEvaluationMatrix_mulVec_apply {ι : Type*}
    (A B : ℕ) (points : ι → GeneralBidegreeFormPoint)
    (c : generalBidegreeFormIndex A B → ℤ) (r : ι) :
    (generalBidegreeFormEvaluationMatrix A B points).mulVec c r =
      generalBidegreeFormEval A B c (points r) := by
  simp [generalBidegreeFormEvaluationMatrix, generalBidegreeFormEval,
    Matrix.mulVec, dotProduct, mul_comm]

/-- A rational right-kernel of the general integral evaluation matrix clears
to a nonzero integral homogeneous bidegree-`(A, B)` form vanishing at every
listed point. -/
theorem exists_nonzero_integral_generalBidegreeForm_of_rationalKernel
    {ι : Type*} (A B : ℕ) (points : ι → GeneralBidegreeFormPoint)
    (hkernel : ∃ q : generalBidegreeFormIndex A B → ℚ, q ≠ 0 ∧
      ((generalBidegreeFormEvaluationMatrix A B points).map
        (algebraMap ℤ ℚ)).mulVec q = 0) :
    ∃ c : generalBidegreeFormIndex A B → ℤ, c ≠ 0 ∧
      ∀ r : ι, generalBidegreeFormEval A B c (points r) = 0 := by
  obtain ⟨c, hcne, hczero⟩ :=
    exists_integral_kernel_of_exists_rational_kernel
      (generalBidegreeFormEvaluationMatrix A B points) hkernel
  refine ⟨c, hcne, ?_⟩
  intro r
  rw [← generalBidegreeFormEvaluationMatrix_mulVec_apply]
  exact congr_fun hczero r

/-- Vanishing of all full rational minors of the rectangular general
evaluation matrix produces one integral homogeneous bidegree-`(A, B)` form
vanishing at every point. -/
theorem exists_nonzero_integral_generalBidegreeForm_of_forall_full_rationalEvaluationMinors_eq_zero
    {ι : Type*} [Fintype ι] (A B : ℕ)
    (points : ι → GeneralBidegreeFormPoint)
    (hminor : ∀ r : generalBidegreeFormIndex A B ↪ ι,
      ((((generalBidegreeFormEvaluationMatrix A B points).map
        (algebraMap ℤ ℚ)).submatrix r id).det = 0)) :
    ∃ c : generalBidegreeFormIndex A B → ℤ, c ≠ 0 ∧
      ∀ row : ι, generalBidegreeFormEval A B c (points row) = 0 := by
  apply exists_nonzero_integral_generalBidegreeForm_of_rationalKernel A B points
  exact exists_rational_kernel_of_forall_fullColumnMinors_eq_zero _ hminor

/-- The finite algebraic auxiliary-form endpoint for the general sheared
route: if every injectively selected full integral evaluation minor vanishes,
then all listed integral homogeneous points lie on a common nonzero integral
standard form of bidegree `(A, B)`.

This conclusion has no determinant estimate, coefficient-height bound,
curve-counting assertion, or rational-coordinate transport built into it. -/
theorem exists_nonzero_integral_generalBidegreeForm_of_forall_full_integralEvaluationMinors_eq_zero
    {ι : Type*} [Fintype ι] (A B : ℕ)
    (points : ι → GeneralBidegreeFormPoint)
    (hminor : ∀ r : generalBidegreeFormIndex A B ↪ ι,
      ((generalBidegreeFormEvaluationMatrix A B points).submatrix r id).det = 0) :
    ∃ c : generalBidegreeFormIndex A B → ℤ, c ≠ 0 ∧
      ∀ row : ι, generalBidegreeFormEval A B c (points row) = 0 := by
  apply
    exists_nonzero_integral_generalBidegreeForm_of_forall_full_rationalEvaluationMinors_eq_zero
      A B points
  intro r
  rw [Matrix.submatrix_map]
  change ((algebraMap ℤ ℚ).mapMatrix
    ((generalBidegreeFormEvaluationMatrix A B points).submatrix r id)).det = 0
  rw [← RingHom.map_det, hminor r, map_zero]

end PellPaper
