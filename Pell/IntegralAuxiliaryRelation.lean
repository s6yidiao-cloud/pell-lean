import Pell.TwoLayerGridAlgebra
import Pell.IntegralDeterminantVanishing
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Integral auxiliary forms from a rank defect

The approximate determinant argument in `main.tex` has a discrete handoff:
once an evaluation determinant is an integer of absolute value less than one,
it is zero; a zero determinant gives a nonzero *integral* auxiliary form.

This file formalizes the second half of that handoff for bihomogeneous forms
of bidegree `(1,B)`.  It deliberately does not assert the analytic determinant
estimate, a height bound for the resulting form, or a point-counting estimate.
Those remain the active determinant-method frontier for
`FixedHeightSquarefree`.
-/

namespace PellPaper

open scoped BigOperators

/-- The `2(B+1)` monomials of a bihomogeneous form of bidegree `(1,B)`:
one source coordinate and a degree-`B` target monomial. -/
abbrev twoLayerFormIndex (B : ℕ) := Fin 2 × Fin (B + 1)

/-- A bidegree-`(1,B)` form has exactly the `2(B+1)` columns used by the
two-layer determinant. -/
@[simp] theorem card_twoLayerFormIndex (B : ℕ) :
    Fintype.card (twoLayerFormIndex B) = 2 * (B + 1) := by
  simp [Nat.mul_add]

/-- An integral source-target point for a bihomogeneous auxiliary form. -/
abbrev TwoLayerFormPoint := (ℤ × ℤ) × (ℤ × ℤ)

/-- The source coordinate selected by the first degree-one index. -/
def twoLayerFormSource (x : ℤ × ℤ) (a : Fin 2) : ℤ :=
  if a = 0 then x.1 else x.2

/-- The degree-`B` target monomial selected by the second index. -/
def twoLayerFormTarget (B : ℕ) (y : ℤ × ℤ) (b : Fin (B + 1)) : ℤ :=
  y.1 ^ (B - b.1) * y.2 ^ b.1

/-- A single bidegree-`(1,B)` monomial evaluated at an integral point. -/
def twoLayerFormMonomial (B : ℕ) (p : TwoLayerFormPoint)
    (ab : twoLayerFormIndex B) : ℤ :=
  twoLayerFormSource p.1 ab.1 * twoLayerFormTarget B p.2 ab.2

/-- Evaluation of an integral bidegree-`(1,B)` auxiliary form. -/
def twoLayerFormEval (B : ℕ) (c : twoLayerFormIndex B → ℤ)
    (p : TwoLayerFormPoint) : ℤ :=
  ∑ ab, c ab * twoLayerFormMonomial B p ab

/-- The evaluation matrix whose columns are the bidegree-`(1,B)` monomials. -/
def twoLayerFormEvaluationMatrix {ι : Type*} (B : ℕ)
    (points : ι → TwoLayerFormPoint) : Matrix ι (twoLayerFormIndex B) ℤ :=
  fun r ab => twoLayerFormMonomial B (points r) ab

/-- Multiplication by the evaluation matrix is literal form evaluation. -/
theorem twoLayerFormEvaluationMatrix_mulVec_apply {ι : Type*} (B : ℕ)
    (points : ι → TwoLayerFormPoint) (c : twoLayerFormIndex B → ℤ) (r : ι) :
    (twoLayerFormEvaluationMatrix B points).mulVec c r =
      twoLayerFormEval B c (points r) := by
  simp [twoLayerFormEvaluationMatrix, twoLayerFormEval, Matrix.mulVec,
    dotProduct, mul_comm]

/-- Clear denominators in a rational kernel vector of an integer matrix.

This is the algebraic step which ensures that determinant vanishing produces
an *integral* auxiliary form rather than merely a rational one.  It is stated
for arbitrary row types because later determinant arguments may include more
rows than columns. -/
theorem exists_integral_kernel_of_exists_rational_kernel
    {ι κ : Type*} [Fintype κ] (A : Matrix ι κ ℤ)
    (hkernel : ∃ q : κ → ℚ, q ≠ 0 ∧
      (A.map (algebraMap ℤ ℚ)).mulVec q = 0) :
    ∃ z : κ → ℤ, z ≠ 0 ∧ A.mulVec z = 0 := by
  classical
  rcases hkernel with ⟨q, hq, hqzero⟩
  obtain ⟨⟨b, hb⟩, hmultiple⟩ :=
    IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors ℤ)
      (Finset.univ.image q)
  choose z hz using hmultiple
  refine
    ⟨fun j => z _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩),
      mt (fun h => funext fun j => ?_) hq, ?_⟩
  · have hcast := congr_arg (algebraMap ℤ ℚ) (congr_fun h j)
    rw [hz, Subtype.coe_mk, Pi.zero_apply, map_zero, Algebra.smul_def,
      mul_eq_zero, IsFractionRing.to_map_eq_zero_iff] at hcast
    exact hcast.resolve_left (nonZeroDivisors.ne_zero hb)
  · funext r
    refine IsFractionRing.injective ℤ ℚ ?_
    calc
      algebraMap ℤ ℚ
          (A.mulVec (fun j => z _
            (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)) r) =
          ((A.map (algebraMap ℤ ℚ)).mulVec
            (algebraMap ℤ ℚ b • q)) r := by
            simp_rw [RingHom.map_mulVec, Matrix.mulVec, dotProduct,
              Function.comp_apply, hz,
              Pi.smul_apply, smul_eq_mul, Algebra.smul_def]
      _ = 0 := by
        have hqzero_r : (A.map (algebraMap ℤ ℚ)).mulVec q r = 0 :=
          congr_fun hqzero r
        rw [Matrix.mulVec_smul, Pi.smul_apply, hqzero_r, smul_zero]
      _ = algebraMap ℤ ℚ 0 := (map_zero _).symm

/-- A rational rank defect in the bidegree-`(1,B)` evaluation matrix gives
a nonzero integral auxiliary form vanishing at every listed point. -/
theorem exists_nonzero_integral_twoLayerForm_of_rationalKernel
    {ι : Type*} (B : ℕ) (points : ι → TwoLayerFormPoint)
    (hkernel : ∃ q : twoLayerFormIndex B → ℚ, q ≠ 0 ∧
      ((twoLayerFormEvaluationMatrix B points).map
        (algebraMap ℤ ℚ)).mulVec q = 0) :
    ∃ c : twoLayerFormIndex B → ℤ, c ≠ 0 ∧
      ∀ r : ι, twoLayerFormEval B c (points r) = 0 := by
  obtain ⟨c, hcne, hczero⟩ :=
    exists_integral_kernel_of_exists_rational_kernel
      (twoLayerFormEvaluationMatrix B points) hkernel
  refine ⟨c, hcne, ?_⟩
  intro r
  rw [← twoLayerFormEvaluationMatrix_mulVec_apply]
  exact congr_fun hczero r

/-- For a square sample of exactly `2(B+1)` points, a zero integral
evaluation determinant gives a nonzero integral bidegree-`(1,B)` form
vanishing on that sample.  This is the exact post-determinant bridge used in
the balanced-cell argument. -/
theorem exists_nonzero_integral_twoLayerForm_of_det_eq_zero
    (B : ℕ) (points : twoLayerFormIndex B → TwoLayerFormPoint)
    (hdet : (twoLayerFormEvaluationMatrix B points).det = 0) :
    ∃ c : twoLayerFormIndex B → ℤ, c ≠ 0 ∧
      ∀ r : twoLayerFormIndex B, twoLayerFormEval B c (points r) = 0 := by
  obtain ⟨c, hcne, hczero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  refine ⟨c, hcne, ?_⟩
  intro r
  rw [← twoLayerFormEvaluationMatrix_mulVec_apply]
  exact congr_fun hczero r

/-- The direct cleared-determinant handoff for one square sample: if the
integral evaluation determinant has strict real absolute value below one,
then it produces a nonzero integral auxiliary form vanishing on that sample.
For a cell with more rows than columns, a separate all-minors/rank-defect
argument is still required before applying the rational-kernel theorem above. -/
theorem exists_nonzero_integral_twoLayerForm_of_abs_cast_det_lt_one
    (B : ℕ) (points : twoLayerFormIndex B → TwoLayerFormPoint)
    (hdet : |((twoLayerFormEvaluationMatrix B points).det : ℝ)| < 1) :
    ∃ c : twoLayerFormIndex B → ℤ, c ≠ 0 ∧
      ∀ r : twoLayerFormIndex B, twoLayerFormEval B c (points r) = 0 :=
  exists_nonzero_integral_twoLayerForm_of_det_eq_zero B points
    (integral_det_eq_zero_of_abs_cast_lt_one
      (twoLayerFormEvaluationMatrix B points) hdet)

end PellPaper
