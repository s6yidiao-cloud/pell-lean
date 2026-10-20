import Pell.GeneralBidegreeAuxiliaryRelation
import Pell.RowScalingTransport
import Pell.GeneralBidegreeFullMinorHadamardHeight

/-!
# Row-scaled general bidegree auxiliary forms on a finite cell

This file packages the discrete end of the general sheared determinant
argument.  A finite cell is indexed by the membership subtype of a `Finset`;
the raw matrix is the standard integral general-bidegree evaluation matrix at
those actual integral points.  If every full-column minor of a nonzero
integral row scaling of that one matrix has strict real absolute value below
one, integrality makes the minors zero, row-scaling transport removes the
factors, and one nonzero integral standard form vanishes on the whole cell.

Nothing here identifies a source-specific transformed or denominator-cleared
matrix with this row scaling.  Nor does it prove the strict determinant bound,
transport affine coordinates, or count points on the resulting form.  The
final theorem below does add the sharp coefficient-height conclusion once a
common coordinate bound is supplied.
-/

namespace PellPaper

/-- The raw integral standard general-bidegree evaluation matrix attached to
a finite cell.  Its rows are the actual integral homogeneous points of the
cell, indexed by their membership subtype. -/
def finiteCellStandardGeneralBidegreeEvaluationMatrix (A B : ℕ)
    (cell : Finset GeneralBidegreeFormPoint) :
    Matrix {p // p ∈ cell} (generalBidegreeFormIndex A B) ℤ :=
  generalBidegreeFormEvaluationMatrix A B Subtype.val

/-- The finite-cell discrete handoff for a nonzero integral row scaling of
the standard general-bidegree evaluation matrix.  A strict real absolute
bound below one for every injectively selected full minor of the row-scaled
matrix gives one nonzero integral standard bidegree-`(A,B)` form vanishing at
every original point of the cell.

The row factors and the matrix are explicitly part of the input: this theorem
does not assert that any particular matrix from `main.tex` has this form. -/
theorem exists_nonzero_integral_generalBidegreeForm_of_finset_rowScaledFullMinors_abs_cast_lt_one
    (A B : ℕ) (cell : Finset GeneralBidegreeFormPoint)
    (d : {p // p ∈ cell} → ℤ) (hd : ∀ p, d p ≠ 0)
    (hminor : ∀ r : generalBidegreeFormIndex A B ↪ {p // p ∈ cell},
      |((((rowScale d (finiteCellStandardGeneralBidegreeEvaluationMatrix A B cell)).submatrix
        r id).det : ℝ))| < 1) :
    ∃ c : generalBidegreeFormIndex A B → ℤ, c ≠ 0 ∧
      ∀ p ∈ cell, generalBidegreeFormEval A B c p = 0 := by
  classical
  obtain ⟨c, hcne, hcvanish⟩ :=
    exists_nonzero_integral_generalBidegreeForm_of_forall_full_integralEvaluationMinors_eq_zero
      A B (fun p : {p // p ∈ cell} => p.1) (by
        intro r
        have hraw :
            ((finiteCellStandardGeneralBidegreeEvaluationMatrix A B cell).submatrix r id).det =
              0 :=
          forall_fullColumnMinors_eq_zero_of_integral_rowScale d hd
            (finiteCellStandardGeneralBidegreeEvaluationMatrix A B cell)
            (fun s => integral_det_eq_zero_of_abs_cast_lt_one _ (hminor s)) r
        simpa [finiteCellStandardGeneralBidegreeEvaluationMatrix] using hraw)
  refine ⟨c, hcne, ?_⟩
  intro p hp
  exact hcvanish ⟨p, hp⟩

/-- The quantitative finite-cell endpoint for a nonzero integral row scaling.
If every full minor of the scaled literal evaluation matrix has real absolute
value below one, then row-scaling transport makes the raw full minors vanish.
With a common coordinate bound `K`, the automatic cofactor construction gives
a nonzero integral form whose coefficients have exact real Hadamard scale
`(sqrt r * K^(A+B))^r` for some `r < (A+1)(B+1)`.

The scaled-matrix determinant estimate and the identification of a manuscript
matrix with this row scaling remain explicit external inputs. -/
theorem exists_nonzero_real_bounded_integral_generalBidegreeForm_of_finset_rowScaledFullMinors_abs_cast_lt_one_hadamard
    (A B : ℕ) (cell : Finset GeneralBidegreeFormPoint)
    (d : {p // p ∈ cell} → ℤ) (hd : ∀ p, d p ≠ 0)
    (hminor : ∀ s : generalBidegreeFormIndex A B ↪ {p // p ∈ cell},
      |((((rowScale d (finiteCellStandardGeneralBidegreeEvaluationMatrix A B cell)).submatrix
        s id).det : ℝ))| < 1)
    {K : ℤ} (hK : 0 ≤ K)
    (hpoints : ∀ p ∈ cell,
      generalBidegreeFormPointCoordinatesBounded K K p) :
    ∃ r : ℕ, r < (A + 1) * (B + 1) ∧
      ∃ c : generalBidegreeFormIndex A B → ℤ, c ≠ 0 ∧
        (∀ p ∈ cell, generalBidegreeFormEval A B c p = 0) ∧
          ∀ j, (|c j| : ℝ) ≤
            (√(r : ℝ) * ((K ^ (A + B) : ℤ) : ℝ)) ^ r := by
  have hraw : ∀ s : generalBidegreeFormIndex A B ↪ {p // p ∈ cell},
      ((finiteCellStandardGeneralBidegreeEvaluationMatrix A B cell).submatrix s id).det =
        0 := by
    intro s
    exact forall_fullColumnMinors_eq_zero_of_integral_rowScale d hd
      (finiteCellStandardGeneralBidegreeEvaluationMatrix A B cell)
      (fun t => integral_det_eq_zero_of_abs_cast_lt_one _ (hminor t)) s
  obtain ⟨r, hr, c, hcne, hcvanish, hbound⟩ :=
    exists_nonzero_real_bounded_integral_generalBidegreeForm_of_forall_fullIntegralEvaluationMinors_eq_zero_hadamard
      A B (fun p : {p // p ∈ cell} => p.1)
      (fun s => by
        simpa [finiteCellStandardGeneralBidegreeEvaluationMatrix] using hraw s)
      hK (fun p => hpoints p.1 p.2)
  refine ⟨r, hr, c, hcne, ?_, hbound⟩
  intro p hp
  exact hcvanish ⟨p, hp⟩

/-- The same row-scaled finite-cell endpoint with separate source and target
coordinate bounds.  Its coefficient scale is the literal
`(sqrt r * (S^A * T^B))^r`, rather than a bound through a common maximum.

As above, the row scaling and its strict minor bound are explicit inputs. -/
theorem exists_nonzero_real_bounded_integral_generalBidegreeForm_of_finset_rowScaledFullMinors_abs_cast_lt_one_hadamard_separateBounds
    (A B : ℕ) (cell : Finset GeneralBidegreeFormPoint)
    (d : {p // p ∈ cell} → ℤ) (hd : ∀ p, d p ≠ 0)
    (hminor : ∀ s : generalBidegreeFormIndex A B ↪ {p // p ∈ cell},
      |((((rowScale d (finiteCellStandardGeneralBidegreeEvaluationMatrix A B cell)).submatrix
        s id).det : ℝ))| < 1)
    {S T : ℤ} (hS : 0 ≤ S) (hT : 0 ≤ T)
    (hpoints : ∀ p ∈ cell,
      generalBidegreeFormPointCoordinatesBounded S T p) :
    ∃ r : ℕ, r < (A + 1) * (B + 1) ∧
      ∃ c : generalBidegreeFormIndex A B → ℤ, c ≠ 0 ∧
        (∀ p ∈ cell, generalBidegreeFormEval A B c p = 0) ∧
          ∀ j, (|c j| : ℝ) ≤
            (√(r : ℝ) * ((S ^ A * T ^ B : ℤ) : ℝ)) ^ r := by
  have hraw : ∀ s : generalBidegreeFormIndex A B ↪ {p // p ∈ cell},
      ((finiteCellStandardGeneralBidegreeEvaluationMatrix A B cell).submatrix s id).det =
        0 := by
    intro s
    exact forall_fullColumnMinors_eq_zero_of_integral_rowScale d hd
      (finiteCellStandardGeneralBidegreeEvaluationMatrix A B cell)
      (fun t => integral_det_eq_zero_of_abs_cast_lt_one _ (hminor t)) s
  obtain ⟨r, hr, c, hcne, hcvanish, hbound⟩ :=
    exists_nonzero_real_bounded_integral_generalBidegreeForm_of_forall_fullIntegralEvaluationMinors_eq_zero_hadamard_separateBounds
      A B (fun p : {p // p ∈ cell} => p.1)
      (fun s => by
        simpa [finiteCellStandardGeneralBidegreeEvaluationMatrix] using hraw s)
      hS hT (fun p => hpoints p.1 p.2)
  refine ⟨r, hr, c, hcne, ?_, hbound⟩
  intro p hp
  exact hcvanish ⟨p, hp⟩

end PellPaper
