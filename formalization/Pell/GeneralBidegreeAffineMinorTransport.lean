import Pell.GeneralBidegreeAffineTransport

/-!
# Determinant transport through bidegree affine denominator clearing

The affine/homogeneous transport identifies a denominator-cleared bidegree
evaluation matrix with a row-scaled rational affine matrix.  This file records
the corresponding exact determinant factor for every selected full minor.
It isolates the row-denominator contribution in the determinant bookkeeping
of `L:sheared`; it contains no analytic determinant estimate.
-/

namespace PellPaper

open scoped BigOperators

/-- Scaling each row of a square matrix multiplies its determinant by the
product of the row factors. -/
theorem det_rowScale (R : Type*) {κ : Type*} [CommRing R]
    [Fintype κ] [DecidableEq κ] (d : κ → R) (M : Matrix κ κ R) :
    (rowScale d M).det = (∏ i, d i) * M.det := by
  calc
    (rowScale d M).det = ((rowScale d M).transpose).det := by
      rw [Matrix.det_transpose]
    _ = (Matrix.of fun i j => d j * M.transpose i j).det := by
      rfl
    _ = (∏ i, d i) * M.transpose.det := Matrix.det_mul_row d M.transpose
    _ = (∏ i, d i) * M.det := by rw [Matrix.det_transpose]

/-- Every selected full minor of the rationalized homogeneous bidegree
matrix is the corresponding affine minor times the product of its explicit
row homogenizing factors. -/
theorem det_rationalizedHomogeneous_submatrix_eq_rowFactor_mul_affine
    {ι : Type*} (A B : ℕ) (points : ι → GeneralBidegreeFormPoint)
    (hden : ∀ r, (points r).1.2 ≠ 0 ∧ (points r).2.2 ≠ 0)
    (r : generalBidegreeFormIndex A B ↪ ι) :
    (((generalBidegreeFormEvaluationMatrix A B points).map
      (algebraMap ℤ ℚ)).submatrix r id).det =
      (∏ i : generalBidegreeFormIndex A B,
        generalBidegreeFormHomogenizingFactor A B (points (r i))) *
        ((generalBidegreeFormAffineEvaluationMatrix A B points).submatrix r id).det := by
  rw [← rowScale_generalBidegreeFormAffineEvaluationMatrix_eq_rationalizedHomogeneous
    A B points hden]
  rw [submatrix_rowScale]
  exact det_rowScale ℚ
    (fun i : generalBidegreeFormIndex A B =>
      generalBidegreeFormHomogenizingFactor A B (points (r i)))
    ((generalBidegreeFormAffineEvaluationMatrix A B points).submatrix r id)

end PellPaper
