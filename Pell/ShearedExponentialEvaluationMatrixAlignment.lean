import Pell.GeneralBidegreeTaylorLimit
import Pell.GeneralBidegreeGridEvaluationBasis
import Pell.ShearedEvaluationMatrixTransport

/-!
# Alignment of the source sheared-exponential matrix with the Taylor limit

The source-side matrix in `ShearedEvaluationMatrixTransport` has arbitrary
row type and bidegree-indexed columns.  The analytic Taylor-limit matrix is
square and indexed by the literal sheared grid.  This file transports both
indices along the supplied row equivalence and the canonical grid-point
equivalence, proving that the two literal sheared-exponential formulae agree.

No determinant nonvanishing or analytic estimate is asserted here.
-/

namespace PellPaper

/-- The first logarithmic coordinate, transported from arbitrary source rows
to the literal sheared grid. -/
noncomputable def generalBidegreeReindexedLogS {ι : Type*} (A B : ℕ)
    (eRows : ι ≃ generalBidegreeGrid A B) (S : ι → ℝ) :
    generalBidegreeGrid A B → ℝ :=
  fun r => Real.log (S (eRows.symm r))

/-- The second sheared logarithmic coordinate, transported from arbitrary
source rows to the literal sheared grid. -/
noncomputable def generalBidegreeReindexedShearedLogT {ι : Type*} (A B : ℕ)
    (eRows : ι ≃ generalBidegreeGrid A B) (S T : ι → ℝ) :
    generalBidegreeGrid A B → ℝ :=
  fun r => Real.log (T (eRows.symm r)) - 2 * Real.log (S (eRows.symm r))

/-- Reindexing the source sheared-exponential evaluation matrix by arbitrary
rows and the canonical sheared-grid columns gives precisely the literal
sheared-exponential matrix used as the Taylor limit. -/
theorem reindex_shearedExponentialEvaluationMatrix_eq_generalBidegreeSheared
    {ι : Type*} (A B : ℕ) (eRows : ι ≃ generalBidegreeGrid A B)
    (S T : ι → ℝ) :
    Matrix.reindex eRows (generalBidegreeGridPointEquiv A B)
      (shearedExponentialEvaluationMatrix A B S T) =
      generalBidegreeShearedExponentialEvaluationMatrix A B
        (generalBidegreeReindexedLogS A B eRows S)
        (generalBidegreeReindexedShearedLogT A B eRows S T) := by
  ext r p
  rcases (generalBidegreeGridPointEquiv A B).surjective p with ⟨ab, rfl⟩
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply]
  simp only [shearedExponentialEvaluationMatrix, shearedExponentialEntry,
    generalBidegreeShearedExponentialEvaluationMatrix,
    generalBidegreeReindexedLogS, generalBidegreeReindexedShearedLogT]
  change Real.exp (((ab.1.1 + 2 * ab.2.1 : ℕ) : ℝ) *
    Real.log (S (eRows.symm r)) + (ab.2.1 : ℝ) *
      (Real.log (T (eRows.symm r)) - 2 * Real.log (S (eRows.symm r)))) =
    Real.exp (((generalBidegreeGridPointEquiv A B ab).1.1 : ℝ) *
      Real.log (S (eRows.symm r)) +
      ((generalBidegreeGridPointEquiv A B ab).1.2 : ℝ) *
        (Real.log (T (eRows.symm r)) - 2 * Real.log (S (eRows.symm r))))
  rfl

/-- The corresponding reindexed square determinants agree exactly.  This is
only an equality of determinant expressions; it makes no nonvanishing claim. -/
theorem det_reindex_shearedExponentialEvaluationMatrix_eq_generalBidegreeSheared
    {ι : Type*} (A B : ℕ) (eRows : ι ≃ generalBidegreeGrid A B)
    (S T : ι → ℝ) :
    (Matrix.reindex eRows (generalBidegreeGridPointEquiv A B)
      (shearedExponentialEvaluationMatrix A B S T)).det =
      (generalBidegreeShearedExponentialEvaluationMatrix A B
        (generalBidegreeReindexedLogS A B eRows S)
        (generalBidegreeReindexedShearedLogT A B eRows S T)).det := by
  rw [reindex_shearedExponentialEvaluationMatrix_eq_generalBidegreeSheared]

end PellPaper
