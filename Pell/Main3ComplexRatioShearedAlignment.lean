import Pell.Main3EmbeddingBasisRatioFactorization
import Pell.ComplexUnitCircleLocalLogAdapter
import Mathlib.Tactic

/-!
# Complex sheared-exponential alignment for the main3 ratio matrix

After the radial factor has been removed from the reflected embedding
matrix, a row consists of the normalized powers `z^i w^j`.  If a fixed unit
centre `c` and local logarithms satisfy

`z = c * exp alpha`, `w = c^2 * exp (2 alpha + delta)`,

then this row is a unit column factor times the literal sheared exponential

`exp ((i + 2j) alpha + j delta)`.

This module proves that exact entrywise identity, its matrix form, and the
resulting determinant-norm equality for every selected full minor.  It also
specializes the identity to the branch-safe local logarithms supplied by one
complex unit-circle cell.  No Taylor estimate, fan-weight calculation,
radial bound, or integral-minor vanishing is asserted.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- The unit-centre factor extracted from the `(i,j)`-th ratio-power
column. -/
def main3ComplexShearedCenterColumnScale
    (centre : ℂ) (ij : generalBidegreeFormIndex 1 B) : ℂ :=
  centre ^ (ij.1.1 + 2 * ij.2.1)

/-- The complex sheared exponential left after extracting the centre from a
normalized ratio-power column. -/
def main3ComplexShearedExponentialEntry
    (alpha delta : ℂ) (ij : generalBidegreeFormIndex 1 B) : ℂ :=
  Complex.exp
    (((ij.1.1 + 2 * ij.2.1 : ℕ) : ℂ) * alpha +
      (ij.2.1 : ℂ) * delta)

/-- The row-family version of the complex sheared exponential matrix. -/
def main3ComplexShearedExponentialEvaluationMatrix
    {ι : Type*} (B : ℕ) (alpha delta : ι → ℂ) :
    Matrix ι (generalBidegreeFormIndex 1 B) ℂ :=
  fun r ij => main3ComplexShearedExponentialEntry (alpha r) (delta r) ij

/-- Exact extraction of a common centre from one normalized ratio-power
entry.  Only exponential identities are used; no equality between chosen
logarithm branches is needed. -/
theorem main3RatioPowerMonomial_eq_centerScale_mul_shearedExponential
    (B : ℕ) {z w centre alpha delta : ℂ}
    (hsource : centre * Complex.exp alpha = z)
    (htarget : centre ^ 2 * Complex.exp (2 * alpha + delta) = w)
    (ij : generalBidegreeFormIndex 1 B) :
    main3RatioPowerMonomial B z w ij =
      main3ComplexShearedCenterColumnScale centre ij *
        main3ComplexShearedExponentialEntry alpha delta ij := by
  rw [← hsource, ← htarget]
  simp only [main3RatioPowerMonomial,
    main3ComplexShearedCenterColumnScale,
    main3ComplexShearedExponentialEntry]
  rw [mul_pow, mul_pow, ← pow_mul,
    ← Complex.exp_nat_mul alpha ij.1.1,
    ← Complex.exp_nat_mul (2 * alpha + delta) ij.2.1]
  calc
    centre ^ ij.1.1 * Complex.exp ((ij.1.1 : ℂ) * alpha) *
        (centre ^ (2 * ij.2.1) *
          Complex.exp ((ij.2.1 : ℂ) * (2 * alpha + delta))) =
      (centre ^ ij.1.1 * centre ^ (2 * ij.2.1)) *
        (Complex.exp ((ij.1.1 : ℂ) * alpha) *
          Complex.exp ((ij.2.1 : ℂ) * (2 * alpha + delta))) := by ring
    _ = centre ^ (ij.1.1 + 2 * ij.2.1) *
        Complex.exp
          ((ij.1.1 : ℂ) * alpha +
            (ij.2.1 : ℂ) * (2 * alpha + delta)) := by
      rw [← pow_add, ← Complex.exp_add]
    _ = centre ^ (ij.1.1 + 2 * ij.2.1) *
        Complex.exp
          (((ij.1.1 + 2 * ij.2.1 : ℕ) : ℂ) * alpha +
            (ij.2.1 : ℂ) * delta) := by
      congr 2
      push_cast
      ring

/-- Pointwise exact local parametrizations turn the entire normalized ratio
matrix into a column-scaled complex sheared-exponential matrix. -/
theorem main3RatioPowerEvaluationMatrix_eq_columnScale_complexSheared
    {ι : Type*} (B : ℕ) (omega omegaBar centre : ℂ)
    (points : ι → GeneralBidegreeFormPoint)
    (alpha delta : ι → ℂ)
    (hsource : ∀ r,
      centre * Complex.exp (alpha r) =
        main3EmbeddingSourceRatio omega omegaBar (points r))
    (htarget : ∀ r,
      centre ^ 2 * Complex.exp (2 * alpha r + delta r) =
        main3EmbeddingTargetRatio omega omegaBar (points r)) :
    main3RatioPowerEvaluationMatrix B omega omegaBar points =
      columnScale
        (main3ComplexShearedCenterColumnScale (B := B) centre)
        (main3ComplexShearedExponentialEvaluationMatrix B alpha delta) := by
  ext r ij
  simpa only [main3RatioPowerEvaluationMatrix, columnScale,
    main3ComplexShearedExponentialEvaluationMatrix, mul_comm] using
    main3RatioPowerMonomial_eq_centerScale_mul_shearedExponential
      B (hsource r) (htarget r) ij

/-- Every selected full normalized-ratio minor is the corresponding complex
sheared minor times the product of its fixed centre-column factors. -/
theorem det_main3RatioPowerEvaluationMatrix_selected_eq_centerFactors_mul_complexSheared
    {ι : Type*} [Fintype ι]
    (B : ℕ) (omega omegaBar centre : ℂ)
    (points : ι → GeneralBidegreeFormPoint)
    (alpha delta : ι → ℂ)
    (hsource : ∀ r,
      centre * Complex.exp (alpha r) =
        main3EmbeddingSourceRatio omega omegaBar (points r))
    (htarget : ∀ r,
      centre ^ 2 * Complex.exp (2 * alpha r + delta r) =
        main3EmbeddingTargetRatio omega omegaBar (points r))
    (s : generalBidegreeFormIndex 1 B ↪ ι) :
    ((main3RatioPowerEvaluationMatrix
        B omega omegaBar points).submatrix s id).det =
      (∏ ij : generalBidegreeFormIndex 1 B,
        main3ComplexShearedCenterColumnScale centre ij) *
        ((main3ComplexShearedExponentialEvaluationMatrix
          B alpha delta).submatrix s id).det := by
  classical
  rw [main3RatioPowerEvaluationMatrix_eq_columnScale_complexSheared
    B omega omegaBar centre points alpha delta hsource htarget]
  let d := main3ComplexShearedCenterColumnScale (B := B) centre
  let E := main3ComplexShearedExponentialEvaluationMatrix B alpha delta
  have hmatrix : (columnScale d E).submatrix s id =
      Matrix.of fun i j => d j * (E.submatrix s id) i j := by
    ext i j
    simp [columnScale, d, E, mul_comm]
  rw [hmatrix]
  exact Matrix.det_mul_row d (E.submatrix s id)

/-- For a unit centre, all extracted column factors have norm one, so the
selected normalized-ratio determinant and the selected sheared determinant
have exactly the same norm. -/
theorem norm_det_main3RatioPowerEvaluationMatrix_selected_eq_complexSheared
    {ι : Type*} [Fintype ι]
    (B : ℕ) (omega omegaBar centre : ℂ)
    (points : ι → GeneralBidegreeFormPoint)
    (alpha delta : ι → ℂ)
    (hcentre : ‖centre‖ = 1)
    (hsource : ∀ r,
      centre * Complex.exp (alpha r) =
        main3EmbeddingSourceRatio omega omegaBar (points r))
    (htarget : ∀ r,
      centre ^ 2 * Complex.exp (2 * alpha r + delta r) =
        main3EmbeddingTargetRatio omega omegaBar (points r))
    (s : generalBidegreeFormIndex 1 B ↪ ι) :
    ‖((main3RatioPowerEvaluationMatrix
        B omega omegaBar points).submatrix s id).det‖ =
      ‖((main3ComplexShearedExponentialEvaluationMatrix
        B alpha delta).submatrix s id).det‖ := by
  rw [
    det_main3RatioPowerEvaluationMatrix_selected_eq_centerFactors_mul_complexSheared
      B omega omegaBar centre points alpha delta hsource htarget s,
    norm_mul, norm_prod]
  have hscale : ∀ ij : generalBidegreeFormIndex 1 B,
      ‖main3ComplexShearedCenterColumnScale centre ij‖ = 1 := by
    intro ij
    rw [main3ComplexShearedCenterColumnScale, norm_pow, hcentre, one_pow]
  simp_rw [hscale]
  simp

/-- The source local logarithm for an arbitrary embedding-ratio row. -/
def main3EmbeddingSourceLocalLog
    (omega omegaBar centre : ℂ) (z : GeneralBidegreeFormPoint) : ℂ :=
  complexUnitCircleSourceLocalLog
    (main3EmbeddingSourceRatio omega omegaBar z) centre

/-- The square-map defect local logarithm for an arbitrary embedding-ratio
row. -/
def main3EmbeddingSquareMapDefectLog
    (omega omegaBar : ℂ) (z : GeneralBidegreeFormPoint) : ℂ :=
  complexUnitCircleSquareMapDefectLog
    (main3EmbeddingSourceRatio omega omegaBar z)
    (main3EmbeddingTargetRatio omega omegaBar z)

/-- Branch-safe local logarithms of unit embedding ratios give the exact
selected determinant-norm alignment required by the complex Taylor engine. -/
theorem norm_det_main3RatioPowerEvaluationMatrix_selected_eq_localLogSheared
    {ι : Type*} [Fintype ι]
    (B : ℕ) (omega omegaBar centre : ℂ)
    (points : ι → GeneralBidegreeFormPoint)
    (hcentre : ‖centre‖ = 1)
    (hsourceNorm : ∀ r,
      ‖main3EmbeddingSourceRatio omega omegaBar (points r)‖ = 1)
    (htargetNorm : ∀ r,
      ‖main3EmbeddingTargetRatio omega omegaBar (points r)‖ = 1)
    (s : generalBidegreeFormIndex 1 B ↪ ι) :
    ‖((main3RatioPowerEvaluationMatrix
        B omega omegaBar points).submatrix s id).det‖ =
      ‖((main3ComplexShearedExponentialEvaluationMatrix B
        (fun r => main3EmbeddingSourceLocalLog
          omega omegaBar centre (points r))
        (fun r => main3EmbeddingSquareMapDefectLog
          omega omegaBar (points r))).submatrix s id).det‖ := by
  apply norm_det_main3RatioPowerEvaluationMatrix_selected_eq_complexSheared
    B omega omegaBar centre points
      (fun r => main3EmbeddingSourceLocalLog
        omega omegaBar centre (points r))
      (fun r => main3EmbeddingSquareMapDefectLog
        omega omegaBar (points r)) hcentre
  · intro r
    exact
      (complexUnitCircleLocalLogs_exactSquareMapParametrization
        (hsourceNorm r) (htargetNorm r) hcentre).1
  · intro r
    exact
      (complexUnitCircleLocalLogs_exactSquareMapParametrization
        (hsourceNorm r) (htargetNorm r) hcentre).2.1

/-- Membership in one accepted complex square-map cell supplies the exact
two sheared-coordinate bounds used by the determinant method.  The source
coordinate has cell scale `3/M`, while the defect coordinate retains the
finer rowwise square-map error. -/
theorem main3EmbeddingLocalLog_bounds_of_mem_squareMapCellPair
    {ι : Type*} {M : ℕ} (hM : 10 ≤ M)
    {i : ComplexUnitCircleSlopeCellIndex}
    (hi : i ∈ complexUnitCircleSlopeCellIndices M)
    (omega omegaBar centre : ℂ)
    (points : ι → GeneralBidegreeFormPoint)
    (hcell : ∀ r, InComplexUnitCircleSquareMapCellPair M i
      (main3EmbeddingSourceRatio omega omegaBar (points r),
        main3EmbeddingTargetRatio omega omegaBar (points r)))
    (hcentre : InComplexUnitCircleSlopeCell M i centre)
    (epsilon : ι → ℝ)
    (herror : ∀ r,
      ‖main3EmbeddingTargetRatio omega omegaBar (points r) -
        main3EmbeddingSourceRatio omega omegaBar (points r) ^ 2‖ ≤ epsilon r)
    (hepsilonMesh : ∀ r, epsilon r ≤ 1 / (M : ℝ)) :
    (∀ r,
      ‖main3EmbeddingSourceLocalLog omega omegaBar centre (points r)‖ ≤
        3 / (M : ℝ)) ∧
      (∀ r,
        ‖main3EmbeddingSquareMapDefectLog omega omegaBar (points r)‖ ≤
          (3 / 2) * epsilon r) ∧
      (∀ r,
        ‖main3EmbeddingSquareMapDefectLog omega omegaBar (points r)‖ ≤
          3 / (2 * (M : ℝ))) := by
  constructor
  · intro r
    rcases complexUnitCircleSquareMapCellPair_localLogCoordinates
      hM hi (hcell r) hcentre (herror r) (hepsilonMesh r) with
      ⟨hsource, _, _, _⟩
    simpa only [main3EmbeddingSourceLocalLog] using hsource.2
  constructor
  · intro r
    rcases complexUnitCircleSquareMapCellPair_localLogCoordinates
      hM hi (hcell r) hcentre (herror r) (hepsilonMesh r) with
      ⟨_, _, hdefect, _⟩
    simpa only [main3EmbeddingSquareMapDefectLog] using hdefect.2.1
  · intro r
    rcases complexUnitCircleSquareMapCellPair_localLogCoordinates
      hM hi (hcell r) hcentre (herror r) (hepsilonMesh r) with
      ⟨_, _, hdefect, _⟩
    simpa only [main3EmbeddingSquareMapDefectLog] using hdefect.2.2

end

end PellPaper
