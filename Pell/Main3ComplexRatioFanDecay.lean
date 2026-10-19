import Pell.Main3ComplexRatioShearedAlignment
import Pell.TwoLayerComplexFanDeterminantDecay

/-!
# Complex two-layer fan decay for selected main3 ratio minors

This module reindexes a selected complex sheared-exponential matrix from the
natural bidegree columns to the literal sheared grid, applies the complex
two-layer fan estimate, and transports the result back to the normalized
main3 embedding-ratio determinant.  Its final theorem states the hypotheses
directly in terms of one accepted complex square-map cell and rowwise
square-map errors.

No radial factor, embedding denominator, discriminant cost, integral-minor
vanishing, or fibre count is included.
-/

namespace PellPaper

noncomputable section

/-- Reindex a complex row coordinate on a selected full minor to the literal
sheared grid. -/
def main3ReindexedComplexCoordinate
    {ι : Type*} (B : ℕ) (s : generalBidegreeFormIndex 1 B ↪ ι)
    (f : ι → ℂ) : generalBidegreeGrid 1 B → ℂ :=
  fun r => f (s ((generalBidegreeGridPointEquiv 1 B).symm r))

/-- Reindexing both axes of a selected main3 complex sheared matrix gives the
literal complex sheared-exponential matrix used by the Taylor engine. -/
theorem reindex_main3ComplexShearedExponentialEvaluationMatrix_selected_eq_generalBidegreeSheared
    {ι : Type*} [Fintype ι]
    (B : ℕ) (alpha delta : ι → ℂ)
    (s : generalBidegreeFormIndex 1 B ↪ ι) :
    Matrix.reindex (generalBidegreeGridPointEquiv 1 B)
        (generalBidegreeGridPointEquiv 1 B)
        ((main3ComplexShearedExponentialEvaluationMatrix
          B alpha delta).submatrix s id) =
      generalBidegreeShearedExponentialEvaluationMatrixComplex 1 B
        (main3ReindexedComplexCoordinate B s alpha)
        (main3ReindexedComplexCoordinate B s delta) := by
  ext r p
  rcases (generalBidegreeGridPointEquiv 1 B).surjective p with ⟨ij, rfl⟩
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply]
  simp only [main3ComplexShearedExponentialEvaluationMatrix,
    main3ComplexShearedExponentialEntry,
    generalBidegreeShearedExponentialEvaluationMatrixComplex,
    main3ReindexedComplexCoordinate]
  rfl

/-- A selected main3 complex sheared determinant has the same norm as the
literal grid-indexed complex exponential determinant. -/
theorem norm_det_main3ComplexShearedExponentialEvaluationMatrix_selected_eq_generalBidegreeExponential
    {ι : Type*} [Fintype ι]
    (B : ℕ) (alpha delta : ι → ℂ)
    (s : generalBidegreeFormIndex 1 B ↪ ι) :
    ‖((main3ComplexShearedExponentialEvaluationMatrix
        B alpha delta).submatrix s id).det‖ =
      ‖(generalBidegreeExponentialEvaluationMatrixComplex 1 B
        (main3ReindexedComplexCoordinate B s alpha)
        (main3ReindexedComplexCoordinate B s delta)).det‖ := by
  let e := generalBidegreeGridPointEquiv 1 B
  let E := (main3ComplexShearedExponentialEvaluationMatrix
    B alpha delta).submatrix s id
  calc
    ‖E.det‖ = ‖(Matrix.reindex e e E).det‖ := by
      rw [Matrix.det_reindex_self]
    _ = ‖(generalBidegreeShearedExponentialEvaluationMatrixComplex 1 B
        (main3ReindexedComplexCoordinate B s alpha)
        (main3ReindexedComplexCoordinate B s delta)).det‖ := by
      rw [reindex_main3ComplexShearedExponentialEvaluationMatrix_selected_eq_generalBidegreeSheared]
    _ = ‖(generalBidegreeExponentialEvaluationMatrixComplex 1 B
        (main3ReindexedComplexCoordinate B s alpha)
        (main3ReindexedComplexCoordinate B s delta)).det‖ := by
      rw [generalBidegreeExponentialEvaluationMatrixComplex_eq_sheared]

/-- Exact two-layer fan decay for an arbitrary selected main3 complex
sheared minor. -/
theorem norm_det_main3ComplexShearedExponentialEvaluationMatrix_selected_le_twoLayerFan_exp_tail
    {ι : Type*} [Fintype ι]
    (B k : ℕ) (alpha delta : ι → ℂ)
    (s : generalBidegreeFormIndex 1 B ↪ ι)
    (ellM ellX : ℝ)
    (hellM : 0 < ellM)
    (hkpos : 1 ≤ k) (hkB : k ≤ B)
    (hfanLower : (2 * (k : ℝ) - 1) * ellM ≤ ellX)
    (hfanUpper : ellX ≤ (2 * (k : ℝ) + 1) * ellM)
    (halpha : ∀ r,
      ‖main3ReindexedComplexCoordinate B s alpha r‖ ≤ Real.exp (-ellM))
    (hdelta : ∀ r,
      ‖main3ReindexedComplexCoordinate B s delta r‖ ≤ Real.exp (-ellX)) :
    ‖((main3ComplexShearedExponentialEvaluationMatrix
        B alpha delta).submatrix s id).det‖ ≤
      (Nat.factorial (Fintype.card (generalBidegreeGrid 1 B)) : ℝ) *
        Real.exp (-twoLayerWeight B k ellM ellX) *
          (Real.exp (((1 + 2 * B : ℕ) : ℝ) + (B : ℝ))) ^
            Fintype.card (generalBidegreeGrid 1 B) := by
  rw [
    norm_det_main3ComplexShearedExponentialEvaluationMatrix_selected_eq_generalBidegreeExponential]
  exact
    norm_det_generalBidegreeExponentialEvaluationMatrixComplex_le_twoLayerFan_exp_tail_gridBounds
      B k (main3ReindexedComplexCoordinate B s alpha)
        (main3ReindexedComplexCoordinate B s delta)
        ellM ellX hellM hkpos hkB hfanLower hfanUpper halpha hdelta

/-- Exact two-layer fan decay for a selected normalized main3 ratio minor,
once its branch-safe local coordinates obey the two exponential scales. -/
theorem norm_det_main3RatioPowerEvaluationMatrix_selected_le_localLog_twoLayerFan_exp_tail
    {ι : Type*} [Fintype ι]
    (B k : ℕ) (omega omegaBar centre : ℂ)
    (points : ι → GeneralBidegreeFormPoint)
    (s : generalBidegreeFormIndex 1 B ↪ ι)
    (ellM ellX : ℝ)
    (hcentre : ‖centre‖ = 1)
    (hsourceNorm : ∀ r,
      ‖main3EmbeddingSourceRatio omega omegaBar (points r)‖ = 1)
    (htargetNorm : ∀ r,
      ‖main3EmbeddingTargetRatio omega omegaBar (points r)‖ = 1)
    (hellM : 0 < ellM)
    (hkpos : 1 ≤ k) (hkB : k ≤ B)
    (hfanLower : (2 * (k : ℝ) - 1) * ellM ≤ ellX)
    (hfanUpper : ellX ≤ (2 * (k : ℝ) + 1) * ellM)
    (halpha : ∀ r,
      ‖main3ReindexedComplexCoordinate B s
        (fun q => main3EmbeddingSourceLocalLog
          omega omegaBar centre (points q)) r‖ ≤ Real.exp (-ellM))
    (hdelta : ∀ r,
      ‖main3ReindexedComplexCoordinate B s
        (fun q => main3EmbeddingSquareMapDefectLog
          omega omegaBar (points q)) r‖ ≤ Real.exp (-ellX)) :
    ‖((main3RatioPowerEvaluationMatrix
        B omega omegaBar points).submatrix s id).det‖ ≤
      (Nat.factorial (Fintype.card (generalBidegreeGrid 1 B)) : ℝ) *
        Real.exp (-twoLayerWeight B k ellM ellX) *
          (Real.exp (((1 + 2 * B : ℕ) : ℝ) + (B : ℝ))) ^
            Fintype.card (generalBidegreeGrid 1 B) := by
  rw [norm_det_main3RatioPowerEvaluationMatrix_selected_eq_localLogSheared
    B omega omegaBar centre points hcentre hsourceNorm htargetNorm s]
  exact
    norm_det_main3ComplexShearedExponentialEvaluationMatrix_selected_le_twoLayerFan_exp_tail
      B k
        (fun q => main3EmbeddingSourceLocalLog
          omega omegaBar centre (points q))
        (fun q => main3EmbeddingSquareMapDefectLog
          omega omegaBar (points q))
        s ellM ellX hellM hkpos hkB hfanLower hfanUpper halpha hdelta

/-- Cell-specialized two-layer fan decay.  The source scale comes from the
common cell, while the defect scale retains the supplied rowwise arithmetic
error instead of being degraded to the mesh width. -/
theorem norm_det_main3RatioPowerEvaluationMatrix_selected_le_of_mem_complexSquareMapCell
    {ι : Type*} [Fintype ι]
    {M : ℕ} (hM : 10 ≤ M)
    {i : ComplexUnitCircleSlopeCellIndex}
    (hi : i ∈ complexUnitCircleSlopeCellIndices M)
    (B k : ℕ) (omega omegaBar centre : ℂ)
    (points : ι → GeneralBidegreeFormPoint)
    (s : generalBidegreeFormIndex 1 B ↪ ι)
    (hcell : ∀ r, InComplexUnitCircleSquareMapCellPair M i
      (main3EmbeddingSourceRatio omega omegaBar (points r),
        main3EmbeddingTargetRatio omega omegaBar (points r)))
    (hcentre : InComplexUnitCircleSlopeCell M i centre)
    (epsilon : ι → ℝ)
    (herror : ∀ r,
      ‖main3EmbeddingTargetRatio omega omegaBar (points r) -
        main3EmbeddingSourceRatio omega omegaBar (points r) ^ 2‖ ≤ epsilon r)
    (hepsilonMesh : ∀ r, epsilon r ≤ 1 / (M : ℝ))
    (ellM ellX : ℝ)
    (hsourceScale : 3 / (M : ℝ) ≤ Real.exp (-ellM))
    (hdefectScale : ∀ r, (3 / 2) * epsilon r ≤ Real.exp (-ellX))
    (hellM : 0 < ellM)
    (hkpos : 1 ≤ k) (hkB : k ≤ B)
    (hfanLower : (2 * (k : ℝ) - 1) * ellM ≤ ellX)
    (hfanUpper : ellX ≤ (2 * (k : ℝ) + 1) * ellM) :
    ‖((main3RatioPowerEvaluationMatrix
        B omega omegaBar points).submatrix s id).det‖ ≤
      (Nat.factorial (Fintype.card (generalBidegreeGrid 1 B)) : ℝ) *
        Real.exp (-twoLayerWeight B k ellM ellX) *
          (Real.exp (((1 + 2 * B : ℕ) : ℝ) + (B : ℝ))) ^
            Fintype.card (generalBidegreeGrid 1 B) := by
  have hbounds := main3EmbeddingLocalLog_bounds_of_mem_squareMapCellPair
    hM hi omega omegaBar centre points hcell hcentre epsilon herror hepsilonMesh
  apply
    norm_det_main3RatioPowerEvaluationMatrix_selected_le_localLog_twoLayerFan_exp_tail
      B k omega omegaBar centre points s ellM ellX hcentre.1
      (fun r => (hcell r).1.1) (fun r => (hcell r).2.1)
      hellM hkpos hkB hfanLower hfanUpper
  · intro r
    exact (hbounds.1 _).trans hsourceScale
  · intro r
    exact (hbounds.2.1 _).trans (hdefectScale _)

end

end PellPaper
