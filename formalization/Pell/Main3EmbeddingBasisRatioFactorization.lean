import Pell.Main3EmbeddingBasisEvaluationMinorTransport
import Mathlib.Tactic

/-!
# Radial and ratio factorization of the main3 embedding matrix

The reflected embedding-basis row has the manuscript orientation

`alpha^i * starAlpha^(1-i) * starGamma^j * gamma^(B-j)`.

This module factors it exactly into the row radial term
`starAlpha * gamma^B` and the normalized ratio powers
`(alpha/starAlpha)^i * (starGamma/gamma)^j`.  It then records the resulting
selected-minor determinant and norm identities.  No localization or
determinant estimate is asserted.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- The source embedding ratio attached to an integral homogeneous point
for a chosen pair of quadratic-basis images. -/
def main3EmbeddingSourceRatio
    (omega omegaBar : ℂ) (z : GeneralBidegreeFormPoint) : ℂ :=
  ((z.1.1 : ℂ) + omega * (z.1.2 : ℂ)) /
    ((z.1.1 : ℂ) + omegaBar * (z.1.2 : ℂ))

/-- The target embedding ratio in the manuscript orientation. -/
def main3EmbeddingTargetRatio
    (omega omegaBar : ℂ) (z : GeneralBidegreeFormPoint) : ℂ :=
  ((z.2.1 : ℂ) + omegaBar * (z.2.2 : ℂ)) /
    ((z.2.1 : ℂ) + omega * (z.2.2 : ℂ))

/-- The row factor removed before applying the normalized determinant
estimate. -/
def main3EmbeddingRadialRowFactor
    (B : ℕ) (omega omegaBar : ℂ) (z : GeneralBidegreeFormPoint) : ℂ :=
  ((z.1.1 : ℂ) + omegaBar * (z.1.2 : ℂ)) *
    (((z.2.1 : ℂ) + omega * (z.2.2 : ℂ)) ^ B)

/-- The normalized ratio-power row on the bidegree-`(1,B)` column grid. -/
def main3RatioPowerMonomial
    (B : ℕ) (sourceRatio targetRatio : ℂ)
    (ij : generalBidegreeFormIndex 1 B) : ℂ :=
  sourceRatio ^ ij.1.1 * targetRatio ^ ij.2.1

/-- The normalized ratio-power evaluation matrix for an arbitrary point
family. -/
def main3RatioPowerEvaluationMatrix
    {ι : Type*} (B : ℕ) (omega omegaBar : ℂ)
    (points : ι → GeneralBidegreeFormPoint) :
    Matrix ι (generalBidegreeFormIndex 1 B) ℂ :=
  fun r ij => main3RatioPowerMonomial B
    (main3EmbeddingSourceRatio omega omegaBar (points r))
    (main3EmbeddingTargetRatio omega omegaBar (points r)) ij

private theorem radial_mul_targetRatio_pow
    (B j : ℕ) (gamma starGamma : ℂ)
    (hj : j ≤ B) (hgamma : gamma ≠ 0) :
    gamma ^ B * (starGamma / gamma) ^ j =
      starGamma ^ j * gamma ^ (B - j) := by
  rw [div_pow, pow_sub₀ gamma hgamma hj, div_eq_mul_inv]
  ring

private theorem starAlpha_mul_sourceRatio_pow
    (i : Fin 2) (alpha starAlpha : ℂ) (hstarAlpha : starAlpha ≠ 0) :
    starAlpha * (alpha / starAlpha) ^ i.1 =
      alpha ^ i.1 * starAlpha ^ (1 - i.1) := by
  fin_cases i
  · simp
  · norm_num
    field_simp

/-- Exact entrywise radial/ratio factorization of the reflected embedding
matrix. -/
theorem main3ReflectedEmbeddingBasisEvaluationMatrix_apply_eq_radial_mul_ratioPower
    {ι : Type*} (B : ℕ) (omega omegaBar : ℂ)
    (points : ι → GeneralBidegreeFormPoint)
    (r : ι) (ij : generalBidegreeFormIndex 1 B)
    (hsourceDen :
      ((points r).1.1 : ℂ) + omegaBar * ((points r).1.2 : ℂ) ≠ 0)
    (htargetDen :
      ((points r).2.1 : ℂ) + omega * ((points r).2.2 : ℂ) ≠ 0) :
    main3ReflectedEmbeddingBasisEvaluationMatrix
        B omega omegaBar points r ij =
      main3EmbeddingRadialRowFactor B omega omegaBar (points r) *
        main3RatioPowerEvaluationMatrix B omega omegaBar points r ij := by
  let alpha : ℂ :=
    ((points r).1.1 : ℂ) + omega * ((points r).1.2 : ℂ)
  let starAlpha : ℂ :=
    ((points r).1.1 : ℂ) + omegaBar * ((points r).1.2 : ℂ)
  let gamma : ℂ :=
    ((points r).2.1 : ℂ) + omega * ((points r).2.2 : ℂ)
  let starGamma : ℂ :=
    ((points r).2.1 : ℂ) + omegaBar * ((points r).2.2 : ℂ)
  have hj : ij.2.1 ≤ B := Nat.le_of_lt_succ ij.2.2
  have hsource :
      starAlpha * (alpha / starAlpha) ^ ij.1.1 =
        alpha ^ ij.1.1 * starAlpha ^ (1 - ij.1.1) :=
    starAlpha_mul_sourceRatio_pow ij.1 alpha starAlpha hsourceDen
  have htarget :
      gamma ^ B * (starGamma / gamma) ^ ij.2.1 =
        starGamma ^ ij.2.1 * gamma ^ (B - ij.2.1) :=
    radial_mul_targetRatio_pow B ij.2.1 gamma starGamma hj htargetDen
  rw [main3ReflectedEmbeddingBasisEvaluationMatrix_apply]
  change alpha ^ ij.1.1 * starAlpha ^ (1 - ij.1.1) *
      (starGamma ^ ij.2.1 * gamma ^ (B - ij.2.1)) =
    (starAlpha * gamma ^ B) *
      ((alpha / starAlpha) ^ ij.1.1 *
        (starGamma / gamma) ^ ij.2.1)
  rw [← hsource, ← htarget]
  ring

/-- Matrix form of the row factorization. -/
theorem main3ReflectedEmbeddingBasisEvaluationMatrix_eq_diagonal_mul_ratioPower
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : ℕ) (omega omegaBar : ℂ)
    (points : ι → GeneralBidegreeFormPoint)
    (hsourceDen : ∀ r,
      ((points r).1.1 : ℂ) + omegaBar * ((points r).1.2 : ℂ) ≠ 0)
    (htargetDen : ∀ r,
      ((points r).2.1 : ℂ) + omega * ((points r).2.2 : ℂ) ≠ 0) :
    main3ReflectedEmbeddingBasisEvaluationMatrix B omega omegaBar points =
      Matrix.diagonal
          (fun r => main3EmbeddingRadialRowFactor
            B omega omegaBar (points r)) *
        main3RatioPowerEvaluationMatrix B omega omegaBar points := by
  ext r ij
  rw [Matrix.diagonal_mul]
  exact
    main3ReflectedEmbeddingBasisEvaluationMatrix_apply_eq_radial_mul_ratioPower
      B omega omegaBar points r ij (hsourceDen r) (htargetDen r)

/-- A selected full reflected embedding minor is the selected normalized
ratio minor with exactly one radial factor from every selected row. -/
theorem det_main3ReflectedEmbeddingBasisEvaluationMatrix_selected_eq_prod_radial_mul_det_ratioPower
    {ι : Type*} [Fintype ι]
    (B : ℕ) (omega omegaBar : ℂ)
    (points : ι → GeneralBidegreeFormPoint)
    (s : generalBidegreeFormIndex 1 B ↪ ι)
    (hsourceDen : ∀ r,
      ((points r).1.1 : ℂ) + omegaBar * ((points r).1.2 : ℂ) ≠ 0)
    (htargetDen : ∀ r,
      ((points r).2.1 : ℂ) + omega * ((points r).2.2 : ℂ) ≠ 0) :
    ((main3ReflectedEmbeddingBasisEvaluationMatrix
        B omega omegaBar points).submatrix s id).det =
      (∏ r : generalBidegreeFormIndex 1 B,
        main3EmbeddingRadialRowFactor B omega omegaBar (points (s r))) *
        ((main3RatioPowerEvaluationMatrix
          B omega omegaBar points).submatrix s id).det := by
  have hmatrix :
      (main3ReflectedEmbeddingBasisEvaluationMatrix
          B omega omegaBar points).submatrix s id =
        Matrix.diagonal
            (fun r : generalBidegreeFormIndex 1 B =>
              main3EmbeddingRadialRowFactor B omega omegaBar (points (s r))) *
          (main3RatioPowerEvaluationMatrix
            B omega omegaBar points).submatrix s id := by
    ext r ij
    rw [Matrix.diagonal_mul]
    exact
      main3ReflectedEmbeddingBasisEvaluationMatrix_apply_eq_radial_mul_ratioPower
        B omega omegaBar points (s r) ij
          (hsourceDen (s r)) (htargetDen (s r))
  rw [hmatrix, Matrix.det_mul, Matrix.det_diagonal]

/-- Norm form of the selected-minor factorization, ready for separate radial
and normalized determinant estimates. -/
theorem norm_det_main3ReflectedEmbeddingBasisEvaluationMatrix_selected_eq_prod_norm_radial_mul_norm_det_ratioPower
    {ι : Type*} [Fintype ι]
    (B : ℕ) (omega omegaBar : ℂ)
    (points : ι → GeneralBidegreeFormPoint)
    (s : generalBidegreeFormIndex 1 B ↪ ι)
    (hsourceDen : ∀ r,
      ((points r).1.1 : ℂ) + omegaBar * ((points r).1.2 : ℂ) ≠ 0)
    (htargetDen : ∀ r,
      ((points r).2.1 : ℂ) + omega * ((points r).2.2 : ℂ) ≠ 0) :
    ‖((main3ReflectedEmbeddingBasisEvaluationMatrix
        B omega omegaBar points).submatrix s id).det‖ =
      (∏ r : generalBidegreeFormIndex 1 B,
        ‖main3EmbeddingRadialRowFactor B omega omegaBar (points (s r))‖) *
        ‖((main3RatioPowerEvaluationMatrix
          B omega omegaBar points).submatrix s id).det‖ := by
  rw [
    det_main3ReflectedEmbeddingBasisEvaluationMatrix_selected_eq_prod_radial_mul_det_ratioPower
      B omega omegaBar points s hsourceDen htargetDen,
    norm_mul, norm_prod]

end

end PellPaper
