import Pell.ShiftedSquareExplicitPlaceGeometry
import Pell.RealSquareMapCellPairCover

/-!
# Real-place shifted-square packages enter the finite square-map cells

This adapter turns the complex localization certificate at the explicit real
place into the literal real source/target hypotheses used by the finite cell
pair cover.  The only quantitative input left explicit is the cross-multiplied
mesh absorption `8 M sqrt(|a|) ≤ n`; a later range lemma supplies it from the
main3 large-analytic cutoff.

No determinant or arithmetic point-count estimate occurs here.
-/

namespace PellPaper

noncomputable section

local instance shiftedSquareRealPlaceCellPairAdapter_numberField (a : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

/-- A complex number with zero imaginary part is its real coordinate. -/
private theorem complex_eq_real_of_im_eq_zero (z : ℂ) (hz : z.im = 0) :
    z = (z.re : ℂ) := by
  apply Complex.ext
  · simp
  · simpa using hz

/-- For real source and target ratios, the invariant complex quotient norm is
the literal relative square-map error used by the real cell cover. -/
theorem shiftedSquare_realRatios_quotientError_eq
    {source target : ℂ}
    (hsourceIm : source.im = 0) (htargetIm : target.im = 0) :
    ‖source⁻¹ ^ 2 * target - 1‖ =
      |target.re / |source.re| ^ 2 - 1| := by
  rw [complex_eq_real_of_im_eq_zero source hsourceIm,
    complex_eq_real_of_im_eq_zero target htargetIm]
  simp only [Complex.ofReal_re]
  rw [← Complex.ofReal_inv, ← Complex.ofReal_pow,
    ← Complex.ofReal_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]
  congr 1
  rw [sq_abs]
  simp [div_eq_mul_inv, mul_comm]

/-- The cross-multiplied mesh condition implies the normalized quotient error
required by a mesh of size `M`. -/
theorem shiftedSquare_quotientError_le_mesh
    {a : ℤ} {n M : ℕ} (ha : a ≠ 0) (hM : 0 < M)
    (hn : 2 * Real.sqrt |(a : ℝ)| ≤ (n : ℝ))
    (hmesh : 8 * (M : ℝ) * Real.sqrt |(a : ℝ)| ≤ (n : ℝ)) :
    (8 * Real.sqrt |(a : ℝ)|) / (n : ℝ) ≤ 1 / (M : ℝ) := by
  have hsqrtPos : 0 < Real.sqrt |(a : ℝ)| := by
    exact Real.sqrt_pos.2 (abs_pos.mpr (by exact_mod_cast ha))
  have hnPos : (0 : ℝ) < n := by nlinarith
  have hMPos : (0 : ℝ) < M := by exact_mod_cast hM
  apply (div_le_div_iff₀ hnPos hMPos).2
  nlinarith

/-- At the explicit positive real place, a simultaneous normalized package
lies in one of the literal `36 M scaleCount` real square-map cell pairs. -/
theorem exists_shiftedSquare_positiveRealPlace_realSquareMapCellPair
    {a : ℤ} {d w n M : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (ha : a < 0) (hd : 0 < d) (hw : 0 < w)
    (hn : 2 * Real.sqrt |(a : ℝ)| ≤ (n : ℝ))
    (hM : 0 < M)
    (hmesh : 8 * (M : ℝ) * Real.sqrt |(a : ℝ)| ≤ (n : ℝ))
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq) :
    let sigma := shiftedSquarePositiveRealPlaceEmbedding a ha
    let source := shiftedSquareSourceEmbeddingRatio P sigma
    let target := shiftedSquareTargetEmbeddingRatio P sigma
    ∃ i ∈ realSquareMapCellPairIndices
        (shiftedSquareEmbeddingScaleLoss a) M,
      InRealSquareMapCellPair (shiftedSquareEmbeddingScaleLoss a) M i
        (source.re, target.re) := by
  let sigma := shiftedSquarePositiveRealPlaceEmbedding a ha
  let source := shiftedSquareSourceEmbeddingRatio P sigma
  let target := shiftedSquareTargetEmbeddingRatio P sigma
  have hloc := shiftedSquare_embeddingRatio_localizationCertificate
    (ne_of_lt ha) hd hw hn P sigma
  have hgeo := shiftedSquare_positiveRealPlace_ratioGeometry ha P
  have hsourceEq : source = (source.re : ℂ) :=
    complex_eq_real_of_im_eq_zero source (by
      simpa only [source, sigma] using hgeo.source_ratio_im_eq_zero)
  have htargetEq : target = (target.re : ℂ) :=
    complex_eq_real_of_im_eq_zero target (by
      simpa only [target, sigma] using hgeo.target_ratio_im_eq_zero)
  have hsourceNorm : ‖source‖ = |source.re| := by
    calc
      ‖source‖ = ‖(source.re : ℂ)‖ := congrArg norm hsourceEq
      _ = |source.re| := by rw [Complex.norm_real, Real.norm_eq_abs]
  have hF : 1 ≤ shiftedSquareEmbeddingScaleLoss a := by
    have haInt : (1 : ℤ) ≤ |a| := by
      rw [abs_of_neg ha]
      omega
    have haReal : (1 : ℝ) ≤ |(a : ℝ)| := by exact_mod_cast haInt
    unfold shiftedSquareEmbeddingScaleLoss
    nlinarith
  have hsourceNe : source.re ≠ 0 := by
    simpa only [source, sigma] using hgeo.source_ratio_re_ne_zero
  have hlower : annularLowerRadius (shiftedSquareEmbeddingScaleLoss a) ≤
      |source.re| := by
    rw [annularLowerRadius, ← hsourceNorm]
    simpa only [one_div] using hloc.source_ratio_norm_bounds.1
  have hupper : |source.re| ≤ shiftedSquareEmbeddingScaleLoss a ^ 2 := by
    rw [← hsourceNorm]
    exact hloc.source_ratio_norm_bounds.2
  have htargetNonneg : 0 ≤ target.re := by
    have htargetPos : 0 < target.re := by
      simpa only [target, sigma] using hgeo.target_ratio_re_pos
    exact htargetPos.le
  have herror : |target.re / |source.re| ^ 2 - 1| ≤ 1 / (M : ℝ) := by
    rw [← shiftedSquare_realRatios_quotientError_eq
      (source := source) (target := target)
      (by simpa only [source, sigma] using hgeo.source_ratio_im_eq_zero)
      (by simpa only [target, sigma] using hgeo.target_ratio_im_eq_zero)]
    exact hloc.quotient_error.trans
      (shiftedSquare_quotientError_le_mesh (ne_of_lt ha) hM hn hmesh)
  simpa only [source, target, sigma] using
    exists_mem_realSquareMapCellPair hF hM hsourceNe hlower hupper
      htargetNonneg herror

end

end PellPaper
