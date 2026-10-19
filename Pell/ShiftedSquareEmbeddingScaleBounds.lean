import Pell.ShiftedSquareQuadraticEmbeddingLower
import Pell.ShiftedSquareTargetEmbeddingRoute
import Pell.ShiftedSquareScaleComparability
import Pell.ShiftedSquareContentScaleBounds
import Mathlib.Tactic

/-!
# Polynomial scale bounds for primitive shifted-square coordinates

The exact source and target embedding boxes have asymmetric quotient forms.
This file converts them to the symmetric norm scales `E_alpha` and `E_gamma`
used by the determinant argument.  A single explicit loss
`512 * |a|` works for both primitive elements at every infinite place.
-/

namespace PellPaper

noncomputable section

/-- The manuscript source scale `E_alpha = d₀ C₀ / r²`. -/
def shiftedSquareEAlpha
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq) : ℝ :=
  ((shiftedSquareD₀ d * P.minkowski.C₀ : ℕ) : ℝ) / (P.r : ℝ) ^ 2

/-- The manuscript target scale `E_gamma = w C₀² / ell²`. -/
def shiftedSquareEGamma
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq) : ℝ :=
  ((w * P.minkowski.C₀ ^ 2 : ℕ) : ℝ) / (P.ell : ℝ) ^ 2

/-- A simple literal polynomial loss, uniform for source and target. -/
def shiftedSquareEmbeddingScaleLoss (a : ℤ) : ℝ :=
  512 * |(a : ℝ)|

/-- The content bound supplies the source scale floor used in the unbalanced
range arithmetic. -/
theorem shiftedSquareEAlpha_ge_sourceFloor
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq) :
    (shiftedSquareD₀ d : ℝ) / (2 * (P.minkowski.C₀ : ℝ)) ≤
      shiftedSquareEAlpha P := by
  simpa only [shiftedSquareEAlpha] using shiftedSquare_sourceNormScale_lower P

/-- Target-content normalization makes the primitive target scale at least
the original `w` scale. -/
theorem shiftedSquareEGamma_ge_targetFloor
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq) :
    (w : ℝ) ≤ shiftedSquareEGamma P := by
  simpa only [shiftedSquareEGamma] using shiftedSquare_targetNormScale_lower P

/-- For a nonzero integral shift, the polynomial loss dominates the sharper
factor `512 * sqrt |a|` arising in the quotient calculation. -/
theorem shiftedSquareEmbeddingScaleLoss_ge_sqrt
    {a : ℤ} (ha : a ≠ 0) :
    512 * Real.sqrt |(a : ℝ)| ≤ shiftedSquareEmbeddingScaleLoss a := by
  have hAone : (1 : ℝ) ≤ |(a : ℝ)| := by
    exact_mod_cast Int.one_le_abs ha
  have hsqrtA : Real.sqrt |(a : ℝ)| ≤ |(a : ℝ)| := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · nlinarith [sq_nonneg (|(a : ℝ)| - 1)]
  exact mul_le_mul_of_nonneg_left hsqrtA (by norm_num)

private theorem source_exactBox_to_scaleBounds
    {A d₀ C r F x : ℝ}
    (hA : 1 ≤ A) (hd₀ : 0 < d₀) (hC : 1 ≤ C) (hr : 0 < r)
    (hF : 512 * Real.sqrt A ≤ F)
    (hlower : ((d₀ * C) / (8 * Real.sqrt (d₀ * Real.sqrt A))) / r ≤ x)
    (hupper : x < (8 * Real.sqrt (d₀ * Real.sqrt A)) / r) :
    Real.sqrt ((d₀ * C) / r ^ 2) / F ≤ x ∧
      x ≤ F * Real.sqrt ((d₀ * C) / r ^ 2) := by
  have hsqrtAOne : 1 ≤ Real.sqrt A := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hA
  have hFpos : 0 < F := by nlinarith
  have hEightF : (8 : ℝ) ≤ F := by nlinarith
  have hEightSqrtF : 8 * Real.sqrt A ≤ F := by nlinarith
  have h64 : 64 * Real.sqrt A ≤ F ^ 2 := by
    calc
      64 * Real.sqrt A = 8 * (8 * Real.sqrt A) := by ring
      _ ≤ F * F := mul_le_mul hEightF hEightSqrtF (by positivity) hFpos.le
      _ = F ^ 2 := by ring
  have h64C : 64 * Real.sqrt A ≤ F ^ 2 * C :=
    h64.trans (le_mul_of_one_le_right (sq_nonneg F) hC)
  have hinside : 0 < d₀ * Real.sqrt A :=
    mul_pos hd₀ (lt_of_lt_of_le zero_lt_one hsqrtAOne)
  have hproduct : 0 < d₀ * C := mul_pos hd₀ (lt_of_lt_of_le zero_lt_one hC)
  have hcore :
      8 * Real.sqrt (d₀ * Real.sqrt A) ≤
        F * Real.sqrt (d₀ * C) := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).1
    calc
      (8 * Real.sqrt (d₀ * Real.sqrt A)) ^ 2 =
          d₀ * (64 * Real.sqrt A) := by
        rw [mul_pow, Real.sq_sqrt hinside.le]
        ring
      _ ≤ d₀ * (F ^ 2 * C) :=
        mul_le_mul_of_nonneg_left h64C hd₀.le
      _ = (F * Real.sqrt (d₀ * C)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hproduct.le]
        ring
  have hsqrtScale :
      Real.sqrt ((d₀ * C) / r ^ 2) = Real.sqrt (d₀ * C) / r := by
    rw [Real.sqrt_div hproduct.le, Real.sqrt_sq_eq_abs, abs_of_pos hr]
  have hbaseLower :
      Real.sqrt (d₀ * C) / F ≤
        (d₀ * C) / (8 * Real.sqrt (d₀ * Real.sqrt A)) := by
    apply (div_le_div_iff₀ hFpos (by positivity)).2
    calc
      Real.sqrt (d₀ * C) * (8 * Real.sqrt (d₀ * Real.sqrt A)) =
          (8 * Real.sqrt (d₀ * Real.sqrt A)) * Real.sqrt (d₀ * C) := by ring
      _ ≤ (F * Real.sqrt (d₀ * C)) * Real.sqrt (d₀ * C) :=
        mul_le_mul_of_nonneg_right hcore (Real.sqrt_nonneg _)
      _ = F * (Real.sqrt (d₀ * C) ^ 2) := by ring
      _ = (d₀ * C) * F := by rw [Real.sq_sqrt hproduct.le]; ring
  constructor
  · calc
      Real.sqrt ((d₀ * C) / r ^ 2) / F =
          (Real.sqrt (d₀ * C) / F) / r := by rw [hsqrtScale]; ring
      _ ≤ ((d₀ * C) / (8 * Real.sqrt (d₀ * Real.sqrt A))) / r :=
        div_le_div_of_nonneg_right hbaseLower hr.le
      _ ≤ x := hlower
  · calc
      x ≤ (8 * Real.sqrt (d₀ * Real.sqrt A)) / r := hupper.le
      _ ≤ (F * Real.sqrt (d₀ * C)) / r :=
        div_le_div_of_nonneg_right hcore hr.le
      _ = F * Real.sqrt ((d₀ * C) / r ^ 2) := by rw [hsqrtScale]; ring

private theorem target_exactBox_to_scaleBounds
    {A d₀ C ell w n F x : ℝ}
    (hA : 1 ≤ A) (hd₀ : 0 < d₀) (hC : 1 ≤ C)
    (hell : 0 < ell) (hw : 0 < w) (hn : 0 < n)
    (hF : 512 * Real.sqrt A ≤ F)
    (hscaleUpper : n ≤ 4 * d₀ * Real.sqrt w)
    (hscaleLower : d₀ * Real.sqrt w ≤ 2 * n)
    (hlower : (C ^ 2 * (n / 4)) /
        ((8 * Real.sqrt (d₀ * Real.sqrt A)) ^ 2 * ell) ≤ x)
    (hupper : x ≤ (C ^ 2 * (2 * n)) /
        (((d₀ * C / (8 * Real.sqrt (d₀ * Real.sqrt A))) ^ 2) * ell)) :
    Real.sqrt ((w * C ^ 2) / ell ^ 2) / F ≤ x ∧
      x ≤ F * Real.sqrt ((w * C ^ 2) / ell ^ 2) := by
  have hsqrtAOne : 1 ≤ Real.sqrt A := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hA
  have hsqrtAPos : 0 < Real.sqrt A := lt_of_lt_of_le zero_lt_one hsqrtAOne
  have hFpos : 0 < F := by nlinarith
  have hFC : 512 * Real.sqrt A ≤ F * C :=
    hF.trans (le_mul_of_one_le_right hFpos.le hC)
  have hsqrtWPos : 0 < Real.sqrt w := Real.sqrt_pos.2 hw
  have hinside : 0 < d₀ * Real.sqrt A := mul_pos hd₀ hsqrtAPos
  have hproduct : 0 < d₀ * C := mul_pos hd₀ (lt_of_lt_of_le zero_lt_one hC)
  have hsqrtScale :
      Real.sqrt ((w * C ^ 2) / ell ^ 2) = C * Real.sqrt w / ell := by
    rw [Real.sqrt_div (by positivity), Real.sqrt_mul hw.le,
      Real.sqrt_sq_eq_abs, abs_of_pos (lt_of_lt_of_le zero_lt_one hC),
      Real.sqrt_sq_eq_abs, abs_of_pos hell]
    ring
  have hlowerRewrite :
      (C ^ 2 * n) / (256 * d₀ * Real.sqrt A * ell) ≤ x := by
    calc
      (C ^ 2 * n) / (256 * d₀ * Real.sqrt A * ell) =
          (C ^ 2 * (n / 4)) /
            ((8 * Real.sqrt (d₀ * Real.sqrt A)) ^ 2 * ell) := by
        rw [mul_pow, Real.sq_sqrt hinside.le]
        (field_simp; ring)
      _ ≤ x := hlower
  have hupperRewrite :
      x ≤ (128 * n * Real.sqrt A) / (d₀ * ell) := by
    calc
      x ≤ (C ^ 2 * (2 * n)) /
          (((d₀ * C / (8 * Real.sqrt (d₀ * Real.sqrt A))) ^ 2) * ell) :=
        hupper
      _ = (128 * n * Real.sqrt A) / (d₀ * ell) := by
        simp only [div_pow, mul_pow, Real.sq_sqrt hinside.le]
        (field_simp; ring)
  have hbaseLower :
      C * Real.sqrt w / F ≤
        (C ^ 2 * n) / (256 * d₀ * Real.sqrt A) := by
    apply (div_le_div_iff₀ hFpos (by positivity)).2
    have hscaleMul :
        C * Real.sqrt w * (256 * d₀ * Real.sqrt A) ≤
          C * n * (512 * Real.sqrt A) := by
      calc
        C * Real.sqrt w * (256 * d₀ * Real.sqrt A) =
            (256 * C * Real.sqrt A) * (d₀ * Real.sqrt w) := by ring
        _ ≤ (256 * C * Real.sqrt A) * (2 * n) :=
          mul_le_mul_of_nonneg_left hscaleLower (by positivity)
        _ = C * n * (512 * Real.sqrt A) := by ring
    calc
      C * Real.sqrt w * (256 * d₀ * Real.sqrt A) ≤
          C * n * (512 * Real.sqrt A) := hscaleMul
      _ ≤ C * n * (F * C) :=
        mul_le_mul_of_nonneg_left hFC (by positivity)
      _ = C ^ 2 * n * F := by ring
  have hbaseUpper :
      (128 * n * Real.sqrt A) / d₀ ≤ F * (C * Real.sqrt w) := by
    apply (div_le_iff₀ hd₀).2
    calc
      128 * n * Real.sqrt A ≤
          128 * (4 * d₀ * Real.sqrt w) * Real.sqrt A := by
        gcongr
      _ = (512 * Real.sqrt A) * (d₀ * Real.sqrt w) := by ring
      _ ≤ (F * C) * (d₀ * Real.sqrt w) :=
        mul_le_mul_of_nonneg_right hFC (by positivity)
      _ = F * (C * Real.sqrt w) * d₀ := by ring
  constructor
  · calc
      Real.sqrt ((w * C ^ 2) / ell ^ 2) / F =
          (C * Real.sqrt w / F) / ell := by rw [hsqrtScale]; ring
      _ ≤ ((C ^ 2 * n) / (256 * d₀ * Real.sqrt A)) / ell :=
        div_le_div_of_nonneg_right hbaseLower hell.le
      _ = (C ^ 2 * n) / (256 * d₀ * Real.sqrt A * ell) := by ring
      _ ≤ x := hlowerRewrite
  · calc
      x ≤ (128 * n * Real.sqrt A) / (d₀ * ell) := hupperRewrite
      _ = ((128 * n * Real.sqrt A) / d₀) / ell := by ring
      _ ≤ (F * (C * Real.sqrt w)) / ell :=
        div_le_div_of_nonneg_right hbaseUpper hell.le
      _ = F * Real.sqrt ((w * C ^ 2) / ell ^ 2) := by rw [hsqrtScale]; ring

/-- Every primitive source element is polynomially comparable to
`sqrt E_alpha` at every infinite place. -/
theorem shiftedSquare_sourceEmbedding_scaleBounds
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (ha : a ≠ 0) (hd : 0 < d)
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq)
    (v : NumberField.InfinitePlace (rationalQuadraticAlgebra (-a))) :
    Real.sqrt (shiftedSquareEAlpha P) / shiftedSquareEmbeddingScaleLoss a ≤
        v (shiftedSquareIntegralBasisElement P.basis P.x) ∧
      v (shiftedSquareIntegralBasisElement P.basis P.x) ≤
        shiftedSquareEmbeddingScaleLoss a * Real.sqrt (shiftedSquareEAlpha P) := by
  have hA : (1 : ℝ) ≤ |(a : ℝ)| := by exact_mod_cast Int.one_le_abs ha
  have hd₀ : (0 : ℝ) < shiftedSquareD₀ d := by
    exact_mod_cast shiftedSquareD₀_pos hd
  have hC : (1 : ℝ) ≤ P.minkowski.C₀ := by exact_mod_cast P.minkowski.C₀_pos
  have hr : (0 : ℝ) < P.r := by exact_mod_cast P.r_pos
  have hbox := shiftedSquare_sourceEmbedding_twoSided hd P v
  have h := source_exactBox_to_scaleBounds hA hd₀ hC hr
    (shiftedSquareEmbeddingScaleLoss_ge_sqrt ha)
    (by simpa only [Nat.cast_mul] using hbox.1)
    (by simpa only [Nat.cast_mul] using hbox.2)
  simpa only [shiftedSquareEAlpha, Nat.cast_mul] using h

/-- Every primitive target element is polynomially comparable to
`sqrt E_gamma` at every infinite place on the large shifted-square range. -/
theorem shiftedSquare_targetEmbedding_scaleBounds
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (ha : a ≠ 0) (hd : 0 < d)
    (hn : 2 * Real.sqrt |(a : ℝ)| ≤ (n : ℝ))
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq)
    (v : NumberField.InfinitePlace (rationalQuadraticAlgebra (-a))) :
    Real.sqrt (shiftedSquareEGamma P) / shiftedSquareEmbeddingScaleLoss a ≤
        v (shiftedSquareIntegralBasisElement P.basis P.y) ∧
      v (shiftedSquareIntegralBasisElement P.basis P.y) ≤
        shiftedSquareEmbeddingScaleLoss a * Real.sqrt (shiftedSquareEGamma P) := by
  have hA : (1 : ℝ) ≤ |(a : ℝ)| := by exact_mod_cast Int.one_le_abs ha
  have hsqrtAPos : 0 < Real.sqrt |(a : ℝ)| :=
    Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one hA)
  have hnReal : (0 : ℝ) < n := (mul_pos (by norm_num) hsqrtAPos).trans_le hn
  have hd₀ : (0 : ℝ) < shiftedSquareD₀ d := by
    exact_mod_cast shiftedSquareD₀_pos hd
  have hC : (1 : ℝ) ≤ P.minkowski.C₀ := by exact_mod_cast P.minkowski.C₀_pos
  have hell : (0 : ℝ) < P.ell := by exact_mod_cast P.ell_pos
  have hscale := shiftedSquareD₀_scale_linear_comparability heq hn
  have hproductPos :
      0 < (shiftedSquareD₀ d : ℝ) * Real.sqrt (w : ℝ) := by
    nlinarith [hscale.1]
  have hsqrtWPos : 0 < Real.sqrt (w : ℝ) := by
    rcases (mul_pos_iff.mp hproductPos) with hpos | hneg
    · exact hpos.2
    · exact (not_lt_of_ge hd₀.le hneg.1).elim
  have hwReal : (0 : ℝ) < w := (Real.sqrt_pos).mp hsqrtWPos
  have hbox := shiftedSquare_targetEmbedding_twoSided hd hn P v
  have h := target_exactBox_to_scaleBounds hA hd₀ hC hell hwReal hnReal
    (shiftedSquareEmbeddingScaleLoss_ge_sqrt ha) hscale.1 hscale.2
    (by simpa only [Nat.cast_mul] using hbox.1)
    (by simpa only [Nat.cast_mul] using hbox.2)
  simpa only [shiftedSquareEGamma, Nat.cast_mul, Nat.cast_pow] using h

/-- Combined four-inequality embedding-scale package used by the determinant
route. -/
theorem shiftedSquare_primitiveEmbeddings_scaleBounds
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (ha : a ≠ 0) (hd : 0 < d)
    (hn : 2 * Real.sqrt |(a : ℝ)| ≤ (n : ℝ))
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq)
    (v : NumberField.InfinitePlace (rationalQuadraticAlgebra (-a))) :
    (Real.sqrt (shiftedSquareEAlpha P) / shiftedSquareEmbeddingScaleLoss a ≤
          v (shiftedSquareIntegralBasisElement P.basis P.x) ∧
        v (shiftedSquareIntegralBasisElement P.basis P.x) ≤
          shiftedSquareEmbeddingScaleLoss a * Real.sqrt (shiftedSquareEAlpha P)) ∧
      (Real.sqrt (shiftedSquareEGamma P) / shiftedSquareEmbeddingScaleLoss a ≤
          v (shiftedSquareIntegralBasisElement P.basis P.y) ∧
        v (shiftedSquareIntegralBasisElement P.basis P.y) ≤
          shiftedSquareEmbeddingScaleLoss a * Real.sqrt (shiftedSquareEGamma P)) :=
  ⟨shiftedSquare_sourceEmbedding_scaleBounds ha hd P v,
    shiftedSquare_targetEmbedding_scaleBounds ha hd hn P v⟩

end

end PellPaper
