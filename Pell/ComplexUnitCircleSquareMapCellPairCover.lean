import Pell.ComplexUnitCircleDominantChart
import Pell.Main3ShiftedSquareEmbeddingRatioLocalization
import Mathlib.Tactic

/-!
# A finite complex unit-circle square-map cover

After the separate four-chart selection, this module divides the ordinary
slope in each dominant-coordinate chart into intervals of width `1/M`.
There are exactly `4 * (2*M+1)` source indices.  A target tube attached to a
source cell consists of unit complex numbers within `1/M` of the square of
some source point in that cell.

The source cells have Euclidean diameter at most `2/M`; consequently every
target in the tube is within `5/M` of the square of every source in the cell,
and each target tube has diameter at most `6/M`.  These are literal geometric
statements.  No determinant estimate or arithmetic point count is asserted.
-/

namespace PellPaper

noncomputable section

open scoped BigOperators

/-- The symmetric integer slope bins for a mesh of width `1/M`. -/
def complexUnitCircleSlopeBins (M : ℕ) : Finset ℤ :=
  Finset.Icc (-(M : ℤ)) (M : ℤ)

/-- A four-chart index together with one ordinary-slope bin. -/
abbrev ComplexUnitCircleSlopeCellIndex := ComplexUnitCircleChartIndex × ℤ

/-- The literal finite family of chart/slope indices. -/
def complexUnitCircleSlopeCellIndices (M : ℕ) :
    Finset ComplexUnitCircleSlopeCellIndex :=
  complexUnitCircleChartIndices.product (complexUnitCircleSlopeBins M)

/-- The right-endpoint slope index in a fixed dominant chart. -/
def complexUnitCircleSlopeRightIndex
    (M : ℕ) (axis : ComplexCoordinateAxis) (z : ℂ) : ℤ :=
  ⌈(M : ℝ) * complexUnitCircleChartCoordinate axis z⌉

/-- A unit-circle point lies in this slope cell when it lies in the selected
dominant chart and its scaled ordinary slope has the displayed half-open
right-endpoint interval. -/
def InComplexUnitCircleSlopeCell
    (M : ℕ) (i : ComplexUnitCircleSlopeCellIndex) (z : ℂ) : Prop :=
  ‖z‖ = 1 ∧ InComplexUnitCircleDominantChart i.1 z ∧
    (i.2 : ℝ) - 1 <
        (M : ℝ) * complexUnitCircleChartCoordinate i.1.1 z ∧
      (M : ℝ) * complexUnitCircleChartCoordinate i.1.1 z ≤ (i.2 : ℝ)

/-- The target tube attached to a source slope cell.  It is independent of
the subsequently chosen source point: membership only asks for some unit
source witness in the fixed cell. -/
def InComplexUnitCircleSquareTargetTube
    (M : ℕ) (i : ComplexUnitCircleSlopeCellIndex) (w : ℂ) : Prop :=
  ‖w‖ = 1 ∧ ∃ z : ℂ,
    InComplexUnitCircleSlopeCell M i z ∧ ‖w - z ^ 2‖ ≤ 1 / (M : ℝ)

/-- A product-like source/target cell pair: the source lies in the fixed
slope cell and the target lies in its fixed square tube. -/
def InComplexUnitCircleSquareMapCellPair
    (M : ℕ) (i : ComplexUnitCircleSlopeCellIndex) (p : ℂ × ℂ) : Prop :=
  InComplexUnitCircleSlopeCell M i p.1 ∧
    InComplexUnitCircleSquareTargetTube M i p.2

/-- The portion of a finite complex-pair family in one literal cell pair. -/
noncomputable def complexUnitCircleSquareMapCellPair
    (S : Finset (ℂ × ℂ)) (M : ℕ) (i : ComplexUnitCircleSlopeCellIndex) :
    Finset (ℂ × ℂ) := by
  classical
  exact S.filter (InComplexUnitCircleSquareMapCellPair M i)

@[simp]
theorem card_complexUnitCircleSlopeBins (M : ℕ) :
    (complexUnitCircleSlopeBins M).card = 2 * M + 1 := by
  rw [complexUnitCircleSlopeBins, Int.card_Icc]
  rw [show (M : ℤ) + 1 - -(M : ℤ) = 2 * (M : ℤ) + 1 by ring]
  omega

/-- Exact linear index count for the four-chart slope mesh. -/
@[simp]
theorem card_complexUnitCircleSlopeCellIndices (M : ℕ) :
    (complexUnitCircleSlopeCellIndices M).card = 4 * (2 * M + 1) := by
  simp [complexUnitCircleSlopeCellIndices]

/-- Index membership is exactly chart membership and the symmetric integral
slope-bin range. -/
theorem mem_complexUnitCircleSlopeCellIndices
    {M : ℕ} {i : ComplexUnitCircleSlopeCellIndex} :
    i ∈ complexUnitCircleSlopeCellIndices M ↔
      i.1 ∈ complexUnitCircleChartIndices ∧
        -(M : ℤ) ≤ i.2 ∧ i.2 ≤ (M : ℤ) := by
  simp [complexUnitCircleSlopeCellIndices, complexUnitCircleSlopeBins]

/-- Two unit-circle points in the same signed dominant chart are controlled
in Euclidean distance by twice the difference of their ordinary slopes. -/
theorem norm_sub_le_two_mul_abs_chartCoordinate_sub
    {i : ComplexUnitCircleChartIndex} {z u : ℂ}
    (hi : i ∈ complexUnitCircleChartIndices)
    (hzNorm : ‖z‖ = 1) (huNorm : ‖u‖ = 1)
    (hzChart : InComplexUnitCircleDominantChart i z)
    (huChart : InComplexUnitCircleDominantChart i u) :
    ‖z - u‖ ≤ 2 *
      |complexUnitCircleChartCoordinate i.1 z -
        complexUnitCircleChartCoordinate i.1 u| := by
  let A : ℝ := complexChartMajor i.1 z
  let B : ℝ := complexChartMinor i.1 z
  let C : ℝ := complexChartMajor i.1 u
  let D : ℝ := complexChartMinor i.1 u
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hzNorm]; norm_num)
  have hu0 : u ≠ 0 := norm_ne_zero_iff.mp (by rw [huNorm]; norm_num)
  have hA : A ≠ 0 := by
    simpa only [A] using complexChartMajor_ne_zero_of_mem hz0 hzChart
  have hC : C ≠ 0 := by
    simpa only [C] using complexChartMajor_ne_zero_of_mem hu0 huChart
  have hzUnit : A ^ 2 + B ^ 2 = 1 := by
    dsimp only [A, B]
    rw [complexChartMajor_sq_add_minor_sq, hzNorm]
    norm_num
  have huUnit : C ^ 2 + D ^ 2 = 1 := by
    dsimp only [C, D]
    rw [complexChartMajor_sq_add_minor_sq, huNorm]
    norm_num
  have hsign : i.2 ∈ complexUnitCircleChartSigns :=
    (Finset.mem_product.mp hi).2
  have hACeq : A * C = |A| * |C| := by
    have hzSign : A = (i.2 : ℝ) * |A| := by
      simpa only [A] using hzChart.1
    have huSign : C = (i.2 : ℝ) * |C| := by
      simpa only [C] using huChart.1
    have heps : i.2 = -1 ∨ i.2 = 1 := by
      simpa [complexUnitCircleChartSigns] using hsign
    rcases heps with heps | heps
    · rw [heps] at hzSign huSign
      norm_num at hzSign huSign
      calc
        A * C = (-|A|) * (-|C|) := congrArg₂ (· * ·) hzSign huSign
        _ = |A| * |C| := by ring
    · rw [heps] at hzSign huSign
      norm_num at hzSign huSign
      exact congrArg₂ (· * ·) hzSign huSign
  have hBDabs : |B * D| ≤ |A| * |C| := by
    rw [abs_mul]
    exact mul_le_mul hzChart.2 huChart.2 (abs_nonneg D) (abs_nonneg A)
  have hdotNonneg : 0 ≤ A * C + B * D := by
    have hneg : -(A * C) ≤ B * D := by
      calc
        -(A * C) = -(|A| * |C|) := by rw [hACeq]
        _ ≤ -|B * D| := neg_le_neg hBDabs
        _ ≤ B * D := neg_abs_le (B * D)
    linarith
  have hAabs : |A| ≤ 1 := by
    nlinarith [sq_nonneg B, sq_abs A, abs_nonneg A]
  have hCabs : |C| ≤ 1 := by
    nlinarith [sq_nonneg D, sq_abs C, abs_nonneg C]
  have hACabs : |A * C| ≤ 1 := by
    rw [abs_mul]
    nlinarith [mul_nonneg (abs_nonneg A) (abs_nonneg C)]
  have hdet : B * C - D * A = A * C *
      (complexUnitCircleChartCoordinate i.1 z -
        complexUnitCircleChartCoordinate i.1 u) := by
    have hzCoord : complexUnitCircleChartCoordinate i.1 z = B / A := rfl
    have huCoord : complexUnitCircleChartCoordinate i.1 u = D / C := rfl
    rw [hzCoord, huCoord]
    field_simp [hA, hC]
  have hdetAbs : |B * C - D * A| ≤
      |complexUnitCircleChartCoordinate i.1 z -
        complexUnitCircleChartCoordinate i.1 u| := by
    rw [hdet, abs_mul]
    exact (mul_le_mul_of_nonneg_right hACabs (abs_nonneg _)).trans_eq
      (one_mul _)
  have hidentity :
      (A * C + B * D) ^ 2 + (B * C - D * A) ^ 2 = 1 := by
    calc
      (A * C + B * D) ^ 2 + (B * C - D * A) ^ 2 =
          (A ^ 2 + B ^ 2) * (C ^ 2 + D ^ 2) := by ring
      _ = 1 := by rw [hzUnit, huUnit]; norm_num
  have hdotLe : A * C + B * D ≤ 1 := by
    nlinarith [sq_nonneg (B * C - D * A)]
  have honeMinus : 1 - (A * C + B * D) ≤ (B * C - D * A) ^ 2 := by
    have hprod : 0 ≤
        (1 - (A * C + B * D)) * (A * C + B * D) :=
      mul_nonneg (sub_nonneg.mpr hdotLe) hdotNonneg
    nlinarith
  have hdetSq : (B * C - D * A) ^ 2 ≤
      |complexUnitCircleChartCoordinate i.1 z -
        complexUnitCircleChartCoordinate i.1 u| ^ 2 := by
    simpa only [sq_abs] using
      (pow_le_pow_left₀ (abs_nonneg (B * C - D * A)) hdetAbs 2)
  have hnormSq : ‖z - u‖ ^ 2 ≤
      (2 * |complexUnitCircleChartCoordinate i.1 z -
        complexUnitCircleChartCoordinate i.1 u|) ^ 2 := by
    have hcoordinate :
        ‖z - u‖ ^ 2 = (A - C) ^ 2 + (B - D) ^ 2 := by
      dsimp only [A, B, C, D]
      rw [Complex.sq_norm, Complex.normSq_apply]
      cases i.1 <;>
        simp only [complexChartMajor, complexChartMinor, Complex.sub_re,
          Complex.sub_im] <;> ring
    rw [hcoordinate]
    have hchord : (A - C) ^ 2 + (B - D) ^ 2 =
        2 * (1 - (A * C + B * D)) := by nlinarith
    rw [hchord]
    nlinarith
  exact (sq_le_sq₀ (norm_nonneg (z - u)) (by positivity)).mp hnormSq

/-- The ceiling-selected slope bin is in the literal symmetric range and
contains the given unit-circle point. -/
theorem complexUnitCircleSlopeRightIndex_mem
    {M : ℕ} (hM : 0 < M) {i : ComplexUnitCircleChartIndex} {z : ℂ}
    (hi : i ∈ complexUnitCircleChartIndices) (hzNorm : ‖z‖ = 1)
    (hzChart : InComplexUnitCircleDominantChart i z) :
    (i, complexUnitCircleSlopeRightIndex M i.1 z) ∈
        complexUnitCircleSlopeCellIndices M ∧
      InComplexUnitCircleSlopeCell M
        (i, complexUnitCircleSlopeRightIndex M i.1 z) z := by
  let t : ℝ := complexUnitCircleChartCoordinate i.1 z
  let k : ℤ := complexUnitCircleSlopeRightIndex M i.1 z
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hzNorm]; norm_num)
  have htAbs : |t| ≤ 1 := by
    simpa only [t] using
      abs_complexUnitCircleChartCoordinate_le_one hz0 hzChart
  have htBounds : -1 ≤ t ∧ t ≤ 1 := abs_le.mp htAbs
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  have hscaledLower : -(M : ℝ) ≤ (M : ℝ) * t := by
    nlinarith
  have hscaledUpper : (M : ℝ) * t ≤ (M : ℝ) := by
    nlinarith
  have hkLowerReal : -(M : ℝ) ≤ (k : ℝ) := by
    exact hscaledLower.trans (by
      simpa only [k, complexUnitCircleSlopeRightIndex, t] using
        Int.le_ceil ((M : ℝ) * t))
  have hkLower : -(M : ℤ) ≤ k := by exact_mod_cast hkLowerReal
  have hkUpper : k ≤ (M : ℤ) := by
    dsimp only [k, complexUnitCircleSlopeRightIndex]
    exact Int.ceil_le.mpr
      (by simpa only [t, Int.cast_natCast] using hscaledUpper)
  have hkMem : k ∈ complexUnitCircleSlopeBins M :=
    Finset.mem_Icc.mpr ⟨hkLower, hkUpper⟩
  have hleft : (k : ℝ) - 1 < (M : ℝ) * t := by
    have hceil := Int.ceil_lt_add_one ((M : ℝ) * t)
    change (k : ℝ) < (M : ℝ) * t + 1 at hceil
    linarith
  have hright : (M : ℝ) * t ≤ (k : ℝ) := by
    have hceil := Int.le_ceil ((M : ℝ) * t)
    change (M : ℝ) * t ≤ (k : ℝ) at hceil
    exact hceil
  constructor
  · exact Finset.mem_product.mpr ⟨hi, hkMem⟩
  · exact ⟨hzNorm, hzChart, by simpa only [t, k] using hleft,
      by simpa only [t, k] using hright⟩

/-- Every unit complex number belongs to one literal chart/slope cell. -/
theorem exists_mem_complexUnitCircleSlopeCell
    {M : ℕ} (hM : 0 < M) {z : ℂ} (hzNorm : ‖z‖ = 1) :
    ∃ i ∈ complexUnitCircleSlopeCellIndices M,
      InComplexUnitCircleSlopeCell M i z := by
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hzNorm]; norm_num)
  obtain ⟨chart, hchart, hzChart⟩ :=
    exists_mem_complexUnitCircleDominantChart hz0
  refine ⟨(chart, complexUnitCircleSlopeRightIndex M chart.1 z), ?_, ?_⟩
  · exact (complexUnitCircleSlopeRightIndex_mem hM hchart hzNorm hzChart).1
  · exact (complexUnitCircleSlopeRightIndex_mem hM hchart hzNorm hzChart).2

/-- A source slope cell has Euclidean diameter at most `2/M`. -/
theorem norm_sub_le_two_div_of_mem_complexUnitCircleSlopeCell
    {M : ℕ} (hM : 0 < M) {i : ComplexUnitCircleSlopeCellIndex}
    (hi : i ∈ complexUnitCircleSlopeCellIndices M) {z u : ℂ}
    (hz : InComplexUnitCircleSlopeCell M i z)
    (hu : InComplexUnitCircleSlopeCell M i u) :
    ‖z - u‖ ≤ 2 / (M : ℝ) := by
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  have hcoord :
      |complexUnitCircleChartCoordinate i.1.1 z -
        complexUnitCircleChartCoordinate i.1.1 u| ≤ 1 / (M : ℝ) := by
    rw [abs_le]
    constructor
    · rw [show -(1 / (M : ℝ)) = (-1 : ℝ) / (M : ℝ) by ring]
      apply (div_le_iff₀ hMreal).2
      nlinarith [hz.2.2.1, hu.2.2.2]
    · apply (le_div_iff₀ hMreal).2
      nlinarith [hu.2.2.1, hz.2.2.2]
  calc
    ‖z - u‖ ≤ 2 *
        |complexUnitCircleChartCoordinate i.1.1 z -
          complexUnitCircleChartCoordinate i.1.1 u| :=
      norm_sub_le_two_mul_abs_chartCoordinate_sub
        (Finset.mem_product.mp hi).1 hz.1 hu.1 hz.2.1 hu.2.1
    _ ≤ 2 * (1 / (M : ℝ)) :=
      mul_le_mul_of_nonneg_left hcoord (by norm_num)
    _ = 2 / (M : ℝ) := by ring

/-- Squaring is `2`-Lipschitz between unit complex numbers. -/
theorem norm_sq_sub_sq_le_two_mul_norm_sub
    {z u : ℂ} (hzNorm : ‖z‖ = 1) (huNorm : ‖u‖ = 1) :
    ‖z ^ 2 - u ^ 2‖ ≤ 2 * ‖z - u‖ := by
  rw [show z ^ 2 - u ^ 2 = (z - u) * (z + u) by ring, norm_mul]
  have hsum : ‖z + u‖ ≤ 2 := by
    calc
      ‖z + u‖ ≤ ‖z‖ + ‖u‖ := norm_add_le z u
      _ = 2 := by rw [hzNorm, huNorm]; norm_num
  simpa only [mul_comm] using
    mul_le_mul_of_nonneg_left hsum (norm_nonneg (z - u))

/-- On the unit circle, the invariant quotient error is exactly an additive
target-versus-source-square error; no annular scale loss is needed. -/
theorem norm_target_sub_source_sq_le_of_unit_quotientError
    {z w : ℂ} (hzNorm : ‖z‖ = 1)
    {δ : ℝ} (herror : ‖z⁻¹ ^ 2 * w - 1‖ ≤ δ) :
    ‖w - z ^ 2‖ ≤ δ := by
  have hz : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hzNorm]; norm_num)
  have hrearrange :
      w - z ^ 2 = z ^ 2 * (z⁻¹ ^ 2 * w - 1) := by
    field_simp [hz]
  rw [hrearrange, norm_mul, norm_pow, hzNorm]
  norm_num
  simpa only [inv_pow] using herror

/-- Every target in a fixed tube is within `5/M` of the square of every
source in the corresponding source cell. -/
theorem norm_target_sub_source_sq_le_five_div_of_mem
    {M : ℕ} (hM : 0 < M) {i : ComplexUnitCircleSlopeCellIndex}
    (hi : i ∈ complexUnitCircleSlopeCellIndices M) {z w : ℂ}
    (hz : InComplexUnitCircleSlopeCell M i z)
    (hw : InComplexUnitCircleSquareTargetTube M i w) :
    ‖w - z ^ 2‖ ≤ 5 / (M : ℝ) := by
  obtain ⟨u, hu, hwu⟩ := hw.2
  have hzu := norm_sub_le_two_div_of_mem_complexUnitCircleSlopeCell
    hM hi hz hu
  have hsq := norm_sq_sub_sq_le_two_mul_norm_sub hu.1 hz.1
  have htriangle : ‖w - z ^ 2‖ ≤ ‖w - u ^ 2‖ + ‖u ^ 2 - z ^ 2‖ := by
    calc
      ‖w - z ^ 2‖ = ‖(w - u ^ 2) + (u ^ 2 - z ^ 2)‖ := by
        congr 1
        ring
      _ ≤ ‖w - u ^ 2‖ + ‖u ^ 2 - z ^ 2‖ :=
        norm_add_le (w - u ^ 2) (u ^ 2 - z ^ 2)
  calc
    ‖w - z ^ 2‖ ≤ ‖w - u ^ 2‖ + ‖u ^ 2 - z ^ 2‖ := htriangle
    _ ≤ 1 / (M : ℝ) + 2 * ‖u - z‖ :=
      add_le_add hwu hsq
    _ ≤ 1 / (M : ℝ) + 2 * (2 / (M : ℝ)) := by
      gcongr
      simpa [norm_sub_rev] using hzu
    _ = 5 / (M : ℝ) := by ring

/-- Each fixed target tube has Euclidean diameter at most `6/M`. -/
theorem norm_sub_le_six_div_of_mem_complexUnitCircleSquareTargetTube
    {M : ℕ} (hM : 0 < M) {i : ComplexUnitCircleSlopeCellIndex}
    (hi : i ∈ complexUnitCircleSlopeCellIndices M) {w₁ w₂ : ℂ}
    (hw₁ : InComplexUnitCircleSquareTargetTube M i w₁)
    (hw₂ : InComplexUnitCircleSquareTargetTube M i w₂) :
    ‖w₁ - w₂‖ ≤ 6 / (M : ℝ) := by
  obtain ⟨z₁, hz₁, hwz₁⟩ := hw₁.2
  obtain ⟨z₂, hz₂, hwz₂⟩ := hw₂.2
  have hzdist := norm_sub_le_two_div_of_mem_complexUnitCircleSlopeCell
    hM hi hz₁ hz₂
  have hsq := norm_sq_sub_sq_le_two_mul_norm_sub hz₁.1 hz₂.1
  have htriangle : ‖w₁ - w₂‖ ≤
      ‖w₁ - z₁ ^ 2‖ + ‖z₁ ^ 2 - z₂ ^ 2‖ + ‖z₂ ^ 2 - w₂‖ := by
    calc
      ‖w₁ - w₂‖ = ‖(w₁ - z₁ ^ 2) + (z₁ ^ 2 - z₂ ^ 2) +
          (z₂ ^ 2 - w₂)‖ := by
        congr 1
        ring
      _ ≤ ‖w₁ - z₁ ^ 2‖ + ‖z₁ ^ 2 - z₂ ^ 2‖ +
          ‖z₂ ^ 2 - w₂‖ := norm_add₃_le
  calc
    ‖w₁ - w₂‖ ≤
        ‖w₁ - z₁ ^ 2‖ + ‖z₁ ^ 2 - z₂ ^ 2‖ + ‖z₂ ^ 2 - w₂‖ := htriangle
    _ ≤ 1 / (M : ℝ) + 2 * ‖z₁ - z₂‖ + 1 / (M : ℝ) := by
      have hwz₂' : ‖z₂ ^ 2 - w₂‖ ≤ 1 / (M : ℝ) := by
        simpa only [norm_sub_rev] using hwz₂
      gcongr
    _ ≤ 1 / (M : ℝ) + 2 * (2 / (M : ℝ)) + 1 / (M : ℝ) := by
      gcongr
    _ = 6 / (M : ℝ) := by ring

/-- Pointwise cover of a perturbed unit-circle square map by the linear-size
family of product-like source/target cell pairs. -/
theorem exists_mem_complexUnitCircleSquareMapCellPair
    {M : ℕ} (hM : 0 < M) {z w : ℂ}
    (hzNorm : ‖z‖ = 1) (hwNorm : ‖w‖ = 1)
    (herror : ‖w - z ^ 2‖ ≤ 1 / (M : ℝ)) :
    ∃ i ∈ complexUnitCircleSlopeCellIndices M,
      InComplexUnitCircleSquareMapCellPair M i (z, w) := by
  obtain ⟨i, hi, hz⟩ := exists_mem_complexUnitCircleSlopeCell hM hzNorm
  refine ⟨i, hi, hz, hwNorm, z, hz, herror⟩

/-- Membership in a literal finite-family cell retains ambient membership
and both fixed-cell predicates. -/
theorem mem_complexUnitCircleSquareMapCellPair
    {S : Finset (ℂ × ℂ)} {M : ℕ} {i : ComplexUnitCircleSlopeCellIndex}
    {p : ℂ × ℂ} (hp : p ∈ complexUnitCircleSquareMapCellPair S M i) :
    p ∈ S ∧ InComplexUnitCircleSquareMapCellPair M i p := by
  classical
  simpa only [complexUnitCircleSquareMapCellPair] using Finset.mem_filter.mp hp

/-- Literal cell membership supplies both fixed-cell predicates and the
uniform `5/M` compatibility of its own target with its own source square. -/
theorem complexUnitCircleSquareMapCellPair_commonGeometry
    {S : Finset (ℂ × ℂ)} {M : ℕ} (hM : 0 < M)
    {i : ComplexUnitCircleSlopeCellIndex}
    (hi : i ∈ complexUnitCircleSlopeCellIndices M) {p : ℂ × ℂ}
    (hp : p ∈ complexUnitCircleSquareMapCellPair S M i) :
    InComplexUnitCircleSlopeCell M i p.1 ∧
      InComplexUnitCircleSquareTargetTube M i p.2 ∧
        ‖p.2 - p.1 ^ 2‖ ≤ 5 / (M : ℝ) := by
  have hcell := (mem_complexUnitCircleSquareMapCellPair hp).2
  exact ⟨hcell.1, hcell.2,
    norm_target_sub_source_sq_le_five_div_of_mem hM hi hcell.1 hcell.2⟩

/-- A finite family of perturbed unit-circle square-map pairs is covered by
the literal linear-size cell family. -/
theorem complexUnitCircleSquareMapPairFinset_subset_biUnion_cells
    (S : Finset (ℂ × ℂ)) {M : ℕ} (hM : 0 < M)
    (hS : ∀ p ∈ S,
      ‖p.1‖ = 1 ∧ ‖p.2‖ = 1 ∧ ‖p.2 - p.1 ^ 2‖ ≤ 1 / (M : ℝ)) :
    S ⊆ (complexUnitCircleSlopeCellIndices M).biUnion
      (complexUnitCircleSquareMapCellPair S M) := by
  intro p hp
  obtain ⟨hzNorm, hwNorm, herror⟩ := hS p hp
  obtain ⟨i, hi, hcell⟩ :=
    exists_mem_complexUnitCircleSquareMapCellPair hM hzNorm hwNorm herror
  apply Finset.mem_biUnion.mpr
  refine ⟨i, hi, ?_⟩
  classical
  simpa only [complexUnitCircleSquareMapCellPair] using
    (Finset.mem_filter.mpr ⟨hp, hcell⟩)

/-- Overlap-safe cardinality consequence of the finite complex cell cover. -/
theorem card_complexUnitCircleSquareMapPairFinset_le_sum_card_cells
    (S : Finset (ℂ × ℂ)) {M : ℕ} (hM : 0 < M)
    (hS : ∀ p ∈ S,
      ‖p.1‖ = 1 ∧ ‖p.2‖ = 1 ∧ ‖p.2 - p.1 ^ 2‖ ≤ 1 / (M : ℝ)) :
    S.card ≤ ∑ i ∈ complexUnitCircleSlopeCellIndices M,
      (complexUnitCircleSquareMapCellPair S M i).card := by
  exact (Finset.card_le_card
    (complexUnitCircleSquareMapPairFinset_subset_biUnion_cells S hM hS)).trans
      Finset.card_biUnion_le

/-- Project adapter: a shifted-square ratio localization certificate with
unit-circle source and target norms enters the finite complex cover as soon
as its explicit error is at most the mesh width. -/
theorem exists_mem_complexUnitCircleSquareMapCellPair_of_shiftedSquare
    {a : ℤ} {d w n M : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (hM : 0 < M)
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ)
    (L : ShiftedSquareEmbeddingRatioLocalizationCertificate heq P sigma)
    (hsourceNorm : ‖shiftedSquareSourceEmbeddingRatio P sigma‖ = 1)
    (htargetNorm : ‖shiftedSquareTargetEmbeddingRatio P sigma‖ = 1)
    (hsmall : (8 * Real.sqrt |(a : ℝ)|) / (n : ℝ) ≤
        1 / (M : ℝ)) :
    ∃ i ∈ complexUnitCircleSlopeCellIndices M,
      InComplexUnitCircleSquareMapCellPair M i
        (shiftedSquareSourceEmbeddingRatio P sigma,
          shiftedSquareTargetEmbeddingRatio P sigma) := by
  apply exists_mem_complexUnitCircleSquareMapCellPair hM hsourceNorm htargetNorm
  exact (norm_target_sub_source_sq_le_of_unit_quotientError
    hsourceNorm L.quotient_error).trans hsmall

/-- Denominator-free project adapter with the manuscript-scale smallness
condition `8 M sqrt |a| ≤ n`. -/
theorem exists_mem_complexUnitCircleSquareMapCellPair_of_shiftedSquare_scale
    {a : ℤ} {d w n M : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (hM : 0 < M) (hn : 0 < n)
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ)
    (L : ShiftedSquareEmbeddingRatioLocalizationCertificate heq P sigma)
    (hsourceNorm : ‖shiftedSquareSourceEmbeddingRatio P sigma‖ = 1)
    (htargetNorm : ‖shiftedSquareTargetEmbeddingRatio P sigma‖ = 1)
    (hscale : 8 * (M : ℝ) * Real.sqrt |(a : ℝ)| ≤ (n : ℝ)) :
    ∃ i ∈ complexUnitCircleSlopeCellIndices M,
      InComplexUnitCircleSquareMapCellPair M i
        (shiftedSquareSourceEmbeddingRatio P sigma,
          shiftedSquareTargetEmbeddingRatio P sigma) := by
  apply exists_mem_complexUnitCircleSquareMapCellPair_of_shiftedSquare
    hM P sigma L hsourceNorm htargetNorm
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  apply (div_le_div_iff₀ hnreal hMreal).2
  simpa only [one_mul] using (by
    calc
      8 * Real.sqrt |(a : ℝ)| * (M : ℝ) =
          8 * (M : ℝ) * Real.sqrt |(a : ℝ)| := by ring
      _ ≤ (n : ℝ) := hscale)

end

end PellPaper
