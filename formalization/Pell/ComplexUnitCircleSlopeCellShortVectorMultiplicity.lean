import Pell.ComplexUnitCircleSquareMapCellPairCover
import Pell.SeparatedRealCenterCounting
import Mathlib.Tactic

/-!
# Complex slope-cell multiplicity near one target direction

On a fixed signed dominant chart, two unit-circle points cannot be nearly
antipodal.  The square map therefore does not contract chord distance there,
while the ordinary chart slope is uniformly Lipschitz.  These two elementary
facts turn proximity of squared source points to one complex target into an
explicit bound for the number of possible integer slope bins.

The final target-tube form is the geometric multiplicity input needed when a
fixed quadratic-order short vector is assigned to many complex Main3 cells.
No lattice count, shortest-vector selection, square sieve, or Weil estimate
occurs here.
-/

namespace PellPaper

noncomputable section

open scoped BigOperators ComplexConjugate

/-- Exact denominator-clearing identity for the unit complex directions
`conj a / a` and `conj b / b`. -/
theorem norm_conj_div_self_sub_conj_div_self_eq
    {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) :
    ‖conj a / a - conj b / b‖ =
      ‖conj a * b - conj b * a‖ / (‖a‖ * ‖b‖) := by
  have hid :
      conj a / a - conj b / b =
        (conj a * b - conj b * a) / (a * b) := by
    field_simp [ha, hb]
  rw [hid, norm_div, norm_mul]

/-- Two unit points in the same signed dominant chart cannot be nearly
antipodal. -/
theorem one_le_norm_add_of_mem_same_complexUnitCircleDominantChart
    {i : ComplexUnitCircleChartIndex} {z u : ℂ}
    (hi : i ∈ complexUnitCircleChartIndices)
    (hzNorm : ‖z‖ = 1) (huNorm : ‖u‖ = 1)
    (hz : InComplexUnitCircleDominantChart i z)
    (hu : InComplexUnitCircleDominantChart i u) :
    1 ≤ ‖z + u‖ := by
  have hiSign : i.2 ∈ complexUnitCircleChartSigns :=
    (Finset.mem_product.mp hi).2
  have hsign : i.2 = -1 ∨ i.2 = 1 := by
    simpa [complexUnitCircleChartSigns] using hiSign
  have hzMajor : (1 : ℝ) / 2 ≤ |complexChartMajor i.1 z| :=
    one_half_le_abs_complexChartMajor_of_norm_eq_one hzNorm hz
  have huMajor : (1 : ℝ) / 2 ≤ |complexChartMajor i.1 u| :=
    one_half_le_abs_complexChartMajor_of_norm_eq_one huNorm hu
  have hmajorAdd :
      |complexChartMajor i.1 z + complexChartMajor i.1 u| =
        |complexChartMajor i.1 z| + |complexChartMajor i.1 u| := by
    rcases hsign with hsign | hsign
    · have hzSign := hz.1
      have huSign := hu.1
      rw [hsign] at hzSign huSign
      norm_num at hzSign huSign
      rw [hzSign, huSign]
      rw [abs_of_nonpos (add_nonpos (neg_nonpos.mpr (abs_nonneg _))
        (neg_nonpos.mpr (abs_nonneg _)))]
      simp only [abs_neg, abs_abs]
      ring
    · have hzSign := hz.1
      have huSign := hu.1
      rw [hsign] at hzSign huSign
      norm_num at hzSign huSign
      rw [hzSign, huSign]
      rw [abs_of_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))]
      simp only [abs_abs]
  have hmajorNorm :
      |complexChartMajor i.1 (z + u)| ≤ ‖z + u‖ := by
    cases haxis : i.1
    · simpa only [complexChartMajor, haxis] using
        Complex.abs_re_le_norm (z + u)
    · simpa only [complexChartMajor, haxis] using
        Complex.abs_im_le_norm (z + u)
  have hmajorAddEq :
      complexChartMajor i.1 (z + u) =
        complexChartMajor i.1 z + complexChartMajor i.1 u := by
    cases i.1 <;> rfl
  calc
    (1 : ℝ) ≤ |complexChartMajor i.1 z| +
        |complexChartMajor i.1 u| := by linarith
    _ = |complexChartMajor i.1 z +
        complexChartMajor i.1 u| := hmajorAdd.symm
    _ = |complexChartMajor i.1 (z + u)| := by rw [hmajorAddEq]
    _ ≤ ‖z + u‖ := hmajorNorm

/-- On one signed chart the unit-circle square map does not contract chord
distance. -/
theorem norm_sub_le_norm_sq_sub_sq_of_mem_same_complexUnitCircleDominantChart
    {i : ComplexUnitCircleChartIndex} {z u : ℂ}
    (hi : i ∈ complexUnitCircleChartIndices)
    (hzNorm : ‖z‖ = 1) (huNorm : ‖u‖ = 1)
    (hz : InComplexUnitCircleDominantChart i z)
    (hu : InComplexUnitCircleDominantChart i u) :
    ‖z - u‖ ≤ ‖z ^ 2 - u ^ 2‖ := by
  have hadd := one_le_norm_add_of_mem_same_complexUnitCircleDominantChart
    hi hzNorm huNorm hz hu
  calc
    ‖z - u‖ = ‖z - u‖ * 1 := by ring
    _ ≤ ‖z - u‖ * ‖z + u‖ :=
      mul_le_mul_of_nonneg_left hadd (norm_nonneg _)
    _ = ‖(z - u) * (z + u)‖ := (norm_mul _ _).symm
    _ = ‖z ^ 2 - u ^ 2‖ := by congr 1; ring

/-- Ordinary slope on a dominant unit-circle chart is uniformly Lipschitz
in chord distance. -/
theorem abs_complexUnitCircleChartCoordinate_sub_le_eight_mul_norm_sub
    {i : ComplexUnitCircleChartIndex} {z u : ℂ}
    (hz : ‖z‖ = 1) (hu : ‖u‖ = 1)
    (hzChart : InComplexUnitCircleDominantChart i z)
    (huChart : InComplexUnitCircleDominantChart i u) :
    |complexUnitCircleChartCoordinate i.1 z -
        complexUnitCircleChartCoordinate i.1 u| ≤ 8 * ‖z - u‖ := by
  let A := complexChartMajor i.1 z
  let B := complexChartMinor i.1 z
  let C := complexChartMajor i.1 u
  let D := complexChartMinor i.1 u
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hz]; norm_num)
  have hu0 : u ≠ 0 := norm_ne_zero_iff.mp (by rw [hu]; norm_num)
  have hA : A ≠ 0 := by
    simpa only [A] using complexChartMajor_ne_zero_of_mem hz0 hzChart
  have hC : C ≠ 0 := by
    simpa only [C] using complexChartMajor_ne_zero_of_mem hu0 huChart
  have hAhalf : (1 : ℝ) / 2 ≤ |A| := by
    simpa only [A] using
      one_half_le_abs_complexChartMajor_of_norm_eq_one hz hzChart
  have hChalf : (1 : ℝ) / 2 ≤ |C| := by
    simpa only [C] using
      one_half_le_abs_complexChartMajor_of_norm_eq_one hu huChart
  have hden : (1 : ℝ) / 4 ≤ |A * C| := by
    rw [abs_mul]
    nlinarith [abs_nonneg A, abs_nonneg C]
  have hCOne : |C| ≤ 1 := by
    have hs := complexChartMajor_sq_add_minor_sq i.1 u
    rw [hu] at hs
    norm_num at hs
    nlinarith [sq_abs C, abs_nonneg C, sq_nonneg (complexChartMinor i.1 u)]
  have hDOne : |D| ≤ 1 := by
    have hs := complexChartMajor_sq_add_minor_sq i.1 u
    rw [hu] at hs
    norm_num at hs
    nlinarith [sq_abs D, abs_nonneg D, sq_nonneg (complexChartMajor i.1 u)]
  have hBsubD : |B - D| ≤ ‖z - u‖ := by
    cases haxis : i.1
    · simpa only [B, D, complexChartMinor, haxis, Complex.sub_im] using
        Complex.abs_im_le_norm (z - u)
    · simpa only [B, D, complexChartMinor, haxis, Complex.sub_re] using
        Complex.abs_re_le_norm (z - u)
  have hCsubA : |C - A| ≤ ‖z - u‖ := by
    cases haxis : i.1
    · simpa only [A, C, complexChartMajor, haxis, Complex.sub_re,
        abs_sub_comm] using Complex.abs_re_le_norm (z - u)
    · simpa only [A, C, complexChartMajor, haxis, Complex.sub_im,
        abs_sub_comm] using Complex.abs_im_le_norm (z - u)
  have hnum : |B * C - D * A| ≤ 2 * ‖z - u‖ := by
    rw [show B * C - D * A = (B - D) * C + D * (C - A) by ring]
    calc
      |(B - D) * C + D * (C - A)| ≤
          |(B - D) * C| + |D * (C - A)| := abs_add_le _ _
      _ = |B - D| * |C| + |D| * |C - A| := by rw [abs_mul, abs_mul]
      _ ≤ ‖z - u‖ * 1 + 1 * ‖z - u‖ := by gcongr
      _ = 2 * ‖z - u‖ := by ring
  have hcoord :
      complexUnitCircleChartCoordinate i.1 z -
          complexUnitCircleChartCoordinate i.1 u =
        (B * C - D * A) / (A * C) := by
    change B / A - D / C = (B * C - D * A) / (A * C)
    field_simp [hA, hC]
  rw [hcoord, abs_div]
  apply (div_le_iff₀ (abs_pos.mpr (mul_ne_zero hA hC))).2
  calc
    |B * C - D * A| ≤ 2 * ‖z - u‖ := hnum
    _ ≤ (8 * ‖z - u‖) * |A * C| := by
      have hnorm : 0 ≤ ‖z - u‖ := norm_nonneg _
      nlinarith

/-- If two source cells use the same signed chart and their squared source
points lie in the same `eta/M` ball, then their integer slope bins differ by
at most `16 eta + 1`. -/
theorem abs_complexUnitCircleSlopeCell_bin_sub_le_of_square_near
    {M : ℕ} (hM : 0 < M) {q : ℂ} {eta : ℝ}
    {i j : ComplexUnitCircleSlopeCellIndex}
    (hi : i ∈ complexUnitCircleSlopeCellIndices M)
    (hchart : i.1 = j.1)
    {z u : ℂ}
    (hz : InComplexUnitCircleSlopeCell M i z)
    (hu : InComplexUnitCircleSlopeCell M j u)
    (hzNear : ‖z ^ 2 - q‖ ≤ eta / (M : ℝ))
    (huNear : ‖u ^ 2 - q‖ ≤ eta / (M : ℝ)) :
    |(i.2 : ℝ) - (j.2 : ℝ)| ≤ 16 * eta + 1 := by
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  have hiChart : i.1 ∈ complexUnitCircleChartIndices :=
    (Finset.mem_product.mp hi).1
  have huChart : InComplexUnitCircleDominantChart i.1 u := by
    simpa only [hchart] using hu.2.1
  have hsquare : ‖z ^ 2 - u ^ 2‖ ≤ 2 * eta / (M : ℝ) := by
    calc
      ‖z ^ 2 - u ^ 2‖ ≤ ‖z ^ 2 - q‖ + ‖q - u ^ 2‖ := by
        calc
          ‖z ^ 2 - u ^ 2‖ = ‖(z ^ 2 - q) + (q - u ^ 2)‖ := by
            congr 1
            ring
          _ ≤ _ := norm_add_le _ _
      _ ≤ eta / (M : ℝ) + eta / (M : ℝ) := by
        gcongr
        simpa only [norm_sub_rev] using huNear
      _ = 2 * eta / (M : ℝ) := by ring
  have hsource : ‖z - u‖ ≤ 2 * eta / (M : ℝ) :=
    (norm_sub_le_norm_sq_sub_sq_of_mem_same_complexUnitCircleDominantChart
      hiChart hz.1 hu.1 hz.2.1 huChart).trans hsquare
  have hcoord :
      |complexUnitCircleChartCoordinate i.1.1 z -
          complexUnitCircleChartCoordinate i.1.1 u| ≤
        16 * eta / (M : ℝ) := by
    calc
      |complexUnitCircleChartCoordinate i.1.1 z -
          complexUnitCircleChartCoordinate i.1.1 u| ≤
          8 * ‖z - u‖ :=
        abs_complexUnitCircleChartCoordinate_sub_le_eight_mul_norm_sub
          hz.1 hu.1 hz.2.1 huChart
      _ ≤ 8 * (2 * eta / (M : ℝ)) := by gcongr
      _ = 16 * eta / (M : ℝ) := by ring
  have hscaled :
      |(M : ℝ) * complexUnitCircleChartCoordinate i.1.1 z -
          (M : ℝ) * complexUnitCircleChartCoordinate i.1.1 u| ≤
        16 * eta := by
    rw [← mul_sub, abs_mul, abs_of_pos hMreal]
    calc
      (M : ℝ) *
          |complexUnitCircleChartCoordinate i.1.1 z -
            complexUnitCircleChartCoordinate i.1.1 u| ≤
          (M : ℝ) * (16 * eta / (M : ℝ)) := by gcongr
      _ = 16 * eta := by field_simp [hMreal.ne']
  have hscaledBounds := abs_le.mp hscaled
  have huLeft :
      (j.2 : ℝ) - 1 <
        (M : ℝ) * complexUnitCircleChartCoordinate i.1.1 u := by
    simpa only [hchart] using hu.2.2.1
  have huRight :
      (M : ℝ) * complexUnitCircleChartCoordinate i.1.1 u ≤
        (j.2 : ℝ) := by
    simpa only [hchart] using hu.2.2.2
  rw [abs_le]
  constructor <;> linarith [hz.2.2.1, hz.2.2.2, huLeft, huRight]

/-- In one fixed signed chart, only `3 + 32 eta` slope bins can contain a
unit source whose square lies in a common `eta/M` ball. -/
theorem card_complexUnitCircleSlopeCells_in_chart_with_square_near_le
    (M : ℕ) (hM : 0 < M) (q : ℂ) (eta : ℝ) (heta : 0 ≤ eta)
    (J : Finset ComplexUnitCircleSlopeCellIndex)
    (hJ : J ⊆ complexUnitCircleSlopeCellIndices M)
    (hwitness : ∀ i ∈ J, ∃ z : ℂ,
      InComplexUnitCircleSlopeCell M i z ∧
        ‖z ^ 2 - q‖ ≤ eta / (M : ℝ))
    (chart : ComplexUnitCircleChartIndex) :
    (((J.filter fun i => i.1 = chart).card : ℕ) : ℝ) ≤
      3 + 32 * eta := by
  classical
  let Jchart := J.filter fun i => i.1 = chart
  by_cases hnonempty : Jchart.Nonempty
  · obtain ⟨i₀, hi₀⟩ := hnonempty
    have hi₀J : i₀ ∈ J := (Finset.mem_filter.mp hi₀).1
    have hi₀Index : i₀ ∈ complexUnitCircleSlopeCellIndices M := hJ hi₀J
    obtain ⟨z₀, hz₀Cell, hz₀Near⟩ := hwitness i₀ hi₀J
    let K : ℝ := 16 * eta + 1
    have hK : 0 ≤ K := by dsimp only [K]; positivity
    have hbounds : ∀ i ∈ Jchart,
        (i₀.2 : ℝ) - K ≤ (i.2 : ℝ) ∧
          (i.2 : ℝ) ≤ (i₀.2 : ℝ) + K := by
      intro i hi
      have hiJ : i ∈ J := (Finset.mem_filter.mp hi).1
      have hiChart : i.1 = chart := (Finset.mem_filter.mp hi).2
      have hi₀Chart : i₀.1 = chart := (Finset.mem_filter.mp hi₀).2
      have hsame : i.1 = i₀.1 := hiChart.trans hi₀Chart.symm
      have hiIndex : i ∈ complexUnitCircleSlopeCellIndices M := hJ hiJ
      obtain ⟨z, hzCell, hzNear⟩ := hwitness i hiJ
      have hbin :=
        abs_complexUnitCircleSlopeCell_bin_sub_le_of_square_near
          hM hiIndex hsame hzCell hz₀Cell hzNear hz₀Near
      have hbinBounds := abs_le.mp hbin
      dsimp only [K]
      constructor <;> linarith
    have hseparated : ∀ i ∈ Jchart, ∀ j ∈ Jchart, i ≠ j →
        (1 : ℝ) ≤ |(i.2 : ℝ) - (j.2 : ℝ)| := by
      intro i hi j hj hij
      have hiChart : i.1 = chart := (Finset.mem_filter.mp hi).2
      have hjChart : j.1 = chart := (Finset.mem_filter.mp hj).2
      have hsecond : i.2 ≠ j.2 := by
        intro heq
        apply hij
        exact Prod.ext (hiChart.trans hjChart.symm) heq
      have hdiff : i.2 - j.2 ≠ 0 := sub_ne_zero.mpr hsecond
      have hsepZ : (1 : ℤ) ≤ |i.2 - j.2| := Int.one_le_abs hdiff
      exact_mod_cast hsepZ
    have hpack := card_le_one_add_div_of_separated_real_centers
      Jchart (fun i => (i.2 : ℝ))
        ((i₀.2 : ℝ) - K) ((i₀.2 : ℝ) + K) 1
        (by norm_num) (by linarith) hbounds hseparated
    change (Jchart.card : ℝ) ≤ 3 + 32 * eta
    calc
      (Jchart.card : ℝ) ≤
          1 + (((i₀.2 : ℝ) + K) - ((i₀.2 : ℝ) - K)) / 1 := hpack
      _ = 3 + 32 * eta := by dsimp only [K]; ring
  · have hempty : Jchart = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnonempty
    change (Jchart.card : ℝ) ≤ 3 + 32 * eta
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

/-- Across all four signed charts, at most `12 + 128 eta` slope cells can
contain a unit source whose square lies in a fixed `eta/M` ball.  The result
is overlap-safe: a geometric source may occur in several charts. -/
theorem card_complexUnitCircleSlopeCells_with_square_near_le
    (M : ℕ) (hM : 0 < M) (q : ℂ) (eta : ℝ) (heta : 0 ≤ eta)
    (J : Finset ComplexUnitCircleSlopeCellIndex)
    (hJ : J ⊆ complexUnitCircleSlopeCellIndices M)
    (hwitness : ∀ i ∈ J, ∃ z : ℂ,
      InComplexUnitCircleSlopeCell M i z ∧
        ‖z ^ 2 - q‖ ≤ eta / (M : ℝ)) :
    (J.card : ℝ) ≤ 12 + 128 * eta := by
  classical
  have hmap : ∀ i ∈ J, i.1 ∈ complexUnitCircleChartIndices := by
    intro i hi
    exact (Finset.mem_product.mp (hJ hi)).1
  have hcardNat : J.card =
      ∑ chart ∈ complexUnitCircleChartIndices,
        (J.filter fun i => i.1 = chart).card :=
    Finset.card_eq_sum_card_fiberwise hmap
  have hcardReal : (J.card : ℝ) =
      ∑ chart ∈ complexUnitCircleChartIndices,
        (((J.filter fun i => i.1 = chart).card : ℕ) : ℝ) := by
    exact_mod_cast hcardNat
  rw [hcardReal]
  calc
    (∑ chart ∈ complexUnitCircleChartIndices,
        (((J.filter fun i => i.1 = chart).card : ℕ) : ℝ)) ≤
        ∑ _chart ∈ complexUnitCircleChartIndices, (3 + 32 * eta) := by
      apply Finset.sum_le_sum
      intro chart hchart
      exact card_complexUnitCircleSlopeCells_in_chart_with_square_near_le
        M hM q eta heta J hJ hwitness chart
    _ = 12 + 128 * eta := by
      simp only [Finset.sum_const, nsmul_eq_mul,
        card_complexUnitCircleChartIndices]
      ring

/-- Target-tube form of the four-chart multiplicity estimate.  If every
selected cell contains a target-tube point within `delta/M` of one fixed
complex number, then there are at most `140 + 128 delta` selected cells. -/
theorem card_complexUnitCircleSlopeCells_with_target_near_le
    (M : ℕ) (hM : 0 < M) (q : ℂ) (delta : ℝ) (hdelta : 0 ≤ delta)
    (J : Finset ComplexUnitCircleSlopeCellIndex)
    (hJ : J ⊆ complexUnitCircleSlopeCellIndices M)
    (hwitness : ∀ i ∈ J, ∃ w : ℂ,
      InComplexUnitCircleSquareTargetTube M i w ∧
        ‖w - q‖ ≤ delta / (M : ℝ)) :
    (J.card : ℝ) ≤ 140 + 128 * delta := by
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  have hsource : ∀ i ∈ J, ∃ z : ℂ,
      InComplexUnitCircleSlopeCell M i z ∧
        ‖z ^ 2 - q‖ ≤ (delta + 1) / (M : ℝ) := by
    intro i hi
    obtain ⟨w, hwTube, hwNear⟩ := hwitness i hi
    obtain ⟨z, hzCell, hwz⟩ := hwTube.2
    refine ⟨z, hzCell, ?_⟩
    calc
      ‖z ^ 2 - q‖ ≤ ‖z ^ 2 - w‖ + ‖w - q‖ := by
        calc
          ‖z ^ 2 - q‖ = ‖(z ^ 2 - w) + (w - q)‖ := by
            congr 1
            ring
          _ ≤ _ := norm_add_le _ _
      _ ≤ 1 / (M : ℝ) + delta / (M : ℝ) := by
        gcongr
        simpa only [norm_sub_rev] using hwz
      _ = (delta + 1) / (M : ℝ) := by ring
  have hcount := card_complexUnitCircleSlopeCells_with_square_near_le
    M hM q (delta + 1) (by positivity) J hJ hsource
  calc
    (J.card : ℝ) ≤ 12 + 128 * (delta + 1) := hcount
    _ = 140 + 128 * delta := by ring

end

end PellPaper
