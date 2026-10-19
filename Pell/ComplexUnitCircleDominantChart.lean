import Mathlib.Tactic

/-!
# Four dominant-coordinate charts on the complex unit circle

This module gives a literal four-chart cover of the complex unit circle.
Each chart chooses the real or imaginary coordinate as denominator, records
its sign, and requires the complementary coordinate to have no larger
absolute value.  On every selected chart the denominator has absolute value
at least `1/2`, and the ordinary slope has absolute value at most one.

The constants are deliberately coarse but absolute.  This is only the chart
selection needed before an angular mesh; it defines no mesh, square-map
compatibility, determinant estimate, or arithmetic count.
-/

namespace PellPaper

noncomputable section

/-- Which Cartesian coordinate is used as the chart denominator. -/
inductive ComplexCoordinateAxis
  | real
  | imaginary
  deriving DecidableEq

/-- The denominator coordinate of a Cartesian chart. -/
def complexChartMajor (axis : ComplexCoordinateAxis) (z : ℂ) : ℝ :=
  match axis with
  | .real => z.re
  | .imaginary => z.im

/-- The complementary numerator coordinate of a Cartesian chart. -/
def complexChartMinor (axis : ComplexCoordinateAxis) (z : ℂ) : ℝ :=
  match axis with
  | .real => z.im
  | .imaginary => z.re

/-- The two literal denominator signs. -/
def complexUnitCircleChartSigns : Finset ℤ := {-1, 1}

/-- A dominant-coordinate chart is an axis together with its denominator
sign. -/
abbrev ComplexUnitCircleChartIndex := ComplexCoordinateAxis × ℤ

/-- The four literal chart indices. -/
def complexUnitCircleChartIndices : Finset ComplexUnitCircleChartIndex :=
  ({.real, .imaginary} : Finset ComplexCoordinateAxis).product
    complexUnitCircleChartSigns

/-- Pointwise membership in a dominant-coordinate chart. -/
def InComplexUnitCircleDominantChart
    (i : ComplexUnitCircleChartIndex) (z : ℂ) : Prop :=
  complexChartMajor i.1 z = (i.2 : ℝ) * |complexChartMajor i.1 z| ∧
    |complexChartMinor i.1 z| ≤ |complexChartMajor i.1 z|

/-- The ordinary slope on a dominant-coordinate chart. -/
def complexUnitCircleChartCoordinate
    (axis : ComplexCoordinateAxis) (z : ℂ) : ℝ :=
  complexChartMinor axis z / complexChartMajor axis z

/-- The portion of a finite complex family lying in one chart. -/
noncomputable def complexUnitCircleDominantChart
    (S : Finset ℂ) (i : ComplexUnitCircleChartIndex) : Finset ℂ := by
  classical
  exact S.filter (InComplexUnitCircleDominantChart i)

@[simp]
theorem card_complexUnitCircleChartSigns :
    complexUnitCircleChartSigns.card = 2 := by
  norm_num [complexUnitCircleChartSigns]

@[simp]
theorem card_complexUnitCircleChartIndices :
    complexUnitCircleChartIndices.card = 4 := by
  decide

/-- The two chart coordinates preserve the Euclidean norm square. -/
theorem complexChartMajor_sq_add_minor_sq
    (axis : ComplexCoordinateAxis) (z : ℂ) :
    complexChartMajor axis z ^ 2 + complexChartMinor axis z ^ 2 = ‖z‖ ^ 2 := by
  cases axis <;>
    simp only [complexChartMajor, complexChartMinor] <;>
    rw [Complex.sq_norm, Complex.normSq_apply] <;>
    ring

private theorem exists_complexUnitCircleChartSign {x : ℝ} (hx : x ≠ 0) :
    ∃ ε ∈ complexUnitCircleChartSigns, x = (ε : ℝ) * |x| := by
  by_cases hxpos : 0 < x
  · refine ⟨1, by norm_num [complexUnitCircleChartSigns], ?_⟩
    simp [abs_of_pos hxpos]
  · have hxneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hxpos) hx
    refine ⟨-1, by norm_num [complexUnitCircleChartSigns], ?_⟩
    simp [abs_of_neg hxneg]

/-- Every nonzero complex number belongs to one of the four literal
dominant-coordinate charts. -/
theorem exists_mem_complexUnitCircleDominantChart
    {z : ℂ} (hz : z ≠ 0) :
    ∃ i ∈ complexUnitCircleChartIndices,
      InComplexUnitCircleDominantChart i z := by
  by_cases hdom : |z.im| ≤ |z.re|
  · have hre : z.re ≠ 0 := by
      intro hre
      have him : z.im = 0 := by
        rw [hre, abs_zero] at hdom
        exact abs_eq_zero.mp (le_antisymm hdom (abs_nonneg _))
      apply hz
      apply Complex.ext <;> simp [hre, him]
    obtain ⟨ε, hε, hsign⟩ := exists_complexUnitCircleChartSign hre
    refine ⟨(.real, ε), ?_, ?_⟩
    · exact Finset.mem_product.mpr ⟨by simp, hε⟩
    · simpa [InComplexUnitCircleDominantChart, complexChartMajor,
        complexChartMinor] using ⟨hsign, hdom⟩
  · have hdom' : |z.re| ≤ |z.im| := (le_of_lt (lt_of_not_ge hdom))
    have him : z.im ≠ 0 := by
      intro him
      have hre : z.re = 0 := by
        rw [him, abs_zero] at hdom'
        exact abs_eq_zero.mp (le_antisymm hdom' (abs_nonneg _))
      apply hz
      apply Complex.ext <;> simp [hre, him]
    obtain ⟨ε, hε, hsign⟩ := exists_complexUnitCircleChartSign him
    refine ⟨(.imaginary, ε), ?_, ?_⟩
    · exact Finset.mem_product.mpr ⟨by simp, hε⟩
    · simpa [InComplexUnitCircleDominantChart, complexChartMajor,
        complexChartMinor] using ⟨hsign, hdom'⟩

/-- The selected chart denominator is nonzero. -/
theorem complexChartMajor_ne_zero_of_mem
    {i : ComplexUnitCircleChartIndex} {z : ℂ} (hz : z ≠ 0)
    (hi : InComplexUnitCircleDominantChart i z) :
    complexChartMajor i.1 z ≠ 0 := by
  intro hmajor
  have hminor : complexChartMinor i.1 z = 0 := by
    have hminorAbs : |complexChartMinor i.1 z| ≤ 0 := by
      simpa [hmajor] using hi.2
    exact abs_eq_zero.mp (le_antisymm hminorAbs (abs_nonneg _))
  cases haxis : i.1 with
  | real =>
      have hre : z.re = 0 := by
        simpa [complexChartMajor, haxis] using hmajor
      have him : z.im = 0 := by
        simpa [complexChartMinor, haxis] using hminor
      exact hz (Complex.ext hre him)
  | imaginary =>
      have hre : z.re = 0 := by
        simpa [complexChartMinor, haxis] using hminor
      have him : z.im = 0 := by
        simpa [complexChartMajor, haxis] using hmajor
      exact hz (Complex.ext hre him)

/-- On the unit circle, the selected denominator has an absolute lower bound
independent of the chart. -/
theorem one_half_le_abs_complexChartMajor_of_norm_eq_one
    {i : ComplexUnitCircleChartIndex} {z : ℂ}
    (hzNorm : ‖z‖ = 1)
    (hi : InComplexUnitCircleDominantChart i z) :
    (1 : ℝ) / 2 ≤ |complexChartMajor i.1 z| := by
  have hsq := complexChartMajor_sq_add_minor_sq i.1 z
  rw [hzNorm] at hsq
  norm_num at hsq
  have hminorSq : complexChartMinor i.1 z ^ 2 ≤
      complexChartMajor i.1 z ^ 2 := by
    have hp := pow_le_pow_left₀ (abs_nonneg _) hi.2 2
    simpa only [sq_abs] using hp
  have hmajorNonneg := abs_nonneg (complexChartMajor i.1 z)
  by_contra hnot
  have hlt : |complexChartMajor i.1 z| < (1 : ℝ) / 2 := lt_of_not_ge hnot
  have hmajorSq : complexChartMajor i.1 z ^ 2 < (1 : ℝ) / 4 := by
    nlinarith [sq_abs (complexChartMajor i.1 z)]
  nlinarith

/-- The ordinary coordinate on every dominant chart has absolute value at
most one. -/
theorem abs_complexUnitCircleChartCoordinate_le_one
    {i : ComplexUnitCircleChartIndex} {z : ℂ} (hz : z ≠ 0)
    (hi : InComplexUnitCircleDominantChart i z) :
    |complexUnitCircleChartCoordinate i.1 z| ≤ 1 := by
  have hmajor := complexChartMajor_ne_zero_of_mem hz hi
  rw [complexUnitCircleChartCoordinate, abs_div]
  exact (div_le_one (abs_pos.mpr hmajor)).mpr hi.2

/-- Membership in a literal finite-set chart retains the ambient family and
the exact chart predicate. -/
theorem mem_complexUnitCircleDominantChart
    {S : Finset ℂ} {i : ComplexUnitCircleChartIndex} {z : ℂ}
    (hz : z ∈ complexUnitCircleDominantChart S i) :
    z ∈ S ∧ InComplexUnitCircleDominantChart i z := by
  classical
  simpa only [complexUnitCircleDominantChart] using Finset.mem_filter.mp hz

/-- Any finite family of unit complex numbers is covered by the four literal
dominant-coordinate charts. -/
theorem complexUnitCircleFinset_subset_biUnion_charts
    (S : Finset ℂ) (hS : ∀ z ∈ S, ‖z‖ = 1) :
    S ⊆ complexUnitCircleChartIndices.biUnion
      (complexUnitCircleDominantChart S) := by
  intro z hz
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by
    rw [hS z hz]
    norm_num)
  obtain ⟨i, hi, hchart⟩ := exists_mem_complexUnitCircleDominantChart hz0
  apply Finset.mem_biUnion.mpr
  refine ⟨i, hi, ?_⟩
  classical
  simpa only [complexUnitCircleDominantChart] using
    (Finset.mem_filter.mpr ⟨hz, hchart⟩)

/-- Overlap-safe cardinality consequence of the four-chart cover. -/
theorem card_complexUnitCircleFinset_le_sum_card_charts
    (S : Finset ℂ) (hS : ∀ z ∈ S, ‖z‖ = 1) :
    S.card ≤ ∑ i ∈ complexUnitCircleChartIndices,
      (complexUnitCircleDominantChart S i).card := by
  exact (Finset.card_le_card
    (complexUnitCircleFinset_subset_biUnion_charts S hS)).trans
      Finset.card_biUnion_le

end

end PellPaper
