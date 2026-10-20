import Pell.CorollaryOddClassFiniteCutoff

/-!
# Browning--Chan one-cutoff reduction for the odd class-number average

The earlier odd-class cutoff module first replaces the individual factor
`sqrt D / log D` by its uniform cutoff majorant.  That is appropriate for
the low-regulator Cauchy estimate, but it loses the extra logarithmic saving
in the Browning--Chan weighted first moment on the high-regulator range.

This module retains the individual factor in a named baseline summand.  The
exact class-number formula and the Pell/maximal-order regulator comparison
then give a pointwise bound with constant `6 * Cgenus`.  A single split at
`T` bounds the low part by the existing `E (T + 1)` Cauchy estimate and the
high part by an unrestricted majorant for the Browning--Chan baseline sum.

The published weighted moment is exposed as a named proposition, never as a
primitive declaration.  Its analytic proof is deliberately outside this
elementary module.
-/

namespace PellPaper

open Filter
open scoped BigOperators

noncomputable section

/-- The individual summand in the Browning--Chan weighted first moment:
`sqrt D / log D * 2^(-omega D) * L(1, chi_D)`. -/
def browningChanOddClassBaselineTerm (D : ℕ) : ℝ :=
  (Real.sqrt (D : ℝ) / Real.log (D : ℝ)) *
    genusWeight D * selectedKroneckerLValue D

/-- The unrestricted Browning--Chan baseline sum at the strict real cutoff
`D < X`. -/
def browningChanOddClassBaselineSum (X : ℝ) : ℝ :=
  ∑ D ∈ fundamentalDiscriminantsBelow X,
    browningChanOddClassBaselineTerm D

/-- The scale in the Browning--Chan weighted moment.  Real powers are used
for both occurrences of the exponent `3 / 2`. -/
def browningChanOddClassBaselineScale (X : ℝ) : ℝ :=
  Real.rpow X (3 / 2) / Real.rpow (Real.log X) (3 / 2)

/-- Named interface for the published Browning--Chan weighted first moment.

The constant is chosen before the cutoff, and the cutoff is strict on the
literal positive-fundamental-discriminant family used by the field sum. -/
def BrowningChanOddClassBaselineMoment : Prop :=
  ∃ Cbc : ℝ, 0 < Cbc ∧
    ∀ᶠ X : ℝ in atTop,
      browningChanOddClassBaselineSum X ≤
        Cbc * browningChanOddClassBaselineScale X

theorem browningChanOddClassBaselineTerm_nonneg
    {D : ℕ} (hD : PositiveFundamentalDiscriminant D) :
    0 ≤ browningChanOddClassBaselineTerm D := by
  unfold browningChanOddClassBaselineTerm
  have hlog : 0 < Real.log (D : ℝ) := by
    exact Real.log_pos (by exact_mod_cast hD.1)
  exact mul_nonneg
    (mul_nonneg (div_nonneg (Real.sqrt_nonneg _) hlog.le)
      (genusWeight_nonneg D))
    (selectedKroneckerLValue_nonneg D)

theorem browningChanOddClassBaselineSum_nonneg (X : ℝ) :
    0 ≤ browningChanOddClassBaselineSum X := by
  unfold browningChanOddClassBaselineSum
  apply Finset.sum_nonneg
  intro D hDX
  exact browningChanOddClassBaselineTerm_nonneg
    (mem_fundamentalDiscriminantsBelow.mp hDX).1

/-- Exact pointwise odd-class bound with the concrete Pell regulator.  The
constant `6 * Cgenus` is solely the factor-six regulator transport multiplied
by the supplied genus constant; the individual `sqrt D / log D` has not been
uniformized. -/
theorem positiveFundamentalDiscriminantOddClassNumber_le_six_mul_genus_browningChanBaseline_div_pellOrderRegulator
    {Cgenus : ℝ} (hgenus : OddClassGenusPointwiseBound Cgenus)
    {D : ℕ} (hD : PositiveFundamentalDiscriminant D) :
    (positiveFundamentalDiscriminantOddClassNumber D : ℝ) ≤
      (6 * Cgenus) *
        (browningChanOddClassBaselineTerm D / pellOrderRegulator D) := by
  have hlog : 0 < Real.log (D : ℝ) :=
    Real.log_pos (by exact_mod_cast hD.1)
  have hratio : 0 ≤ Real.sqrt (D : ℝ) / Real.log (D : ℝ) :=
    div_nonneg (Real.sqrt_nonneg _) hlog.le
  have hweight : 0 ≤ Cgenus * genusWeight D :=
    mul_nonneg hgenus.1 (genusWeight_nonneg D)
  have hform :=
    properFormClass_card_le_selectedLValue_div_normalizedRegulator D hD
  have hdenom :=
    div_maximalOrderFundamentalUnitRegulator_le_six_mul_div_pellOrderRegulator
      hD (selectedKroneckerLValue_nonneg D)
  calc
    (positiveFundamentalDiscriminantOddClassNumber D : ℝ) ≤
        Cgenus * genusWeight D *
          (Nat.card (IntegralBinaryQuadraticForm.ProperFormClass (D : ℤ)) : ℝ) :=
      hgenus.2 D hD
    _ ≤ Cgenus * genusWeight D *
        ((Real.sqrt (D : ℝ) / Real.log (D : ℝ)) *
          (selectedKroneckerLValue D /
            maximalOrderFundamentalUnitRegulator D)) :=
      mul_le_mul_of_nonneg_left hform hweight
    _ ≤ Cgenus * genusWeight D *
        ((Real.sqrt (D : ℝ) / Real.log (D : ℝ)) *
          (6 * selectedKroneckerLValue D / pellOrderRegulator D)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hdenom hratio) hweight
    _ = (6 * Cgenus) *
        (browningChanOddClassBaselineTerm D / pellOrderRegulator D) := by
      unfold browningChanOddClassBaselineTerm
      ring

/-- The baseline numerator on the low-regulator filter is controlled by the
current Cauchy estimate at `E (T + 1)`.  This is the only place where the
uniform factor-four comparison of `sqrt D / log D` with its value at `X` is
used. -/
theorem browningChanOddClassBaseline_lowPellOrderRegulatorSum_le
    (X T M : ℝ) (hX : 3 ≤ X)
    (hmoment :
      (∑ D ∈ fundamentalDiscriminantsBelow X,
        (selectedKroneckerLValue D) ^ 2) ≤ M) :
    (∑ D ∈ (fundamentalDiscriminantsBelow X).filter
      (fun D ↦ pellOrderRegulator D ≤ T),
        browningChanOddClassBaselineTerm D) ≤
      4 * (Real.sqrt X / Real.log X) *
        Real.sqrt (E (T + 1) X * M) := by
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hfactor : 0 ≤ 4 * (Real.sqrt X / Real.log X) :=
    mul_nonneg (by norm_num)
      (div_nonneg (Real.sqrt_nonneg _) hlogX.le)
  calc
    (∑ D ∈ (fundamentalDiscriminantsBelow X).filter
        (fun D ↦ pellOrderRegulator D ≤ T),
          browningChanOddClassBaselineTerm D) ≤
      ∑ D ∈ (fundamentalDiscriminantsBelow X).filter
        (fun D ↦ pellOrderRegulator D ≤ T),
          (4 * (Real.sqrt X / Real.log X)) *
            selectedKroneckerLValue D := by
      apply Finset.sum_le_sum
      intro D hDlow
      have hDX := (Finset.mem_filter.mp hDlow).1
      obtain ⟨hD, hDXreal⟩ := mem_fundamentalDiscriminantsBelow.mp hDX
      have hDtwo : (2 : ℝ) ≤ D := by exact_mod_cast hD.1
      have huniform := sqrt_div_log_le_four_mul_of_two_le hDtwo hDXreal.le
      have hweightedL : 0 ≤ genusWeight D * selectedKroneckerLValue D :=
        mul_nonneg (genusWeight_nonneg D) (selectedKroneckerLValue_nonneg D)
      unfold browningChanOddClassBaselineTerm
      calc
        (Real.sqrt (D : ℝ) / Real.log (D : ℝ)) *
              genusWeight D * selectedKroneckerLValue D =
            (Real.sqrt (D : ℝ) / Real.log (D : ℝ)) *
              (genusWeight D * selectedKroneckerLValue D) := by ring
        _ ≤ (4 * (Real.sqrt X / Real.log X)) *
              (genusWeight D * selectedKroneckerLValue D) :=
          mul_le_mul_of_nonneg_right huniform hweightedL
        _ ≤ (4 * (Real.sqrt X / Real.log X)) *
              (1 * selectedKroneckerLValue D) := by
          apply mul_le_mul_of_nonneg_left _ hfactor
          exact mul_le_mul_of_nonneg_right (genusWeight_le_one D)
            (selectedKroneckerLValue_nonneg D)
        _ = (4 * (Real.sqrt X / Real.log X)) *
              selectedKroneckerLValue D := by ring
    _ = (4 * (Real.sqrt X / Real.log X)) *
        (∑ D ∈ (fundamentalDiscriminantsBelow X).filter
          (fun D ↦ pellOrderRegulator D ≤ T),
            selectedKroneckerLValue D) := by
      rw [Finset.mul_sum]
    _ ≤ (4 * (Real.sqrt X / Real.log X)) *
        Real.sqrt (E (T + 1) X * M) := by
      exact mul_le_mul_of_nonneg_left
        (selectedKroneckerLValue_lowPellOrderRegulatorSum_le
          X T M (by linarith) hmoment) hfactor
    _ = 4 * (Real.sqrt X / Real.log X) *
        Real.sqrt (E (T + 1) X * M) := by ring

/-- An unrestricted majorant for the Browning--Chan baseline sum also
majorizes its high-regulator subfamily. -/
theorem browningChanOddClassBaseline_highPellOrderRegulatorSum_le
    (X T B : ℝ)
    (hbaseline : browningChanOddClassBaselineSum X ≤ B) :
    (∑ D ∈ (fundamentalDiscriminantsBelow X).filter
      (fun D ↦ T < pellOrderRegulator D),
        browningChanOddClassBaselineTerm D) ≤ B := by
  calc
    (∑ D ∈ (fundamentalDiscriminantsBelow X).filter
        (fun D ↦ T < pellOrderRegulator D),
          browningChanOddClassBaselineTerm D) ≤
      ∑ D ∈ fundamentalDiscriminantsBelow X,
        browningChanOddClassBaselineTerm D := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro D hDX _hnot
      exact browningChanOddClassBaselineTerm_nonneg
        (mem_fundamentalDiscriminantsBelow.mp hDX).1
    _ ≤ B := by
      simpa only [browningChanOddClassBaselineSum] using hbaseline

/-- Complete one-cutoff estimate retaining the Browning--Chan baseline.

The low term uses Cauchy--Schwarz and `E (T + 1)`; the high term is exactly
the unrestricted baseline majorant divided by `T`. -/
theorem positiveFundamentalDiscriminantOddClassSum_le_browningChan_oneCutoff
    (Cgenus X T M B : ℝ)
    (hgenus : OddClassGenusPointwiseBound Cgenus)
    (hX : 3 ≤ X) (hT : (1 / 2 : ℝ) ≤ T)
    (hmoment :
      (∑ D ∈ fundamentalDiscriminantsBelow X,
        (selectedKroneckerLValue D) ^ 2) ≤ M)
    (hbaseline : browningChanOddClassBaselineSum X ≤ B) :
    positiveFundamentalDiscriminantOddClassSum X ≤
      48 * Cgenus * (Real.sqrt X / Real.log X) *
          Real.sqrt (E (T + 1) X * M) +
        (6 * Cgenus * B) / T := by
  have hfinite := finite_sum_class_bound_of_cutoff_numerators
    (fundamentalDiscriminantsBelow X)
    (fun D ↦ (positiveFundamentalDiscriminantOddClassNumber D : ℝ))
    browningChanOddClassBaselineTerm pellOrderRegulator
    (6 * Cgenus) (1 / 2 : ℝ) T
    (4 * (Real.sqrt X / Real.log X) * Real.sqrt (E (T + 1) X * M)) B
    (mul_nonneg (by norm_num) hgenus.1)
    (fun D hDX ↦ browningChanOddClassBaselineTerm_nonneg
      (mem_fundamentalDiscriminantsBelow.mp hDX).1)
    (fun D hDX ↦ (one_half_lt_pellOrderRegulator
      (mem_fundamentalDiscriminantsBelow.mp hDX).1).le)
    (by norm_num) hT
    (fun D hDX ↦
      positiveFundamentalDiscriminantOddClassNumber_le_six_mul_genus_browningChanBaseline_div_pellOrderRegulator
        hgenus (mem_fundamentalDiscriminantsBelow.mp hDX).1)
    (browningChanOddClassBaseline_lowPellOrderRegulatorSum_le
      X T M hX hmoment)
    (browningChanOddClassBaseline_highPellOrderRegulatorSum_le
      X T B hbaseline)
  unfold positiveFundamentalDiscriminantOddClassSum
  calc
    (∑ D ∈ fundamentalDiscriminantsBelow X,
        (positiveFundamentalDiscriminantOddClassNumber D : ℝ)) ≤
      (6 * Cgenus) *
        ((4 * (Real.sqrt X / Real.log X) *
          Real.sqrt (E (T + 1) X * M)) / (1 / 2 : ℝ) + B / T) := hfinite
    _ = 48 * Cgenus * (Real.sqrt X / Real.log X) *
          Real.sqrt (E (T + 1) X * M) +
        (6 * Cgenus * B) / T := by ring

/-- Field-isomorphism-class form of the same finite Browning--Chan cutoff
bound, using the proved exact field/discriminant transport. -/
theorem realQuadraticFieldOddClassSum_le_browningChan_oneCutoff
    (Cgenus X T M B : ℝ)
    (hgenus : OddClassGenusPointwiseBound Cgenus)
    (hX : 3 ≤ X) (hT : (1 / 2 : ℝ) ≤ T)
    (hmoment :
      (∑ D ∈ fundamentalDiscriminantsBelow X,
        (selectedKroneckerLValue D) ^ 2) ≤ M)
    (hbaseline : browningChanOddClassBaselineSum X ≤ B) :
    realQuadraticFieldOddClassSum X ≤
      48 * Cgenus * (Real.sqrt X / Real.log X) *
          Real.sqrt (E (T + 1) X * M) +
        (6 * Cgenus * B) / T := by
  rw [realQuadraticFieldOddClassSum_eq_positiveFundamentalDiscriminantOddClassSum]
  exact positiveFundamentalDiscriminantOddClassSum_le_browningChan_oneCutoff
    Cgenus X T M B hgenus hX hT hmoment hbaseline

end

end PellPaper
