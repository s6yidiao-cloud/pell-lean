import Pell.CorollaryOddClassBrowningChanCapstone

/-!
# Weighted-moment bridge for the odd-class average

The proof of the odd-class average theorem in the manuscript uses the genus-weighted first
moment
`sum_{D < X} 2^(-omega D) L(1, chi_D) \ll X / sqrt (log X)`.
This module records that analytic input as one named proposition and proves
that it implies the Browning--Chan baseline moment used by the class-average pipeline.

No analytic estimate is asserted here.  All unproved content remains in
`Main4OddClassWeightedFirstMoment`.
-/

namespace PellPaper

open Filter
open scoped BigOperators

noncomputable section

/-- The literal genus-weighted selected-L sum at the strict real cutoff
`D < X`. -/
def main4OddClassWeightedFirstMomentSum (X : ℝ) : ℝ :=
  ∑ D ∈ fundamentalDiscriminantsBelow X,
    genusWeight D * selectedKroneckerLValue D

/-- The exact eventual positive-constant form of the weighted first moment
used in the proof of the odd-class average theorem in the manuscript.

The constant is chosen before `X`, the discriminant cutoff is strict, and
the sum is over the same literal positive-fundamental-discriminant family as
the field sum. -/
def Main4OddClassWeightedFirstMoment : Prop :=
  ∃ Cmain4 : ℝ, 0 < Cmain4 ∧
    ∀ᶠ X : ℝ in atTop,
      main4OddClassWeightedFirstMomentSum X ≤
        Cmain4 * (X / Real.sqrt (Real.log X))

/-- Uniformizing the individual factor `sqrt D / log D` embeds the `main4`
weighted sum into the Browning--Chan baseline sum.  The factor four is the
explicit constant in `sqrt_div_log_le_four_mul_of_two_le`. -/
theorem browningChanOddClassBaselineSum_le_four_mul_main4WeightedSum
    (X : ℝ) (hX : 3 ≤ X) :
    browningChanOddClassBaselineSum X ≤
      4 * (Real.sqrt X / Real.log X) *
        main4OddClassWeightedFirstMomentSum X := by
  have _hXpos : 0 < X := by linarith
  unfold browningChanOddClassBaselineSum
  unfold main4OddClassWeightedFirstMomentSum
  calc
    (∑ D ∈ fundamentalDiscriminantsBelow X,
        browningChanOddClassBaselineTerm D) ≤
      ∑ D ∈ fundamentalDiscriminantsBelow X,
        (4 * (Real.sqrt X / Real.log X)) *
          (genusWeight D * selectedKroneckerLValue D) := by
      apply Finset.sum_le_sum
      intro D hDX
      obtain ⟨hD, hDXreal⟩ := mem_fundamentalDiscriminantsBelow.mp hDX
      have hDtwo : (2 : ℝ) ≤ D := by exact_mod_cast hD.1
      have huniform :=
        sqrt_div_log_le_four_mul_of_two_le hDtwo hDXreal.le
      have hweighted : 0 ≤ genusWeight D * selectedKroneckerLValue D :=
        mul_nonneg (genusWeight_nonneg D)
          (selectedKroneckerLValue_nonneg D)
      unfold browningChanOddClassBaselineTerm
      calc
        (Real.sqrt (D : ℝ) / Real.log (D : ℝ)) *
              genusWeight D * selectedKroneckerLValue D =
            (Real.sqrt (D : ℝ) / Real.log (D : ℝ)) *
              (genusWeight D * selectedKroneckerLValue D) := by ring
        _ ≤ (4 * (Real.sqrt X / Real.log X)) *
              (genusWeight D * selectedKroneckerLValue D) :=
          mul_le_mul_of_nonneg_right huniform hweighted
    _ = 4 * (Real.sqrt X / Real.log X) *
        (∑ D ∈ fundamentalDiscriminantsBelow X,
          genusWeight D * selectedKroneckerLValue D) := by
      rw [Finset.mul_sum]

/-- Exact algebraic identity between the scale obtained by combining the
`main4` moment with the factor `sqrt X / log X` and the published
Browning--Chan baseline scale. -/
theorem four_mul_sqrt_div_log_mul_main4Scale_eq_browningChanScale
    {C X : ℝ} (hX : 3 ≤ X) :
    4 * (Real.sqrt X / Real.log X) *
        (C * (X / Real.sqrt (Real.log X))) =
      (4 * C) * browningChanOddClassBaselineScale X := by
  have hXpos : 0 < X := by linarith
  have hlog : 0 < Real.log X := Real.log_pos (by linarith)
  have hsqrtLog : Real.sqrt (Real.log X) ≠ 0 :=
    (Real.sqrt_pos.2 hlog).ne'
  unfold browningChanOddClassBaselineScale
  rw [rpow_three_halves_eq_mul_sqrt hXpos,
    rpow_three_halves_eq_mul_sqrt hlog]
  field_simp [hlog.ne', hsqrtLog]

/-- The manuscript weighted first moment implies the sole analytic
interface used by the production Browning--Chan completion. -/
theorem browningChanOddClassBaselineMoment_of_main4WeightedFirstMoment
    (hMain4 : Main4OddClassWeightedFirstMoment) :
    BrowningChanOddClassBaselineMoment := by
  obtain ⟨Cmain4, hCmain4, hMain4Bound⟩ := hMain4
  refine ⟨4 * Cmain4, mul_pos (by norm_num) hCmain4, ?_⟩
  filter_upwards [hMain4Bound, eventually_ge_atTop (3 : ℝ)] with
      X hMain4X hX
  have hlog : 0 < Real.log X := Real.log_pos (by linarith)
  have hfactor : 0 ≤ 4 * (Real.sqrt X / Real.log X) :=
    mul_nonneg (by norm_num)
      (div_nonneg (Real.sqrt_nonneg _) hlog.le)
  calc
    browningChanOddClassBaselineSum X ≤
        4 * (Real.sqrt X / Real.log X) *
          main4OddClassWeightedFirstMomentSum X :=
      browningChanOddClassBaselineSum_le_four_mul_main4WeightedSum X hX
    _ ≤ 4 * (Real.sqrt X / Real.log X) *
        (Cmain4 * (X / Real.sqrt (Real.log X))) :=
      mul_le_mul_of_nonneg_left hMain4X hfactor
    _ = (4 * Cmain4) * browningChanOddClassBaselineScale X :=
      four_mul_sqrt_div_log_mul_main4Scale_eq_browningChanScale hX

/-- Exact Corollary 1.2 assertion conditional only on the weighted first
moment stated in the manuscript. -/
theorem realQuadraticFieldOddClassAverageAssertion_conditional_on_main4WeightedFirstMoment
    (hMain4 : Main4OddClassWeightedFirstMoment) :
    RealQuadraticFieldOddClassAverageAssertion := by
  exact
    realQuadraticFieldOddClassAverageAssertion_conditional_on_browningChanMoment
      (browningChanOddClassBaselineMoment_of_main4WeightedFirstMoment hMain4)

end

end PellPaper
