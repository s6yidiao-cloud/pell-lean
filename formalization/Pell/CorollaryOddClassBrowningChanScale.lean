import Pell.CorollaryOddClassBrowningChanCutoff
import Pell.CorollaryOddClassScale

/-!
# Browning--Chan scale algebra for Corollary 1.2

The weighted first moment has scale
`X^(3/2) / (log X)^(3/2)`.  Dividing it by the moving regulator cutoff is
exactly the odd-class average scale, up to the reciprocal cutoff constant.
-/

namespace PellPaper

open Filter Asymptotics

noncomputable section

theorem browningChanOddClassBaselineScale_nonneg {X : ℝ} (hX : 1 ≤ X) :
    0 ≤ browningChanOddClassBaselineScale X := by
  unfold browningChanOddClassBaselineScale
  exact div_nonneg
    (Real.rpow_nonneg (zero_le_one.trans hX) _)
    (Real.rpow_nonneg (Real.log_nonneg hX) _)

/-- The explicit eventual-constant interface is exactly Mathlib's `IsBigO`
spelling of the published Browning--Chan estimate.  This removes any
notational ambiguity at the literature boundary: the source's `\ll` and
`BrowningChanOddClassBaselineMoment` carry the same mathematical content. -/
theorem browningChanOddClassBaselineMoment_iff_isBigO :
    BrowningChanOddClassBaselineMoment ↔
      (fun X : ℝ ↦ browningChanOddClassBaselineSum X) =O[atTop]
        browningChanOddClassBaselineScale := by
  constructor
  · rintro ⟨C, _hC, hbound⟩
    rw [isBigO_iff]
    refine ⟨C, ?_⟩
    filter_upwards [hbound, eventually_ge_atTop (3 : ℝ)] with X hboundX hX
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (browningChanOddClassBaselineSum_nonneg X),
      abs_of_nonneg (browningChanOddClassBaselineScale_nonneg (by linarith))]
      using hboundX
  · intro hO
    rw [isBigO_iff] at hO
    obtain ⟨C, hbound⟩ := hO
    refine ⟨|C| + 1, by positivity, ?_⟩
    filter_upwards [hbound, eventually_ge_atTop (3 : ℝ)] with X hboundX hX
    have hscale : 0 ≤ browningChanOddClassBaselineScale X :=
      browningChanOddClassBaselineScale_nonneg (by linarith)
    have hC : C ≤ |C| + 1 := by linarith [le_abs_self C]
    calc
      browningChanOddClassBaselineSum X =
          ‖browningChanOddClassBaselineSum X‖ := by
            rw [Real.norm_eq_abs,
              abs_of_nonneg (browningChanOddClassBaselineSum_nonneg X)]
      _ ≤ C * ‖browningChanOddClassBaselineScale X‖ := hboundX
      _ = C * browningChanOddClassBaselineScale X := by
            rw [Real.norm_eq_abs, abs_of_nonneg hscale]
      _ ≤ (|C| + 1) * browningChanOddClassBaselineScale X :=
            mul_le_mul_of_nonneg_right hC hscale

/-- Exact scale identity for the high-regulator Browning--Chan contribution.
The range `exp 1 < X` supplies positivity of both logarithmic denominators. -/
theorem browningChanOddClassBaselineScale_div_classAverageCutoff
    {kappa X : ℝ} (hX : Real.exp 1 < X) :
    browningChanOddClassBaselineScale X / classAverageCutoff kappa X =
      (1 / kappa) * oddClassAverageScale X := by
  have hlog : 0 < Real.log X := classAverageCutoff_log_pos hX
  have hsqrt : 0 < Real.sqrt (Real.log X) := Real.sqrt_pos.2 hlog
  unfold browningChanOddClassBaselineScale oddClassAverageScale
  rw [div_eq_mul_one_div, one_div_classAverageCutoff,
    Real.sqrt_div' _ hlog.le,
    rpow_three_halves_eq_mul_sqrt hlog]
  field_simp [hlog.ne', hsqrt.ne']
  rw [Real.sq_sqrt hlog.le]

/-- Raw-form spelling of the same identity, with `Real.rpow (3 / 2)` visible
on both the `X` and `log X` factors. -/
theorem browningChan_rpow_three_halves_div_cutoff_eq_oddClassAverageScale
    {kappa X : ℝ} (hX : Real.exp 1 < X) :
    (Real.rpow X (3 / 2) / Real.rpow (Real.log X) (3 / 2)) /
        classAverageCutoff kappa X =
      (1 / kappa) * oddClassAverageScale X := by
  exact browningChanOddClassBaselineScale_div_classAverageCutoff hX

end

end PellPaper
