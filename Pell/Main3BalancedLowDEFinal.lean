import Pell.Main3BalancedLowDEBoxSummation
import Pell.Main3BalancedDyadicScaleCount
import Pell.Main3BalancedRangeThreshold

/-!
# Final main3 bound for the balanced low-DE union

This is the exact composition of the finite low-`DE` union estimate with the
uniform four-scale absorption.  No new analytic input is introduced.
-/

namespace PellPaper

open Filter

noncomputable section

/-- Uniform final estimate for the low-`DE` half of the main3 balanced
dyadic decomposition. -/
theorem eventually_main3BalancedLowDEBoxUnion_card_le
    (c : ℝ) (hc : 0 < c)
    (hsmall : 10 * c ^ 2 ≤ (1 : ℝ) / 400) :
    ∀ᶠ Y : ℕ in atTop,
      ∀ theta : ℝ,
        3 ≤ theta →
        theta ≤ c * Real.sqrt
          (Real.log (Y : ℝ) / Real.log (Real.log (Y : ℝ))) →
        ((main3BalancedLowDEBoxUnion theta Y
          (main3BalancedR theta Y)).card : ℝ) ≤
            32 * (Y : ℝ) ^ (1 - 1 / (200 * theta ^ 2)) := by
  have habsorb :=
    eventually_main3Balanced_dyadicScaleProduct_mul_lowDEEnvelope_le
      c hc hsmall
  filter_upwards [habsorb] with Y hY
  intro theta htheta hadmissible
  have hsum :=
    main3BalancedLowDEBoxUnion_card_cast_le_scaleProduct_mul_elementaryEnvelope
      theta Y (main3BalancedR theta Y)
  change
    ((main3BalancedLowDEBoxUnion theta Y
      (main3BalancedR theta Y)).card : ℝ) ≤
      (main3BalancedDyadicScaleProduct theta Y : ℝ) *
        (4 * (Y : ℝ) ^ (1 - 1 / (100 * theta ^ 2)) +
          28 * Real.sqrt (Y : ℝ)) at hsum
  exact hsum.trans (hY theta htheta hadmissible)

end

end PellPaper
