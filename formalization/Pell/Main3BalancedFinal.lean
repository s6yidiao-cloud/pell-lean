import Pell.Main3BalancedHighDEFinal
import Pell.Main3BalancedLowDEFinal
import Mathlib.Tactic

/-!
# Final main3 estimate for the complete balanced range

The exact high/low dyadic decomposition is now combined with the two final
union estimates.  The low-`DE` saving `1/(200*theta^2)` is stronger than the
high-`DE` saving `1/(400*theta^2)`, so monotonicity of real powers over
`Y >= 1` gives the common constant `3 + 32 = 35`.
-/

namespace PellPaper

open Filter

noncomputable section

/-- Uniform power saving for all main3 balanced factor tuples. -/
theorem eventually_main3BalancedDyadicFactorTuples_card_le
    (hWeil : OneVariableQuadraticWeilDegreeBound)
    (c : ℝ) (hc : 0 < c)
    (hsmall : 10 * c ^ 2 ≤ (1 : ℝ) / 2400) :
    ∀ᶠ Y : ℕ in atTop,
      ∀ theta : ℝ,
        3 ≤ theta →
        theta ≤ c * Real.sqrt
          (Real.log (Y : ℝ) / Real.log (Real.log (Y : ℝ))) →
        ((balancedDyadicFactorTuples (theta + 1 / 4) Y
          (main3BalancedR theta Y)).card : ℝ) ≤
            35 * (Y : ℝ) ^ (1 - 1 / (400 * theta ^ 2)) := by
  have hsmall400 : 10 * c ^ 2 ≤ (1 : ℝ) / 400 := by linarith
  have hhigh :=
    eventually_main3BalancedHighDEBoxUnion_card_le hWeil c hc hsmall
  have hlow :=
    eventually_main3BalancedLowDEBoxUnion_card_le c hc hsmall400
  filter_upwards [hhigh, hlow, eventually_ge_atTop 1] with Y hHigh hLow hY
  intro theta htheta hadmissible
  let y : ℝ := Y
  let b : ℝ := 1 - 1 / (400 * theta ^ 2)
  let ell : ℝ := 1 - 1 / (200 * theta ^ 2)
  have hyone : 1 ≤ y := by
    dsimp [y]
    exact_mod_cast hY
  have hthetaPos : 0 < theta := by linarith
  have hthetaSqPos : 0 < theta ^ 2 := sq_pos_of_pos hthetaPos
  have hellb : ell ≤ b := by
    dsimp [ell, b]
    apply sub_le_sub_left
    apply div_le_div_of_nonneg_left (by norm_num)
    · positivity
    · nlinarith
  have hrpow : y ^ ell ≤ y ^ b :=
    Real.rpow_le_rpow_of_exponent_le hyone hellb
  have hsplitNat :=
    card_balancedDyadicFactorTuples_le_main3BalancedHighDE_add_lowDE
      theta Y (main3BalancedR theta Y)
  have hsplit :
      ((balancedDyadicFactorTuples (theta + 1 / 4) Y
        (main3BalancedR theta Y)).card : ℝ) ≤
        ((main3BalancedHighDEBoxUnion theta Y
          (main3BalancedR theta Y)).card : ℝ) +
        ((main3BalancedLowDEBoxUnion theta Y
          (main3BalancedR theta Y)).card : ℝ) := by
    exact_mod_cast hsplitNat
  have hHigh' := hHigh theta htheta hadmissible
  have hLow' := hLow theta htheta hadmissible
  calc
    ((balancedDyadicFactorTuples (theta + 1 / 4) Y
      (main3BalancedR theta Y)).card : ℝ) ≤
        ((main3BalancedHighDEBoxUnion theta Y
          (main3BalancedR theta Y)).card : ℝ) +
        ((main3BalancedLowDEBoxUnion theta Y
          (main3BalancedR theta Y)).card : ℝ) := hsplit
    _ ≤ 3 * y ^ b + 32 * y ^ ell := by
      simpa only [y, b, ell] using add_le_add hHigh' hLow'
    _ ≤ 3 * y ^ b + 32 * y ^ b := by gcongr
    _ = 35 * y ^ b := by ring

end

end PellPaper
