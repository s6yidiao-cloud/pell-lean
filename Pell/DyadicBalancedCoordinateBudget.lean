import Pell.DyadicBalancedSquareSieveScale
import Mathlib.Tactic

/-!
# Endpoint bounds for the balanced coordinate ledger

This module derives the three coordinate-log hypotheses used by the balanced
square-sieve scale from the literal undoubled dyadic endpoint products.  The
source product has the manuscript exponent `q - 1/2`, the target product is
bounded by `Y`, and the cell denominator is at most `Y`.

The dyadic endpoints themselves are powers of two, so their lower bounds by
one are proved internally rather than retained as hypotheses.  The single
explicit coordinate constant is `C = 2`.
-/

namespace PellPaper

noncomputable section

/-- Each source endpoint is at least one, so the doubled maximum coordinate
bound is at most twice the source endpoint product. -/
theorem dyadicSourceCoordinateBound_le_two_mul_endpointProduct
    (i : ℕ × ℕ × ℕ × ℕ) :
    (dyadicSourceCoordinateBound i : ℝ) ≤
      2 * (((2 ^ i.1 : ℕ) : ℝ) * ((2 ^ i.2.1 : ℕ) : ℝ)) := by
  have hDpos : 0 < 2 ^ i.1 := by positivity
  have hEpos : 0 < 2 ^ i.2.1 := by positivity
  have hmax : max (2 ^ i.1) (2 ^ i.2.1) ≤
      (2 ^ i.1) * (2 ^ i.2.1) := by
    apply max_le
    · exact Nat.le_mul_of_pos_right _ hEpos
    · simpa [Nat.mul_comm] using Nat.le_mul_of_pos_right (2 ^ i.2.1) hDpos
  have hnat : 2 * max (2 ^ i.1) (2 ^ i.2.1) ≤
      2 * ((2 ^ i.1) * (2 ^ i.2.1)) := Nat.mul_le_mul_left 2 hmax
  rw [dyadicSourceCoordinateBound]
  exact_mod_cast hnat

/-- Each target endpoint is at least one, so the doubled maximum coordinate
bound is at most twice the target endpoint product. -/
theorem dyadicTargetCoordinateBound_le_two_mul_endpointProduct
    (i : ℕ × ℕ × ℕ × ℕ) :
    (dyadicTargetCoordinateBound i : ℝ) ≤
      2 * (((2 ^ i.2.2.1 : ℕ) : ℝ) *
        ((2 ^ i.2.2.2 : ℕ) : ℝ)) := by
  have hUpos : 0 < 2 ^ i.2.2.1 := by positivity
  have hVpos : 0 < 2 ^ i.2.2.2 := by positivity
  have hmax : max (2 ^ i.2.2.1) (2 ^ i.2.2.2) ≤
      (2 ^ i.2.2.1) * (2 ^ i.2.2.2) := by
    apply max_le
    · exact Nat.le_mul_of_pos_right _ hVpos
    · simpa [Nat.mul_comm] using
        Nat.le_mul_of_pos_right (2 ^ i.2.2.2) hUpos
  have hnat : 2 * max (2 ^ i.2.2.1) (2 ^ i.2.2.2) ≤
      2 * ((2 ^ i.2.2.1) * (2 ^ i.2.2.2)) :=
    Nat.mul_le_mul_left 2 hmax
  rw [dyadicTargetCoordinateBound]
  exact_mod_cast hnat

/-- The manuscript source-product range gives the source coordinate-log
hypothesis with the explicit constant `C = 2`. -/
theorem log_dyadicSourceCoordinateBound_le_two_mul_theta_logBudget
    (theta q : ℝ) (Y : ℕ) (i : ℕ × ℕ × ℕ × ℕ)
    (htheta : 3 ≤ theta) (hY : 2 ≤ Y)
    (hq : q ≤ 7 * theta / 6)
    (hsourceProduct :
      ((2 ^ i.1 : ℕ) : ℝ) * ((2 ^ i.2.1 : ℕ) : ℝ) ≤
        (Y : ℝ) ^ (q - 1 / 2)) :
    Real.log (dyadicSourceCoordinateBound i : ℝ) ≤
      2 * theta * (1 + Real.log (2 * (Y : ℝ))) := by
  let y : ℝ := Y
  let A : ℝ := 1 + Real.log (2 * y)
  have hypos : 0 < y := by
    dsimp [y]
    positivity
  have hyone : 1 ≤ y := by
    dsimp [y]
    exact_mod_cast (show 1 ≤ Y by omega)
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg hyone
  have hlogtwo : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hlogTwoY : Real.log (2 * y) = Real.log 2 + Real.log y := by
    rw [Real.log_mul (by norm_num) hypos.ne']
  have hAone : 1 ≤ A := by
    dsimp [A]
    rw [hlogTwoY]
    linarith
  have hA0 : 0 ≤ A := zero_le_one.trans hAone
  have hlogyA : Real.log y ≤ A := by
    dsimp [A]
    rw [hlogTwoY]
    linarith
  have hlogtwoA : Real.log (2 : ℝ) ≤ A := by
    dsimp [A]
    rw [hlogTwoY]
    linarith
  have hsourceUpper : (dyadicSourceCoordinateBound i : ℝ) ≤
      2 * y ^ (q - 1 / 2) := by
    calc
      (dyadicSourceCoordinateBound i : ℝ) ≤
          2 * (((2 ^ i.1 : ℕ) : ℝ) * ((2 ^ i.2.1 : ℕ) : ℝ)) :=
        dyadicSourceCoordinateBound_le_two_mul_endpointProduct i
      _ ≤ 2 * y ^ (q - 1 / 2) := by
        dsimp [y] at hsourceProduct ⊢
        gcongr
  have hsourcePos : (0 : ℝ) < dyadicSourceCoordinateBound i := by
    exact_mod_cast dyadicSourceCoordinateBound_pos i
  have hlogUpper :
      Real.log (dyadicSourceCoordinateBound i : ℝ) ≤
        Real.log (2 * y ^ (q - 1 / 2)) :=
    Real.log_le_log hsourcePos hsourceUpper
  have hlogRpow : Real.log (2 * y ^ (q - 1 / 2)) =
      Real.log 2 + (q - 1 / 2) * Real.log y := by
    rw [Real.log_mul (by norm_num)
        (Real.rpow_pos_of_pos hypos (q - 1 / 2)).ne',
      Real.log_rpow hypos]
  have hqterm : (q - 1 / 2) * Real.log y ≤
      (7 * theta / 6) * A := by
    calc
      (q - 1 / 2) * Real.log y ≤
          (7 * theta / 6) * Real.log y := by
        gcongr
        linarith
      _ ≤ (7 * theta / 6) * A := by
        gcongr
  have hcoefficient : 1 + 7 * theta / 6 ≤ 2 * theta := by
    linarith
  calc
    Real.log (dyadicSourceCoordinateBound i : ℝ) ≤
        Real.log 2 + (q - 1 / 2) * Real.log y := by
      simpa only [hlogRpow] using hlogUpper
    _ ≤ A + (7 * theta / 6) * A := add_le_add hlogtwoA hqterm
    _ = (1 + 7 * theta / 6) * A := by ring
    _ ≤ (2 * theta) * A :=
      mul_le_mul_of_nonneg_right hcoefficient hA0
    _ = 2 * theta * (1 + Real.log (2 * (Y : ℝ))) := by
      dsimp [A, y]

/-- The target endpoint-product range gives a sharper target coordinate-log
bound than the `C = 2` interface requires. -/
theorem log_dyadicTargetCoordinateBound_le_logBudget
    (Y : ℕ) (i : ℕ × ℕ × ℕ × ℕ)
    (htargetProduct :
      ((2 ^ i.2.2.1 : ℕ) : ℝ) * ((2 ^ i.2.2.2 : ℕ) : ℝ) ≤
        (Y : ℝ)) :
    Real.log (dyadicTargetCoordinateBound i : ℝ) ≤
      1 + Real.log (2 * (Y : ℝ)) := by
  have htargetUpper : (dyadicTargetCoordinateBound i : ℝ) ≤
      2 * (Y : ℝ) := by
    calc
      (dyadicTargetCoordinateBound i : ℝ) ≤
          2 * (((2 ^ i.2.2.1 : ℕ) : ℝ) *
            ((2 ^ i.2.2.2 : ℕ) : ℝ)) :=
        dyadicTargetCoordinateBound_le_two_mul_endpointProduct i
      _ ≤ 2 * (Y : ℝ) := by gcongr
  have htargetPos : (0 : ℝ) < dyadicTargetCoordinateBound i := by
    exact_mod_cast dyadicTargetCoordinateBound_pos i
  have hlog := Real.log_le_log htargetPos htargetUpper
  linarith

/-- A denominator `M ≤ Y` contributes at most the same elementary log
budget as the target coordinates. -/
theorem log_dyadicCellDenominator_add_one_le_logBudget
    (Y M : ℕ) (hY : 2 ≤ Y) (hM : M ≤ Y) :
    Real.log ((M : ℝ) + 1) ≤ 1 + Real.log (2 * (Y : ℝ)) := by
  have hnat : M + 1 ≤ 2 * Y := by omega
  have hcast : (M : ℝ) + 1 ≤ 2 * (Y : ℝ) := by exact_mod_cast hnat
  have hpos : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hlog := Real.log_le_log hpos hcast
  linarith

/-- The literal endpoint-product hypotheses bound the complete balanced
coordinate ledger with the square-sieve interface's explicit choice `C = 2`.
No coordinate-height estimate remains as a premise. -/
theorem dyadicBalancedCoordinateLogBudget_le_eight_mul_theta_of_endpointProducts
    (theta q : ℝ) (Y : ℕ) (i : ℕ × ℕ × ℕ × ℕ) (M : ℕ)
    (htheta : 3 ≤ theta) (hY : 2 ≤ Y) (hq : q ≤ 7 * theta / 6)
    (hM : M ≤ Y)
    (hsourceProduct :
      ((2 ^ i.1 : ℕ) : ℝ) * ((2 ^ i.2.1 : ℕ) : ℝ) ≤
        (Y : ℝ) ^ (q - 1 / 2))
    (htargetProduct :
      ((2 ^ i.2.2.1 : ℕ) : ℝ) * ((2 ^ i.2.2.2 : ℕ) : ℝ) ≤
        (Y : ℝ)) :
    dyadicBalancedCoordinateLogBudget i M ≤
      8 * theta * (1 + Real.log (2 * (Y : ℝ))) := by
  let A : ℝ := 1 + Real.log (2 * (Y : ℝ))
  have hAone : 1 ≤ A := by
    dsimp [A]
    have htwoY : (1 : ℝ) ≤ 2 * (Y : ℝ) := by
      exact_mod_cast (show 1 ≤ 2 * Y by omega)
    exact le_add_of_nonneg_right (Real.log_nonneg htwoY)
  have hsource :=
    log_dyadicSourceCoordinateBound_le_two_mul_theta_logBudget
      theta q Y i htheta hY hq hsourceProduct
  have htarget0 :=
    log_dyadicTargetCoordinateBound_le_logBudget Y i htargetProduct
  have hdenominator0 :=
    log_dyadicCellDenominator_add_one_le_logBudget Y M hY hM
  have htarget : Real.log (dyadicTargetCoordinateBound i : ℝ) ≤
      2 * A := by linarith
  have hdenominator : Real.log ((M : ℝ) + 1) ≤
      2 * theta * A := by
    have hthetaOne : 1 ≤ 2 * theta := by linarith
    exact hdenominator0.trans <| by
      calc
        A = 1 * A := by ring
        _ ≤ (2 * theta) * A :=
          mul_le_mul_of_nonneg_right hthetaOne (zero_le_one.trans hAone)
        _ = 2 * theta * A := by ring
  have hcoordinate :=
    dyadicBalancedCoordinateLogBudget_le_of_reducedBasisBounds
      theta 2 Y i M htheta (by norm_num) hY hsource htarget hdenominator
  dsimp [A] at htarget hdenominator hcoordinate ⊢
  norm_num at hcoordinate ⊢
  exact hcoordinate

/-- Endpoint products and one explicit prime-scale inequality discharge the
entire residual square-sieve budget.  This is the manuscript-facing version
of the scale theorem, with the coordinate constant specialized to `2`. -/
theorem fullCellResidualSieveUniformBudgetThreshold_le_balancedSquareSieveScale_of_endpointProducts
    (B : ℕ) (theta q : ℝ) (Y : ℕ)
    (i : ℕ × ℕ × ℕ × ℕ) (M : ℕ)
    (htheta : 3 ≤ theta) (hY : 2 ≤ Y)
    (hBupper : (B : ℝ) < theta ^ 2 + 1)
    (hq : q ≤ 7 * theta / 6) (hM : M ≤ Y)
    (hsourceProduct :
      ((2 ^ i.1 : ℕ) : ℝ) * ((2 ^ i.2.1 : ℕ) : ℝ) ≤
        (Y : ℝ) ^ (q - 1 / 2))
    (htargetProduct :
      ((2 ^ i.2.2.1 : ℕ) : ℝ) * ((2 ^ i.2.2.2 : ℕ) : ℝ) ≤
        (Y : ℝ))
    (hprime :
      640000 * theta ^ 7 * (1 + Real.log (2 * (Y : ℝ))) ≤
        dyadicBalancedSquareSieveRealScale i M) :
    fullCellResidualSieveUniformBudgetThreshold i M B
        (dyadicSourceTargetCellResidualHeight B i) ≤
      (dyadicBalancedSquareSieveScale i M : ℝ) := by
  apply
    fullCellResidualSieveUniformBudgetThreshold_le_balancedSquareSieveScale_of_primeThreshold
      B theta 2 Y i M htheta (by norm_num) hY hBupper
  · exact log_dyadicSourceCoordinateBound_le_two_mul_theta_logBudget
      theta q Y i htheta hY hq hsourceProduct
  · have htarget :=
      log_dyadicTargetCoordinateBound_le_logBudget Y i htargetProduct
    have hA0 : 0 ≤ 1 + Real.log (2 * (Y : ℝ)) := by
      have htwoY : (1 : ℝ) ≤ 2 * (Y : ℝ) := by
        exact_mod_cast (show 1 ≤ 2 * Y by omega)
      linarith [Real.log_nonneg htwoY]
    nlinarith
  · have hdenominator :=
      log_dyadicCellDenominator_add_one_le_logBudget Y M hY hM
    have hA0 : 0 ≤ 1 + Real.log (2 * (Y : ℝ)) := by
      have htwoY : (1 : ℝ) ≤ 2 * (Y : ℝ) := by
        exact_mod_cast (show 1 ≤ 2 * Y by omega)
      linarith [Real.log_nonneg htwoY]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ theta) hA0]
  · norm_num at hprime ⊢
    exact hprime

end

end PellPaper
