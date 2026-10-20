import Pell.TwoLayerTargetTwiceBalancedFanRate
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Target-twice fan rate with separate decay and clearing exponents

The target localization uses a fixed logarithmic slack, so its determinant
decay exponent is slightly smaller than the exponent needed to clear the
source endpoint product.  This module keeps those two exponents separate and
charges their bounded logarithmic gap explicitly.  The charge is finite in
the degree and is absorbed by the existing `exp (800 * theta^2) < Y`
threshold.
-/

namespace PellPaper

noncomputable section

/-- The fixed fan ledger after allowing a source-clearing exponent whose
logarithmic gap from the determinant-decay exponent is at most `log 15360`. -/
def twoLayerTargetTwiceSplitExponentFanFixedLogCost (B : ℕ) : ℝ :=
  twoLayerTargetTwiceFanFixedLogCost B +
    ((B : ℝ) + 1) * Real.log 15360

/-- Changing only the source-clearing exponent changes the exact clearing
ledger by `(B+1) (qCost-qDecay) L`. -/
theorem twoLayerTargetTwiceBalancedDoubledBaseLogCost_change_sourceExponent
    (B : ℕ) (qDecay qCost L : ℝ) :
    twoLayerTargetTwiceBalancedDoubledBaseLogCost B qCost L =
      twoLayerTargetTwiceBalancedDoubledBaseLogCost B qDecay L +
        ((B : ℝ) + 1) * (qCost - qDecay) * L := by
  have hsource :
      1 * ((1 + 1) * (B + 1)) / 2 = B + 1 := by omega
  unfold twoLayerTargetTwiceBalancedDoubledBaseLogCost
    dyadicSymmetricBaseLogCost
  rw [hsource]
  push_cast
  ring

/-- Exact main-term cancellation with distinct determinant-decay and
source-clearing exponents. -/
theorem twoLayerWeight_sub_twoLayerTargetTwiceSplitExponentBaseLogCost_eq
    (B k : ℕ) (m qDecay qCost L : ℝ) (hk : k ≤ B) :
    twoLayerWeight B k (m * L) (qDecay * L) -
        twoLayerTargetTwiceBalancedDoubledBaseLogCost B qCost L =
      twoLayerBalancedFanSurplus B k m qDecay * L -
          dyadicEndpointDoublingLogCost 1 B -
        (B : ℝ) * ((B : ℝ) + 1) * Real.log 2 -
        ((B : ℝ) + 1) * (qCost - qDecay) * L := by
  rw [twoLayerTargetTwiceBalancedDoubledBaseLogCost_change_sourceExponent,
    sub_add_eq_sub_sub,
    twoLayerWeight_sub_twoLayerTargetTwiceBalancedDoubledBaseLogCost_eq
      B k m qDecay L hk]

/-- A convenient rigorous numerical bound for the fixed source-gap
constant. -/
theorem log_15360_lt_ten : Real.log 15360 < (10 : ℝ) := by
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 15360)).2
  calc
    (15360 : ℝ) < (2.7 : ℝ) ^ 10 := by norm_num
    _ < (Real.exp 1) ^ 10 := by
      gcongr
      exact (by norm_num : (2.7 : ℝ) < 2.7182818283).trans
        Real.exp_one_gt_d9
    _ = Real.exp 10 := by
      rw [← Real.exp_nat_mul]
      norm_num

/-- In the near-square degree range, the bounded split-exponent charge adds
at most one copy of `(B+1)^2` to the previous constant `43`. -/
theorem twoLayerTargetTwiceSplitExponentFanFixedLogCost_le_fortyFour_mul_sq
    (B : ℕ) (hB : 9 ≤ B) :
    twoLayerTargetTwiceSplitExponentFanFixedLogCost B ≤
      44 * ((B : ℝ) + 1) ^ 2 := by
  have hten : (10 : ℝ) ≤ (B : ℝ) + 1 := by
    exact_mod_cast (Nat.succ_le_succ hB)
  have hgap : Real.log 15360 ≤ (B : ℝ) + 1 :=
    log_15360_lt_ten.le.trans hten
  have hextra :
      ((B : ℝ) + 1) * Real.log 15360 ≤ ((B : ℝ) + 1) ^ 2 := by
    calc
      ((B : ℝ) + 1) * Real.log 15360 ≤
          ((B : ℝ) + 1) * ((B : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hgap (by positivity)
      _ = ((B : ℝ) + 1) ^ 2 := by ring
  have hbase := twoLayerTargetTwiceFanFixedLogCost_le_fortyThree_mul_sq B
  unfold twoLayerTargetTwiceSplitExponentFanFixedLogCost
  calc
    twoLayerTargetTwiceFanFixedLogCost B +
          ((B : ℝ) + 1) * Real.log 15360 ≤
        43 * ((B : ℝ) + 1) ^ 2 + ((B : ℝ) + 1) ^ 2 :=
      add_le_add hbase hextra
    _ = 44 * ((B : ℝ) + 1) ^ 2 := by ring

/-- The unchanged growth assumption absorbs the complete split-exponent
fixed ledger. -/
theorem twoLayerTargetTwiceSplitExponentFanFixedLogCost_lt_theta_sq_div_twelve_mul_log
    (B : ℕ) (theta Y : ℝ)
    (htheta : 3 ≤ theta)
    (hBlower : theta ^ 2 ≤ (B : ℝ))
    (hBupper : (B : ℝ) < theta ^ 2 + 1)
    (hY : Real.exp (800 * theta ^ 2) < Y) :
    twoLayerTargetTwiceSplitExponentFanFixedLogCost B <
      (theta ^ 2 / 12) * Real.log Y := by
  let b : ℝ := B
  let t : ℝ := theta ^ 2
  have ht9 : 9 ≤ t := by
    dsimp [t]
    nlinarith [sq_nonneg (theta - 3)]
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht9
  have hB9 : 9 ≤ B := by
    have hB9real : (9 : ℝ) ≤ (B : ℝ) := by
      exact ht9.trans (by simpa only [t] using hBlower)
    exact_mod_cast hB9real
  have hb0 : 0 ≤ b := by positivity
  have hdegree : 9 * (b + 1) < 11 * t := by
    dsimp [b, t]
    nlinarith
  have hsum : 0 < 11 * t + 9 * (b + 1) := by positivity
  have hproduct :
      0 < (11 * t - 9 * (b + 1)) * (11 * t + 9 * (b + 1)) :=
    mul_pos (sub_pos.mpr hdegree) hsum
  have hsquare : 81 * (b + 1) ^ 2 < 121 * t ^ 2 := by
    nlinarith
  have hcost :=
    twoLayerTargetTwiceSplitExponentFanFixedLogCost_le_fortyFour_mul_sq
      B hB9
  have hcostScaled :
      44 * (b + 1) ^ 2 < (t / 12) * (800 * t) := by
    nlinarith
  have hYpos : 0 < Y := (Real.exp_pos _).trans hY
  have hlog := Real.strictMonoOn_log (Real.exp_pos _) hYpos hY
  rw [Real.log_exp] at hlog
  have hgainLog :
      (t / 12) * (800 * t) < (t / 12) * Real.log Y :=
    mul_lt_mul_of_pos_left hlog (by positivity)
  dsimp [b, t] at hcost hcostScaled hgainLog ⊢
  exact hcost.trans_lt (hcostScaled.trans hgainLog)

/-- A lower bound for the balanced surplus and a bounded logarithmic gap
give the exact fan-rate inequality with separate exponents. -/
theorem twoLayerTargetTwiceSplitExponentFan_rate_of_balancedSurplus
    (B k : ℕ) (m qDecay qCost L gain : ℝ)
    (hk : k ≤ B) (hL : 0 ≤ L)
    (hsurplus : gain ≤ twoLayerBalancedFanSurplus B k m qDecay)
    (hgap : (qCost - qDecay) * L ≤ Real.log 15360)
    (hfixed : twoLayerTargetTwiceSplitExponentFanFixedLogCost B < gain * L) :
    twoLayerTargetTwiceBalancedDoubledBaseLogCost B qCost L +
          shearedComparableCoordinateLogLoss 1 B 2 24 +
          Real.log (Nat.factorial
            (Fintype.card (generalBidegreeGrid 1 B)) : ℝ) +
        twoLayerFanTaylorTail B *
          (Fintype.card (generalBidegreeGrid 1 B) : ℝ) <
      twoLayerWeight B k (m * L) (qDecay * L) := by
  have hsurplusL : gain * L ≤
      twoLayerBalancedFanSurplus B k m qDecay * L :=
    mul_le_mul_of_nonneg_right hsurplus hL
  have hgap' :
      ((B : ℝ) + 1) * ((qCost - qDecay) * L) ≤
        ((B : ℝ) + 1) * Real.log 15360 :=
    mul_le_mul_of_nonneg_left hgap (by positivity)
  have hid :=
    twoLayerWeight_sub_twoLayerTargetTwiceSplitExponentBaseLogCost_eq
      B k m qDecay qCost L hk
  unfold twoLayerTargetTwiceSplitExponentFanFixedLogCost
    twoLayerTargetTwiceFanFixedLogCost twoLayerFanFixedLogCost at hfixed
  nlinarith

/-- Standard balanced numerics for the determinant exponent, together with
the explicit clearing-exponent gap, imply the split-exponent exact rate. -/
theorem twoLayerTargetTwiceSplitExponentFan_rate_of_standardBalanced
    (B k : ℕ) (theta m qDecay qCost Y : ℝ)
    (htheta : 3 ≤ theta)
    (hBlower : theta ^ 2 ≤ (B : ℝ))
    (hBupper : (B : ℝ) < theta ^ 2 + 1)
    (hmlower : 9 / 10 ≤ m) (hmupper : m ≤ 1)
    (hq0 : 0 ≤ qDecay) (hq : qDecay ≤ 7 * theta / 6)
    (hdefect : (1 - m) * theta ^ 2 ≤ 1 / 50)
    (hk : k ≤ B)
    (hgap : (qCost - qDecay) * Real.log Y ≤ Real.log 15360)
    (hY : Real.exp (800 * theta ^ 2) < Y) :
    twoLayerTargetTwiceBalancedDoubledBaseLogCost B qCost (Real.log Y) +
          shearedComparableCoordinateLogLoss 1 B 2 24 +
          Real.log (Nat.factorial
            (Fintype.card (generalBidegreeGrid 1 B)) : ℝ) +
        twoLayerFanTaylorTail B *
          (Fintype.card (generalBidegreeGrid 1 B) : ℝ) <
      twoLayerWeight B k (m * Real.log Y) (qDecay * Real.log Y) := by
  have hYone : 1 < Y := by
    have hexpone : 1 < Real.exp (800 * theta ^ 2) :=
      Real.one_lt_exp_iff.mpr (by positivity)
    exact hexpone.trans hY
  have hlogY : 0 ≤ Real.log Y := (Real.log_pos hYone).le
  have hsurplus : theta ^ 2 / 12 ≤
      twoLayerBalancedFanSurplus B k m qDecay :=
    theta_sq_div_twelve_le_twoLayerBalancedFanSurplus
      B k theta m qDecay htheta hBlower hBupper hmlower hmupper
        hq0 hq hdefect
  have hfixed : twoLayerTargetTwiceSplitExponentFanFixedLogCost B <
      (theta ^ 2 / 12) * Real.log Y :=
    twoLayerTargetTwiceSplitExponentFanFixedLogCost_lt_theta_sq_div_twelve_mul_log
      B theta Y htheta hBlower hBupper hY
  exact twoLayerTargetTwiceSplitExponentFan_rate_of_balancedSurplus
    B k m qDecay qCost (Real.log Y) (theta ^ 2 / 12)
      hk hlogY hsurplus hgap hfixed

end

end PellPaper
