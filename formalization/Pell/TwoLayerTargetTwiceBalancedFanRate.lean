import Pell.TwoLayerFanFixedCostAbsorption
import Pell.TwoLayerBalancedFanNumerics
import Pell.DyadicSymmetricCostBudget
import Mathlib.Tactic

/-!
# Exact two-layer fan rate with target product at most twice the base scale

An actual global dyadic factor box supplies `UV < 2Y`, rather than the
stronger normalization `UV <= Y`.  This module retains `L = log Y` and
records the extra target factor two exactly.  Its logarithmic contribution
is `B(B+1) log 2`; the standard `exp (800 theta^2) < Y` threshold still
absorbs the enlarged fixed ledger.
-/

namespace PellPaper

noncomputable section

/-- The exact doubled-endpoint clearing ledger when
`DE <= Y^(q-1/2)` and `UV <= 2Y`, with `L = log Y`. -/
def twoLayerTargetTwiceBalancedDoubledBaseLogCost
    (B : ℕ) (q L : ℝ) : ℝ :=
  dyadicSymmetricBaseLogCost 1 B
    ((q - 1 / 2) * L + Real.log 4)
    (L + Real.log 2 + Real.log 4)

/-- The complete fixed fan ledger after adjoining the target factor-two
cost.  The original ledger already contains both endpoint-doubling costs. -/
def twoLayerTargetTwiceFanFixedLogCost (B : ℕ) : ℝ :=
  twoLayerFanFixedLogCost B +
    (B : ℝ) * ((B : ℝ) + 1) * Real.log 2

/-- Raising the target product allowance from `Y` to `2Y` adds exactly
`B(B+1) log 2` to the source-degree-one clearing ledger. -/
theorem twoLayerTargetTwiceBalancedDoubledBaseLogCost_eq
    (B : ℕ) (q L : ℝ) :
    twoLayerTargetTwiceBalancedDoubledBaseLogCost B q L =
      twoLayerBalancedDoubledBaseLogCost B q L +
        (B : ℝ) * ((B : ℝ) + 1) * Real.log 2 := by
  have htarget :
      B * ((1 + 1) * (B + 1)) / 2 = B * (B + 1) := by
    calc
      B * ((1 + 1) * (B + 1)) / 2 =
          (B * (B + 1)) * 2 / 2 := by
        congr 1
        ring
      _ = B * (B + 1) :=
        Nat.mul_div_left _ (by norm_num : 0 < 2)
  unfold twoLayerTargetTwiceBalancedDoubledBaseLogCost
    twoLayerBalancedDoubledBaseLogCost dyadicSymmetricBaseLogCost
  rw [htarget]
  push_cast
  ring

/-- Exact main-term cancellation with the sole new fixed contribution
displayed separately. -/
theorem twoLayerWeight_sub_twoLayerTargetTwiceBalancedDoubledBaseLogCost_eq
    (B k : ℕ) (m q L : ℝ) (hk : k ≤ B) :
    twoLayerWeight B k (m * L) (q * L) -
        twoLayerTargetTwiceBalancedDoubledBaseLogCost B q L =
      twoLayerBalancedFanSurplus B k m q * L -
          dyadicEndpointDoublingLogCost 1 B -
        (B : ℝ) * ((B : ℝ) + 1) * Real.log 2 := by
  rw [twoLayerTargetTwiceBalancedDoubledBaseLogCost_eq,
    sub_add_eq_sub_sub,
    twoLayerWeight_sub_twoLayerBalancedDoubledBaseLogCost_eq B k m q L hk]

/-- The original fixed fan ledger admits the sharper elementary constant
`42`; the earlier constant `44` is not needed. -/
theorem twoLayerFanFixedLogCost_le_fortyTwo_mul_sq (B : ℕ) :
    twoLayerFanFixedLogCost B ≤ 42 * ((B : ℝ) + 1) ^ 2 := by
  let b : ℝ := B
  let n : ℕ := 2 * (B + 1)
  have hb0 : 0 ≤ b := by positivity
  have hnpos : 0 < n := by
    dsimp [n]
    omega
  have hfacNat : n.factorial ≤ n ^ n := Nat.factorial_le_pow n
  have hfacReal : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by
    exact_mod_cast hfacNat
  have hlogFacPow : Real.log (n.factorial : ℝ) ≤
      Real.log ((n : ℝ) ^ n) := by
    exact Real.log_le_log (by positivity) hfacReal
  have hlogFac : Real.log (n.factorial : ℝ) ≤ (n : ℝ) ^ 2 := by
    rw [Real.log_pow] at hlogFacPow
    have hlogn : Real.log (n : ℝ) ≤ (n : ℝ) :=
      Real.log_le_self (by positivity)
    have hn0 : 0 ≤ (n : ℝ) := by positivity
    nlinarith
  have hlog4 : Real.log 4 ≤ (4 : ℝ) :=
    Real.log_le_self (by norm_num)
  have hlog2 : Real.log 2 ≤ (2 : ℝ) :=
    Real.log_le_self (by norm_num)
  have hlog24 : Real.log 24 ≤ (24 : ℝ) :=
    Real.log_le_self (by norm_num)
  have hexplicit := twoLayerFanFixedLogCost_eq_explicit B
  dsimp [b, n] at hb0 hlogFac hexplicit ⊢
  rw [hexplicit]
  norm_num at hlogFac
  nlinarith [mul_nonneg hb0 hb0]

/-- The target factor-two correction enlarges the sharper base ledger by at
most one further copy of `(B+1)^2`. -/
theorem twoLayerTargetTwiceFanFixedLogCost_le_fortyThree_mul_sq (B : ℕ) :
    twoLayerTargetTwiceFanFixedLogCost B ≤
      43 * ((B : ℝ) + 1) ^ 2 := by
  let b : ℝ := B
  have hb0 : 0 ≤ b := by positivity
  have hlog2 : Real.log 2 ≤ (1 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hcoefficient : 0 ≤ b * (b + 1) := by positivity
  have hextraOne :
      b * (b + 1) * Real.log 2 ≤ b * (b + 1) := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hlog2 hcoefficient
  have hextra :
      b * (b + 1) * Real.log 2 ≤ (b + 1) ^ 2 := by
    calc
      b * (b + 1) * Real.log 2 ≤ b * (b + 1) := hextraOne
      _ ≤ (b + 1) ^ 2 := by nlinarith
  have hbase := twoLayerFanFixedLogCost_le_fortyTwo_mul_sq B
  dsimp [b] at hb0 hextra ⊢
  unfold twoLayerTargetTwiceFanFixedLogCost
  calc
    twoLayerFanFixedLogCost B +
          (B : ℝ) * ((B : ℝ) + 1) * Real.log 2 ≤
        42 * ((B : ℝ) + 1) ^ 2 + ((B : ℝ) + 1) ^ 2 :=
      add_le_add hbase hextra
    _ = 43 * ((B : ℝ) + 1) ^ 2 := by ring

/-- The standard near-square degree window and
`exp (800 theta^2) < Y` absorb the widened fixed ledger into the unchanged
balanced gain `theta^2/12`. -/
theorem twoLayerTargetTwiceFanFixedLogCost_lt_theta_sq_div_twelve_mul_log_of_nearSquare
    (B : ℕ) (theta Y : ℝ)
    (htheta : 3 ≤ theta)
    (hBupper : (B : ℝ) < theta ^ 2 + 1)
    (hY : Real.exp (800 * theta ^ 2) < Y) :
    twoLayerTargetTwiceFanFixedLogCost B <
      (theta ^ 2 / 12) * Real.log Y := by
  let b : ℝ := B
  let t : ℝ := theta ^ 2
  have ht9 : 9 ≤ t := by
    dsimp [t]
    nlinarith [sq_nonneg (theta - 3)]
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht9
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
  have hcost := twoLayerTargetTwiceFanFixedLogCost_le_fortyThree_mul_sq B
  have hcostScaled :
      43 * (b + 1) ^ 2 < (t / 12) * (800 * t) := by
    nlinarith
  have hYpos : 0 < Y := (Real.exp_pos _).trans hY
  have hlog := Real.strictMonoOn_log (Real.exp_pos _) hYpos hY
  rw [Real.log_exp] at hlog
  have hgainLog :
      (t / 12) * (800 * t) < (t / 12) * Real.log Y :=
    mul_lt_mul_of_pos_left hlog (by positivity)
  dsimp [b, t] at hcost hcostScaled hgainLog ⊢
  exact hcost.trans_lt (hcostScaled.trans hgainLog)

/-- A balanced-surplus lower bound and absorption of the widened fixed
ledger imply the exact fan-rate inequality for the target-twice ledger. -/
theorem twoLayerTargetTwiceFan_rate_of_balancedSurplus_and_fixedCost
    (B k : ℕ) (m q L gain : ℝ)
    (hk : k ≤ B) (hL : 0 ≤ L)
    (hsurplus : gain ≤ twoLayerBalancedFanSurplus B k m q)
    (hfixed : twoLayerTargetTwiceFanFixedLogCost B < gain * L) :
    twoLayerTargetTwiceBalancedDoubledBaseLogCost B q L +
          shearedComparableCoordinateLogLoss 1 B 2 24 +
          Real.log (Nat.factorial
            (Fintype.card (generalBidegreeGrid 1 B)) : ℝ) +
        twoLayerFanTaylorTail B *
          (Fintype.card (generalBidegreeGrid 1 B) : ℝ) <
      twoLayerWeight B k (m * L) (q * L) := by
  have hsurplusL : gain * L ≤
      twoLayerBalancedFanSurplus B k m q * L :=
    mul_le_mul_of_nonneg_right hsurplus hL
  have hid :=
    twoLayerWeight_sub_twoLayerTargetTwiceBalancedDoubledBaseLogCost_eq
      B k m q L hk
  unfold twoLayerTargetTwiceFanFixedLogCost twoLayerFanFixedLogCost at hfixed
  linarith

/-- The standard balanced numerical assumptions give the final exact fan
rate with `L = log Y`, even when the target product is allowed up to `2Y`. -/
theorem twoLayerTargetTwiceFan_rate_of_standardBalanced
    (B k : ℕ) (theta m q Y : ℝ)
    (htheta : 3 ≤ theta)
    (hBlower : theta ^ 2 ≤ (B : ℝ))
    (hBupper : (B : ℝ) < theta ^ 2 + 1)
    (hmlower : 9 / 10 ≤ m) (hmupper : m ≤ 1)
    (hq0 : 0 ≤ q) (hq : q ≤ 7 * theta / 6)
    (hdefect : (1 - m) * theta ^ 2 ≤ 1 / 50)
    (hk : k ≤ B)
    (hY : Real.exp (800 * theta ^ 2) < Y) :
    twoLayerTargetTwiceBalancedDoubledBaseLogCost B q (Real.log Y) +
          shearedComparableCoordinateLogLoss 1 B 2 24 +
          Real.log (Nat.factorial
            (Fintype.card (generalBidegreeGrid 1 B)) : ℝ) +
        twoLayerFanTaylorTail B *
          (Fintype.card (generalBidegreeGrid 1 B) : ℝ) <
      twoLayerWeight B k (m * Real.log Y) (q * Real.log Y) := by
  have hYone : 1 < Y := by
    have hexpone : 1 < Real.exp (800 * theta ^ 2) :=
      Real.one_lt_exp_iff.mpr (by positivity)
    exact hexpone.trans hY
  have hlogY : 0 ≤ Real.log Y := (Real.log_pos hYone).le
  have hsurplus : theta ^ 2 / 12 ≤
      twoLayerBalancedFanSurplus B k m q :=
    theta_sq_div_twelve_le_twoLayerBalancedFanSurplus
      B k theta m q htheta hBlower hBupper hmlower hmupper hq0 hq hdefect
  have hfixed : twoLayerTargetTwiceFanFixedLogCost B <
      (theta ^ 2 / 12) * Real.log Y :=
    twoLayerTargetTwiceFanFixedLogCost_lt_theta_sq_div_twelve_mul_log_of_nearSquare
      B theta Y htheta hBupper hY
  exact twoLayerTargetTwiceFan_rate_of_balancedSurplus_and_fixedCost
    B k m q (Real.log Y) (theta ^ 2 / 12) hk hlogY hsurplus hfixed

/-- Endpoint product bounds `DE <= Y^(q-1/2)` and `UV <= 2Y` give exactly
the widened doubled-endpoint clearing-cost premise. -/
theorem doubledDyadicSymmetricCost_le_exp_of_sourceRpow_targetTwice
    (B : ℕ) (i : ℕ × ℕ × ℕ × ℕ) (Y q : ℝ)
    (hY : 0 < Y)
    (hDE :
      ((2 ^ i.1 : ℕ) : ℝ) * ((2 ^ i.2.1 : ℕ) : ℝ) ≤
        Y ^ (q - 1 / 2))
    (hUV :
      ((2 ^ i.2.2.1 : ℕ) : ℝ) * ((2 ^ i.2.2.2 : ℕ) : ℝ) ≤
        2 * Y) :
    ((2 * ((2 ^ i.1 : ℕ) : ℝ)) *
        (2 * ((2 ^ i.2.1 : ℕ) : ℝ))) ^
          (1 * ((1 + 1) * (B + 1)) / 2) *
      ((2 * ((2 ^ i.2.2.1 : ℕ) : ℝ)) *
        (2 * ((2 ^ i.2.2.2 : ℕ) : ℝ))) ^
          (B * ((1 + 1) * (B + 1)) / 2) ≤
      Real.exp
        (twoLayerTargetTwiceBalancedDoubledBaseLogCost B q (Real.log Y)) := by
  have hDEexp :
      ((2 ^ i.1 : ℕ) : ℝ) * ((2 ^ i.2.1 : ℕ) : ℝ) ≤
        Real.exp ((q - 1 / 2) * Real.log Y) :=
    endpointProduct_le_exp_of_le_rpow Y
      (((2 ^ i.1 : ℕ) : ℝ) * ((2 ^ i.2.1 : ℕ) : ℝ))
      (q - 1 / 2) hY hDE
  have hUVexp :
      ((2 ^ i.2.2.1 : ℕ) : ℝ) * ((2 ^ i.2.2.2 : ℕ) : ℝ) ≤
        Real.exp (Real.log Y + Real.log 2) := by
    calc
      ((2 ^ i.2.2.1 : ℕ) : ℝ) * ((2 ^ i.2.2.2 : ℕ) : ℝ) ≤
          2 * Y := hUV
      _ = Real.exp (Real.log Y + Real.log 2) := by
        rw [Real.exp_add, Real.exp_log hY,
          Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        ring
  simpa only [twoLayerTargetTwiceBalancedDoubledBaseLogCost] using
    doubledDyadicSymmetricCost_le_exp_of_endpointLogBounds
      1 B i ((q - 1 / 2) * Real.log Y) (Real.log Y + Real.log 2)
      hDEexp hUVexp

end

end PellPaper
