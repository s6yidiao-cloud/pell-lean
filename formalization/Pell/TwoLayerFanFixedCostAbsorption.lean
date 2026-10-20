import Pell.TwoLayerBalancedFanRate
import Mathlib.Tactic

/-!
# Finite-threshold absorption of the exact two-layer fan cost

This module discharges the remaining fixed logarithmic cost in the balanced
two-layer fan rate.  The first theorem is an exact threshold wrapper: a
positive gain absorbs the cost as soon as `Y` is strictly larger than the
exponential of `cost / gain`.  A second bound collapses the complete ledger
to `44 * (B + 1)^2`, giving a threshold with no factorial or auxiliary
definitions left in it.
-/

namespace PellPaper

noncomputable section

/-- At source degree one, the full fixed-cost ledger has this elementary
closed form.  In particular, the row count is exactly `2 * (B + 1)` and no
asymptotic replacement is used. -/
theorem twoLayerFanFixedLogCost_eq_explicit (B : ℕ) :
    twoLayerFanFixedLogCost B =
      ((B : ℝ) + 1) ^ 2 * Real.log 4 +
        ((B : ℝ) + 1) * (1 + 2 * (B : ℝ)) * Real.log 2 +
          (B : ℝ) * ((B : ℝ) + 1) * Real.log 24 +
            Real.log ((2 * (B + 1)).factorial : ℝ) +
              (1 + 3 * (B : ℝ)) * (2 * ((B : ℝ) + 1)) := by
  have hsource :
      1 * ((1 + 1) * (B + 1)) / 2 = B + 1 := by omega
  have htarget :
      B * ((1 + 1) * (B + 1)) / 2 = B * (B + 1) := by
    calc
      B * ((1 + 1) * (B + 1)) / 2 =
          (B * (B + 1)) * 2 / 2 := by
        congr 1
        ring
      _ = B * (B + 1) :=
        Nat.mul_div_left _ (by norm_num : 0 < 2)
  have hcoordinate :
      ((1 + 1) * (B + 1) * (1 + 2 * B)) / 2 =
        (B + 1) * (1 + 2 * B) := by
    calc
      ((1 + 1) * (B + 1) * (1 + 2 * B)) / 2 =
          ((B + 1) * (1 + 2 * B)) * 2 / 2 := by
        congr 1
        ring
      _ = (B + 1) * (1 + 2 * B) :=
        Nat.mul_div_left _ (by norm_num : 0 < 2)
  have hcard :
      Fintype.card (generalBidegreeGrid 1 B) = 2 * (B + 1) := by
    calc
      Fintype.card (generalBidegreeGrid 1 B) =
          (generalBidegreeGrid 1 B).card := Fintype.card_coe _
      _ = (1 + 1) * (B + 1) := card_generalBidegreeGrid 1 B
      _ = 2 * (B + 1) := by omega
  unfold twoLayerFanFixedLogCost dyadicEndpointDoublingLogCost
    shearedComparableCoordinateLogLoss twoLayerFanTaylorTail
  rw [hsource, htarget, hcoordinate, hcard]
  push_cast
  ring

/-- A direct finite bound for the complete fan ledger.  It is deliberately
coarse, but is uniform for every natural `B` and eliminates the factorial. -/
theorem twoLayerFanFixedLogCost_le_fortyFour_mul_sq (B : ℕ) :
    twoLayerFanFixedLogCost B ≤ 44 * ((B : ℝ) + 1) ^ 2 := by
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

/-- Exact exponential threshold for absorbing the fixed ledger into an
arbitrary positive logarithmic gain. -/
theorem twoLayerFanFixedLogCost_lt_gain_mul_log_of_exp_div_lt
    (B : ℕ) (gain Y : ℝ) (hgain : 0 < gain)
    (hY : Real.exp (twoLayerFanFixedLogCost B / gain) < Y) :
    twoLayerFanFixedLogCost B < gain * Real.log Y := by
  have hYpos : 0 < Y := (Real.exp_pos _).trans hY
  have hlog := Real.strictMonoOn_log (Real.exp_pos _) hYpos hY
  rw [Real.log_exp] at hlog
  exact (div_lt_iff₀ hgain).mp hlog |>.trans_eq (mul_comm _ _)

/-- The exact threshold specialized to the balanced gain `theta^2 / 12`.
The standard regime `theta >= 3` supplies its positivity. -/
theorem twoLayerFanFixedLogCost_lt_theta_sq_div_twelve_mul_log_of_exp_div_lt
    (B : ℕ) (theta Y : ℝ) (htheta : 3 ≤ theta)
    (hY :
      Real.exp (twoLayerFanFixedLogCost B / (theta ^ 2 / 12)) < Y) :
    twoLayerFanFixedLogCost B <
      (theta ^ 2 / 12) * Real.log Y := by
  apply twoLayerFanFixedLogCost_lt_gain_mul_log_of_exp_div_lt
  · positivity
  · exact hY

/-- A completely elementary sufficient threshold for the same balanced
gain.  It is compatible with the usual choice `B` near `theta^2` and has no
factorial or named fixed-cost term in its premise. -/
theorem twoLayerFanFixedLogCost_lt_theta_sq_div_twelve_mul_log_of_exp_sq_lt
    (B : ℕ) (theta Y : ℝ) (htheta : 3 ≤ theta)
    (hY :
      Real.exp (528 * ((B : ℝ) + 1) ^ 2 / theta ^ 2) < Y) :
    twoLayerFanFixedLogCost B <
      (theta ^ 2 / 12) * Real.log Y := by
  have hthetaSq : 0 < theta ^ 2 := by positivity
  have hYpos : 0 < Y := (Real.exp_pos _).trans hY
  have hlog := Real.strictMonoOn_log (Real.exp_pos _) hYpos hY
  rw [Real.log_exp] at hlog
  have hcost := twoLayerFanFixedLogCost_le_fortyFour_mul_sq B
  have hscale :
      44 * ((B : ℝ) + 1) ^ 2 <
        (theta ^ 2 / 12) * Real.log Y := by
    have hdiv :
        44 * ((B : ℝ) + 1) ^ 2 / (theta ^ 2 / 12) < Real.log Y := by
      calc
        44 * ((B : ℝ) + 1) ^ 2 / (theta ^ 2 / 12) =
            528 * ((B : ℝ) + 1) ^ 2 / theta ^ 2 := by
          field_simp
          ring
        _ < Real.log Y := hlog
    exact ((div_lt_iff₀ (by positivity : 0 < theta ^ 2 / 12)).mp hdiv).trans_eq
      (mul_comm _ _)
  exact hcost.trans_lt hscale

/-- In the standard near-square degree window, the previous threshold is
implied by the particularly simple condition `exp (800 * theta^2) < Y`.
The upper degree hypothesis is the one used by the balanced fan numerics. -/
theorem twoLayerFanFixedLogCost_lt_theta_sq_div_twelve_mul_log_of_nearSquare
    (B : ℕ) (theta Y : ℝ)
    (htheta : 3 ≤ theta)
    (hBupper : (B : ℝ) < theta ^ 2 + 1)
    (hY : Real.exp (800 * theta ^ 2) < Y) :
    twoLayerFanFixedLogCost B <
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
  have hcost := twoLayerFanFixedLogCost_le_fortyFour_mul_sq B
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

end

end PellPaper

