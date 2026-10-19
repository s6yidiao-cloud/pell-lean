import Pell.TwoLayerFanDeterminantStrictness
import Pell.DyadicSymmetricCostBudget

/-!
# The scalar balanced surplus behind the exact two-layer fan rate

This module separates the main logarithmic cancellation in the balanced
determinant method from all finite-degree costs.  At source degree one, the
exact two-layer weight minus the doubled dyadic source/target clearing cost
is the manuscript's balanced fan surplus times the ambient logarithm, less
only the explicitly named endpoint-doubling cost.
-/

namespace PellPaper

noncomputable section

/-- The exact balanced-box surplus after subtracting the source and target
radial clearing costs from the two-layer weight. -/
def twoLayerBalancedFanSurplus
    (B k : ℕ) (m q : ℝ) : ℝ :=
  ((B : ℝ) + 1) / 2 -
    (q * (k : ℝ) - m * (k : ℝ) ^ 2) -
      (1 - m) * (B : ℝ) * ((B : ℝ) + 1)

/-- The exact doubled-endpoint clearing-cost ledger in the balanced regime
`DE <= Y^(q-1/2)` and `UV <= Y`. -/
def twoLayerBalancedDoubledBaseLogCost
    (B : ℕ) (q L : ℝ) : ℝ :=
  dyadicSymmetricBaseLogCost 1 B
    ((q - 1 / 2) * L + Real.log 4)
    (L + Real.log 4)

/-- All finite logarithmic terms in the exact fan strictness comparison:
endpoint doubling, the fixed comparable-coordinate loss, the factorial,
and the exact Taylor tail. -/
def twoLayerFanFixedLogCost (B : ℕ) : ℝ :=
  dyadicEndpointDoublingLogCost 1 B +
    shearedComparableCoordinateLogLoss 1 B 2 24 +
      Real.log (Nat.factorial
        (Fintype.card (generalBidegreeGrid 1 B)) : ℝ) +
        twoLayerFanTaylorTail B *
          (Fintype.card (generalBidegreeGrid 1 B) : ℝ)

/-- Exact main-term cancellation for the balanced two-layer determinant. -/
theorem twoLayerWeight_sub_twoLayerBalancedDoubledBaseLogCost_eq
    (B k : ℕ) (m q L : ℝ) (hk : k ≤ B) :
    twoLayerWeight B k (m * L) (q * L) -
        twoLayerBalancedDoubledBaseLogCost B q L =
      twoLayerBalancedFanSurplus B k m q * L -
        dyadicEndpointDoublingLogCost 1 B := by
  have hsource :
      1 * ((1 + 1) * (B + 1)) / 2 = B + 1 := by omega
  have htarget :
      B * ((1 + 1) * (B + 1)) / 2 = B * (B + 1) := by
    change B * (2 * (B + 1)) / 2 = B * (B + 1)
    calc
      B * (2 * (B + 1)) / 2 =
          ((B * (B + 1)) * 2) / 2 := by
            congr 1
            ring
      _ = B * (B + 1) :=
        Nat.mul_div_left (B * (B + 1)) (by norm_num : 0 < 2)
  rw [twoLayerWeight_eq B k hk]
  unfold twoLayerBalancedDoubledBaseLogCost
    twoLayerBalancedFanSurplus dyadicSymmetricBaseLogCost
    dyadicEndpointDoublingLogCost
  rw [hsource, htarget]
  push_cast
  ring

/-- Once the finite logarithmic cost is smaller than any lower bound for
the balanced surplus, the exact fan strict-rate inequality follows. -/
theorem twoLayerFan_rate_of_balancedSurplus_and_fixedCost
    (B k : ℕ) (m q L gain : ℝ)
    (hk : k ≤ B) (hL : 0 ≤ L)
    (hsurplus : gain ≤ twoLayerBalancedFanSurplus B k m q)
    (hfixed : twoLayerFanFixedLogCost B < gain * L) :
    twoLayerBalancedDoubledBaseLogCost B q L +
          shearedComparableCoordinateLogLoss 1 B 2 24 +
          Real.log (Nat.factorial
            (Fintype.card (generalBidegreeGrid 1 B)) : ℝ) +
        twoLayerFanTaylorTail B *
          (Fintype.card (generalBidegreeGrid 1 B) : ℝ) <
      twoLayerWeight B k (m * L) (q * L) := by
  have hsurplusL : gain * L ≤
      twoLayerBalancedFanSurplus B k m q * L :=
    mul_le_mul_of_nonneg_right hsurplus hL
  have hid := twoLayerWeight_sub_twoLayerBalancedDoubledBaseLogCost_eq
    B k m q L hk
  unfold twoLayerFanFixedLogCost at hfixed
  linarith

/-- The elementary square-completion inequality controlling the chosen fan
index.  It is valid for every real `k`, hence in particular for the cast of
an integer nearest to `q/(2m)`. -/
theorem q_mul_sub_m_mul_sq_le_sq_div_four
    (m q x : ℝ) (hm : 0 < m) :
    q * x - m * x ^ 2 ≤ q ^ 2 / (4 * m) := by
  apply (le_div_iff₀ (by positivity : 0 < 4 * m)).mpr
  nlinarith [sq_nonneg (2 * m * x - q)]

/-- Replacing the discrete fan-index loss by its completed-square maximum
gives the standard lower bound for the balanced surplus. -/
theorem twoLayerBalancedFanSurplus_lower_bound
    (B k : ℕ) (m q : ℝ) (hm : 0 < m) :
    ((B : ℝ) + 1) / 2 - q ^ 2 / (4 * m) -
        (1 - m) * (B : ℝ) * ((B : ℝ) + 1) ≤
      twoLayerBalancedFanSurplus B k m q := by
  have hquad := q_mul_sub_m_mul_sq_le_sq_div_four m q (k : ℝ) hm
  unfold twoLayerBalancedFanSurplus
  linarith

end

end PellPaper
