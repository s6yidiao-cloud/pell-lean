import Pell.ShearedLocalCoordinateCostComparability
import Pell.ShearedDeterminantStrictness

/-!
# Absorbing comparable local-coordinate losses in the sheared rate

In `L:sheared` of `main.tex`, the comparisons `s₀ \asymp D / E` and
`(D / E)² \asymp V / U` introduce fixed dyadic constants.  The finite
bookkeeping in `ShearedLocalCoordinateCostComparability` keeps these as the
explicit factors `c^K * k^L`.  This module records their exact logarithmic
cost and the elementary ``sufficiently large `Y`'' step which absorbs that
cost into a strict determinant-rate budget.

It does not prove the local comparisons, the determinant decay, or a
rank-deficit lower bound.  Those remain separate source-specific inputs.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- The logarithm of the two explicit comparison losses in the sheared
local-coordinate cost.  The exponents are precisely those in
`sheared_dyadic_center_denominator_scale_le_of_comparableScale`. -/
def shearedComparableCoordinateLogLoss (A B : ℕ) (c k : ℝ) : ℝ :=
  ((((A + 1) * (B + 1) * (A + 2 * B)) / 2 : ℕ) : ℝ) * Real.log c +
    ((B * ((A + 1) * (B + 1)) / 2 : ℕ) : ℝ) * Real.log k

/-- For positive comparison constants, exponentiating the displayed
logarithmic loss recovers exactly the finite `c`- and `k`-powers. -/
theorem exp_shearedComparableCoordinateLogLoss
    (A B : ℕ) {c k : ℝ} (hc : 0 < c) (hk : 0 < k) :
    Real.exp (shearedComparableCoordinateLogLoss A B c k) =
      c ^ (((A + 1) * (B + 1) * (A + 2 * B)) / 2) *
        k ^ (B * ((A + 1) * (B + 1)) / 2) := by
  unfold shearedComparableCoordinateLogLoss
  rw [Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul,
    Real.exp_log hc, Real.exp_log hk]

/-- The comparable local-coordinate bound has exponential cost equal to the
symmetric dyadic cost plus the explicit logarithmic `c`/`k` loss.  This is a
bridge to the `hcost` hypothesis in the strict determinant endpoint. -/
theorem abs_rowDenominator_center_le_expCost_of_comparableScale_logLoss
    {ι : Type*} [Fintype ι]
    (A B : ℕ) (e u : ι → ℝ) (s D E U V c k baseCost : ℝ)
    (hcard : Fintype.card ι = (A + 1) * (B + 1))
    (hD : 0 ≤ D) (hE : 0 < E) (hU : 0 < U) (hV : 0 ≤ V)
    (hc : 0 < c) (hk : 0 < k)
    (he : ∀ i, |e i| ≤ E) (hu : ∀ i, |u i| ≤ U)
    (hs : |s| ≤ c * (D / E))
    (hscale : (D / E) ^ 2 ≤ k * (V / U))
    (hbaseCost :
      (D * E) ^ (A * ((A + 1) * (B + 1)) / 2) *
          (U * V) ^ (B * ((A + 1) * (B + 1)) / 2) ≤ Real.exp baseCost) :
    |(∏ i, e i ^ A * u i ^ B) *
        s ^ (((A + 1) * (B + 1) * (A + 2 * B)) / 2)| ≤
      Real.exp (baseCost + shearedComparableCoordinateLogLoss A B c k) := by
  have hloss := exp_shearedComparableCoordinateLogLoss A B hc hk
  calc
    |(∏ i, e i ^ A * u i ^ B) *
        s ^ (((A + 1) * (B + 1) * (A + 2 * B)) / 2)| ≤
        c ^ (((A + 1) * (B + 1) * (A + 2 * B)) / 2) *
          k ^ (B * ((A + 1) * (B + 1)) / 2) *
            (D * E) ^ (A * ((A + 1) * (B + 1)) / 2) *
            (U * V) ^ (B * ((A + 1) * (B + 1)) / 2) :=
      abs_rowDenominator_center_le_shearedDyadicCost_of_comparableScale
        A B e u s D E U V c k hcard hD hE hU hV hc.le hk.le he hu hs hscale
    _ ≤ (c ^ (((A + 1) * (B + 1) * (A + 2 * B)) / 2) *
          k ^ (B * ((A + 1) * (B + 1)) / 2)) * Real.exp baseCost := by
      calc
        c ^ (((A + 1) * (B + 1) * (A + 2 * B)) / 2) *
              k ^ (B * ((A + 1) * (B + 1)) / 2) *
            (D * E) ^ (A * ((A + 1) * (B + 1)) / 2) *
            (U * V) ^ (B * ((A + 1) * (B + 1)) / 2) =
            (c ^ (((A + 1) * (B + 1) * (A + 2 * B)) / 2) *
              k ^ (B * ((A + 1) * (B + 1)) / 2)) *
              ((D * E) ^ (A * ((A + 1) * (B + 1)) / 2) *
                (U * V) ^ (B * ((A + 1) * (B + 1)) / 2)) := by ring
        _ ≤ (c ^ (((A + 1) * (B + 1) * (A + 2 * B)) / 2) *
              k ^ (B * ((A + 1) * (B + 1)) / 2)) * Real.exp baseCost := by
          apply mul_le_mul_of_nonneg_left hbaseCost
          positivity
    _ = Real.exp (baseCost + shearedComparableCoordinateLogLoss A B c k) := by
      rw [← hloss, ← Real.exp_add]
      congr 1
      ring

/-- A chosen positive logarithmic slack absorbs the fixed comparable
local-coordinate loss once `Y` exceeds the explicit exponential threshold.
The conclusion has exactly the strict-rate shape used by
`ShearedDeterminantStrictness`, with `baseCost + loss` as its cost.

For a fixed-degree source application, `A`, `B`, `c`, `k`, and the positive
slack are fixed before `Y`, so the threshold is independent of `Y`.  This
does not by itself cover a growing-degree uniform regime.  Obtaining the
base rate (including any other source `O_{A,B}(H)` terms) and the determinant
rank deficit is intentionally outside this lemma. -/
theorem strict_sheared_rate_of_comparableCoordinateLoss_absorbed
    {n : Type*} [Fintype n]
    (A B : ℕ) (c k baseCost tail W slack Y : ℝ)
    (hslack : 0 < slack)
    (hthreshold :
      Real.exp (shearedComparableCoordinateLogLoss A B c k / slack) ≤ Y)
    (hbaseRate :
      baseCost + slack * Real.log Y +
          Real.log (Nat.factorial (Fintype.card n) : ℝ) +
          tail * (Fintype.card n : ℝ) < W) :
    (baseCost + shearedComparableCoordinateLogLoss A B c k) +
        Real.log (Nat.factorial (Fintype.card n) : ℝ) +
        tail * (Fintype.card n : ℝ) < W := by
  have hYpos : 0 < Y := lt_of_lt_of_le (Real.exp_pos _) hthreshold
  have hratio : shearedComparableCoordinateLogLoss A B c k / slack ≤ Real.log Y := by
    apply (Real.exp_le_exp).mp
    rw [Real.exp_log hYpos]
    exact hthreshold
  have hloss : shearedComparableCoordinateLogLoss A B c k ≤ slack * Real.log Y := by
    calc
      shearedComparableCoordinateLogLoss A B c k ≤ Real.log Y * slack :=
        (div_le_iff₀ hslack).mp hratio
      _ = slack * Real.log Y := by ring
  linarith

end

end PellPaper
