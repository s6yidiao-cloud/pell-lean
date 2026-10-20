import Pell.SmallRootBudget
import Pell.SmallSquarePartDyadicCover

/-!
# Natural thresholds for the small-root budget

The square-part reductions index roots by natural numbers, whereas the
manuscript's small-root threshold is a real power of the dyadic scale.  This
module supplies the elementary cast bridge needed to apply the real-power
budget uniformly to every root below a natural threshold.
-/

namespace PellPaper

/-- A natural root below a threshold which itself lies below the manuscript's
real-power threshold satisfies the square-part scale budget. -/
theorem squarePartScaleBudget_of_nat_lt_rpow_threshold
    {theta lam : ℝ} {Y S s : ℕ}
    (htheta : 0 ≤ theta) (hY : 1 ≤ Y)
    (hS : (S : ℝ) ≤ (Y : ℝ) ^ (lam / (theta + 1)))
    (hsS : s < S) (hlam : lam ≤ (1 : ℝ) / 8) :
    squarePartScaleBudget theta Y s := by
  unfold squarePartScaleBudget
  apply rpow_le_rpow_quarter_of_small_root_budget_of_le_one_eighth
    htheta (by exact_mod_cast hY) (Nat.cast_nonneg _)
  · have hs : (s : ℝ) ≤ (S : ℝ) := by
      exact_mod_cast Nat.le_of_lt hsS
    exact hs.trans hS
  · exact hlam

/-- The preceding natural threshold supplies the budget hypothesis for every
positive root occurring in the finite interval `Ico 1 S`. -/
theorem all_squarePartScaleBudgets_of_nat_rpow_threshold
    {theta lam : ℝ} {Y S : ℕ}
    (htheta : 0 ≤ theta) (hY : 1 ≤ Y)
    (hS : (S : ℝ) ≤ (Y : ℝ) ^ (lam / (theta + 1)))
    (hlam : lam ≤ (1 : ℝ) / 8) :
    ∀ s : ℕ, 1 ≤ s → s < S → squarePartScaleBudget theta Y s := by
  intro s _ hsS
  exact squarePartScaleBudget_of_nat_lt_rpow_threshold
    htheta hY hS hsS hlam

end PellPaper
