import Pell.Main3UnbalancedEnlargedActiveDyadicSplit
import Pell.Main3BalancedDyadicScaleCount
import Mathlib.Tactic

/-!
# Cardinality of the enlarged main3 unbalanced dyadic index families

This file counts only the finite parameter families.  It records injectivity
of the binary endpoint map and bounds the active, direct, and large-analytic
families by the literal four choices of signed shift, fewer than `R` choices
of the small factor, and the two binary scale counts.  No point-counting
estimate is used.
-/

namespace PellPaper

noncomputable section

/-- Binary powers do not collide, so the endpoint image has exactly the
cardinality of its scale range. -/
theorem card_dyadicLowerEndpoints (H : ℕ) :
    (dyadicLowerEndpoints H).card = dyadicScaleCount H := by
  classical
  calc
    (dyadicLowerEndpoints H).card =
        (Finset.range (dyadicScaleCount H)).card := by
      apply Finset.card_image_iff.mpr
      exact (Nat.pow_right_injective (by norm_num : 2 ≤ 2)).injOn
    _ = dyadicScaleCount H := Finset.card_range _

/-- The signed difference family has its literal four elements. -/
theorem card_signedDyadicDifferenceValues :
    signedDyadicDifferenceValues.card = 4 := by
  norm_num [signedDyadicDifferenceValues]

/-- A convenient exact product controlling all enlarged unbalanced index
families after the four signed choices are separated. -/
def main3UnbalancedEnlargedDyadicIndexScaleProduct
    (theta : ℝ) (Y : ℕ) : ℕ :=
  main3BalancedR theta Y *
    (dyadicScaleCount (dyadicFactorHeight (theta + 1 / 4) Y) *
      dyadicScaleCount
        (dyadicFactorHeight (theta + 1 / 4) Y * main3BalancedR theta Y))

/-- The broad exact cover has at most four times the displayed index-scale
product. -/
theorem card_unbalancedShiftedSquareDyadicCoverIndices_main3Enlarged_le
    (theta : ℝ) (Y : ℕ) :
    (unbalancedShiftedSquareDyadicCoverIndices
      (theta + 1 / 4) Y (main3BalancedR theta Y)).card ≤
        4 * main3UnbalancedEnlargedDyadicIndexScaleProduct theta Y := by
  classical
  rw [unbalancedShiftedSquareDyadicCoverIndices]
  simp only [Finset.product_eq_sprod, Finset.card_product,
    card_signedDyadicDifferenceValues,
    Nat.card_Ico, card_dyadicLowerEndpoints,
    main3UnbalancedEnlargedDyadicIndexScaleProduct]
  gcongr
  omega

/-- Filtering to active indices cannot increase the broad index count. -/
theorem card_main3UnbalancedEnlargedActiveDyadicCoverIndices_le
    (theta : ℝ) (Y : ℕ) :
    (main3UnbalancedEnlargedActiveDyadicCoverIndices theta Y).card ≤
      4 * main3UnbalancedEnlargedDyadicIndexScaleProduct theta Y := by
  exact (Finset.card_le_card
    (main3UnbalancedEnlargedActiveDyadicCoverIndices_subset_broad
      theta Y)).trans
    (card_unbalancedShiftedSquareDyadicCoverIndices_main3Enlarged_le
      theta Y)

/-- The direct endpoint subfamily obeys the same common count. -/
theorem card_main3UnbalancedEnlargedDirectDyadicCoverIndices_le
    (theta : ℝ) (Y : ℕ) :
    (main3UnbalancedEnlargedDirectDyadicCoverIndices theta Y).card ≤
      4 * main3UnbalancedEnlargedDyadicIndexScaleProduct theta Y := by
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans
    (card_main3UnbalancedEnlargedActiveDyadicCoverIndices_le theta Y)

/-- The complementary analytic endpoint subfamily obeys the same count. -/
theorem card_main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices_le
    (theta : ℝ) (Y : ℕ) :
    (main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y).card ≤
      4 * main3UnbalancedEnlargedDyadicIndexScaleProduct theta Y := by
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans
    (card_main3UnbalancedEnlargedActiveDyadicCoverIndices_le theta Y)

end

end PellPaper
