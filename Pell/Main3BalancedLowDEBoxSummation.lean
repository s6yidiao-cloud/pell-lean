import Pell.BalancedLowDEElementaryCount
import Pell.Main3BalancedDyadicBoxSummation
import Mathlib.Tactic

/-!
# Summing the elementary low-DE balanced-box estimate

This module inserts the direct low-`DE` cell count into the finite balanced
dyadic decomposition.  It keeps the exact four-coordinate dyadic scale count
visible; the later uniform absorption step is responsible for replacing that
fixed polylogarithmic cost by a small power of the global scale.
-/

namespace PellPaper

noncomputable section

/-- A common pointwise envelope costs at most the number of occupied
low-`DE` boxes times that envelope. -/
theorem main3BalancedLowDEBoxUnion_card_cast_le_card_mul
    (theta : ℝ) (Y R : ℕ) (A : ℝ)
    (hA : ∀ i ∈ main3BalancedLowDEBoxIndices theta Y R,
      ((dyadicFactorBoxCell (theta + 1 / 4) Y i).card : ℝ) ≤ A) :
    ((main3BalancedLowDEBoxUnion theta Y R).card : ℝ) ≤
      ((main3BalancedLowDEBoxIndices theta Y R).card : ℝ) * A := by
  calc
    ((main3BalancedLowDEBoxUnion theta Y R).card : ℝ) ≤
        ∑ _i ∈ main3BalancedLowDEBoxIndices theta Y R, A :=
      main3BalancedLowDEBoxUnion_card_cast_le_sum theta Y R (fun _ => A) hA
    _ = ((main3BalancedLowDEBoxIndices theta Y R).card : ℝ) * A := by
      simp

/-- The active low-`DE` boxes are bounded by the same exact four-coordinate
dyadic scale product as the ambient factor-box decomposition. -/
theorem card_main3BalancedLowDEBoxIndices_le_scale_product
    (theta : ℝ) (Y R : ℕ) :
    (main3BalancedLowDEBoxIndices theta Y R).card ≤
      dyadicScaleCount (dyadicFactorHeight (theta + 1 / 4) Y) *
        (dyadicScaleCount (dyadicFactorHeight (theta + 1 / 4) Y) *
          (dyadicScaleCount (2 * Y) * dyadicScaleCount (2 * Y))) := by
  calc
    (main3BalancedLowDEBoxIndices theta Y R).card ≤
        (dyadicFactorBoxIndices (theta + 1 / 4) Y).card := by
      apply Finset.card_le_card
      intro i hi
      exact (mem_main3BalancedOccupiedBoxIndices.mp
        (mem_main3BalancedLowDEBoxIndices.mp hi).1).1
    _ = _ := by
      simp [dyadicFactorBoxIndices, card_dyadicBoxIndices]

/-- Complete finite low-`DE` summation before the standard polylogarithmic
scale count is absorbed. -/
theorem main3BalancedLowDEBoxUnion_card_cast_le_scaleProduct_mul_elementaryEnvelope
    (theta : ℝ) (Y R : ℕ) :
    ((main3BalancedLowDEBoxUnion theta Y R).card : ℝ) ≤
      (dyadicScaleCount (dyadicFactorHeight (theta + 1 / 4) Y) *
          (dyadicScaleCount (dyadicFactorHeight (theta + 1 / 4) Y) *
            (dyadicScaleCount (2 * Y) * dyadicScaleCount (2 * Y))) : ℕ) *
        (4 * (Y : ℝ) ^ (1 - 1 / (100 * theta ^ 2)) +
          28 * Real.sqrt (Y : ℝ)) := by
  let A : ℝ := 4 * (Y : ℝ) ^ (1 - 1 / (100 * theta ^ 2)) +
    28 * Real.sqrt (Y : ℝ)
  have hpoint : ∀ i ∈ main3BalancedLowDEBoxIndices theta Y R,
      ((dyadicFactorBoxCell (theta + 1 / 4) Y i).card : ℝ) ≤ A := by
    intro i hi
    have hmem := mem_main3BalancedLowDEBoxIndices.mp hi
    have hcell := (mem_main3BalancedOccupiedBoxIndices.mp hmem.1).2.1
    simpa only [A] using
      main3BalancedLowDE_dyadicFactorBoxCell_card_le theta Y i hcell hmem.2
  have hunion :=
    main3BalancedLowDEBoxUnion_card_cast_le_card_mul theta Y R A hpoint
  have hindices :
      ((main3BalancedLowDEBoxIndices theta Y R).card : ℝ) ≤
        (dyadicScaleCount (dyadicFactorHeight (theta + 1 / 4) Y) *
          (dyadicScaleCount (dyadicFactorHeight (theta + 1 / 4) Y) *
            (dyadicScaleCount (2 * Y) * dyadicScaleCount (2 * Y))) : ℕ) := by
    exact_mod_cast card_main3BalancedLowDEBoxIndices_le_scale_product theta Y R
  have hA0 : 0 ≤ A := by
    dsimp [A]
    positivity
  exact hunion.trans (mul_le_mul_of_nonneg_right hindices hA0)

end

end PellPaper
