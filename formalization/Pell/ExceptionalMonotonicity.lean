import Pell.Definitions

/-!
# Monotonicity of the Pell exceptional sets

The exponent in `SmallFundamentalSolution` is monotone only after its radicand
has been shown to be at least one.  A small fundamental solution supplies that
fact automatically: it cannot occur at the zero radicand.  This file keeps that
minor, but important, side condition explicit before passing to finite-set
inclusions and cardinalities.
-/

namespace PellPaper

/-- For a natural base at least one, real powers are monotone in the exponent. -/
theorem nat_rpow_le_rpow_of_exponent_le {m : ℕ} {θ φ : ℝ}
    (hm : 1 ≤ m) (hθφ : θ ≤ φ) :
    (m : ℝ) ^ θ ≤ (m : ℝ) ^ φ := by
  apply Real.rpow_le_rpow_of_exponent_le
  · exact_mod_cast hm
  · exact hθφ

/-- A small fundamental solution forces its natural radicand to be at least one. -/
theorem one_le_of_smallFundamentalSolution {θ : ℝ} {m : ℕ}
    (hsmall : SmallFundamentalSolution θ m) : 1 ≤ m := by
  exact Nat.succ_le_iff.mpr (positive_nonsquare_of_smallFundamentalSolution hsmall).1

/-- Increasing the exponent preserves the small-fundamental-solution condition.

There is deliberately no version with only `0 ≤ m`: at the zero base, real
power monotonicity depends on the signs of the exponents.  Here positivity is
obtained from the Pell witness itself. -/
theorem smallFundamentalSolution_mono {θ φ : ℝ} {m : ℕ}
    (hθφ : θ ≤ φ) :
    SmallFundamentalSolution θ m → SmallFundamentalSolution φ m := by
  rintro ⟨a, ha, hbound⟩
  refine ⟨a, ha, hbound.trans ?_⟩
  apply nat_rpow_le_rpow_of_exponent_le
  · exact one_le_of_smallFundamentalSolution ⟨a, ha, hbound⟩
  · exact hθφ

/-- At a fixed cutoff, increasing the exponent enlarges the exceptional set. -/
theorem exceptionalSet_subset_exponent {θ φ : ℝ} (hθφ : θ ≤ φ) (X : ℕ) :
    exceptionalSet θ X ⊆ exceptionalSet φ X := by
  intro m hm
  obtain ⟨hmone, hmX, hsmall⟩ := mem_exceptionalSet.mp hm
  exact mem_exceptionalSet.mpr
    ⟨hmone, hmX, smallFundamentalSolution_mono hθφ hsmall⟩

/-- The integer exceptional count is monotone in the exponent. -/
theorem EInt_le_of_exponent_le {θ φ : ℝ} (hθφ : θ ≤ φ) (X : ℕ) :
    EInt θ X ≤ EInt φ X := by
  unfold EInt
  exact Finset.card_le_card (exceptionalSet_subset_exponent hθφ X)

/-- At a fixed exponent, increasing the integer cutoff enlarges the exceptional
set. -/
theorem exceptionalSet_subset_cutoff (θ : ℝ) {X Y : ℕ} (hXY : X ≤ Y) :
    exceptionalSet θ X ⊆ exceptionalSet θ Y := by
  intro m hm
  obtain ⟨hmone, hmX, hsmall⟩ := mem_exceptionalSet.mp hm
  exact mem_exceptionalSet.mpr ⟨hmone, hmX.trans hXY, hsmall⟩

/-- The integer exceptional count is monotone in the cutoff. -/
theorem EInt_le_of_cutoff_le (θ : ℝ) {X Y : ℕ} (hXY : X ≤ Y) :
    EInt θ X ≤ EInt θ Y := by
  unfold EInt
  exact Finset.card_le_card (exceptionalSet_subset_cutoff θ hXY)

/-- The real-cutoff exceptional count is likewise monotone in the Pell
exponent. -/
theorem E_le_of_exponent_le {θ φ X : ℝ} (hθφ : θ ≤ φ) :
    E θ X ≤ E φ X := by
  unfold E
  exact_mod_cast EInt_le_of_exponent_le hθφ ⌊X⌋₊

end PellPaper
