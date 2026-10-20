import Pell.DyadicSquarePartReduction
import Pell.SquarePartTailAnalytic

/-!
# The dyadic large-square-part tail at a real-power threshold

The natural threshold `ceil (Y ^ a) + 1` makes the denominator in the
elementary square-divisor tail at least `Y ^ a`.  For `Y ≥ 1` this gives
the explicit bound `2 * Y ^ (1 - a)` for the large-square-part contribution
to the half-open dyadic interval `[Y, 2Y)`.

The exponent `a` may be any real number.  The final split retains the entire
small-square-part contribution; it does not assert a Pell power saving.
-/

namespace PellPaper

/-- A positive integral threshold whose predecessor majorizes the real power. -/
noncomputable def squarePartPowerThreshold (Y : ℕ) (a : ℝ) : ℕ :=
  ⌈(Y : ℝ) ^ a⌉₊ + 1

/-- At a positive scale the power threshold is at least two, for every
real exponent, including negative exponents. -/
theorem two_le_squarePartPowerThreshold {Y : ℕ} (hY : 1 ≤ Y) (a : ℝ) :
    2 ≤ squarePartPowerThreshold Y a := by
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hY)
  have hceil : 1 ≤ ⌈(Y : ℝ) ^ a⌉₊ :=
    Nat.one_le_ceil_iff.mpr (Real.rpow_pos_of_pos hYpos a)
  unfold squarePartPowerThreshold
  omega

/-- The real predecessor of the chosen threshold is the natural ceiling,
so it bounds the power without a rounding loss. -/
theorem rpow_le_squarePartPowerThreshold_sub_one (Y : ℕ) (a : ℝ) :
    (Y : ℝ) ^ a ≤ (squarePartPowerThreshold Y a : ℝ) - 1 := by
  simpa only [squarePartPowerThreshold, Nat.cast_add, Nat.cast_one,
    add_sub_cancel_right] using Nat.le_ceil ((Y : ℝ) ^ a)

/-- The analytic tail at the power threshold, with constant exactly two. -/
theorem dyadic_square_part_tail_le_rpow {Y : ℕ} (hY : 1 ≤ Y) (a : ℝ) :
    (2 * Y : ℝ) / ((squarePartPowerThreshold Y a : ℝ) - 1) ≤
      2 * (Y : ℝ) ^ (1 - a) := by
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hY)
  have hpowpos : 0 < (Y : ℝ) ^ a := Real.rpow_pos_of_pos hYpos a
  calc
    (2 * Y : ℝ) / ((squarePartPowerThreshold Y a : ℝ) - 1) ≤
        (2 * Y : ℝ) / (Y : ℝ) ^ a :=
      div_le_div_of_nonneg_left (by positivity) hpowpos
        (rpow_le_squarePartPowerThreshold_sub_one Y a)
    _ = 2 * (Y : ℝ) ^ (1 - a) := by
      rw [Real.rpow_sub hYpos, Real.rpow_one, mul_div_assoc]

/-- The dyadic large-square-part family obeys the elementary tail with the
exact closed natural cutoff `2Y - 1` inherited from `m < 2Y`. -/
theorem dyadicLargeSquarePartExceptional_card_le_div
    (θ : ℝ) (Y S : ℕ) (hS : 2 ≤ S) :
    ((dyadicLargeSquarePartExceptionalSet θ Y S).card : ℝ) ≤
      ((2 * Y - 1 : ℕ) : ℝ) / ((S : ℝ) - 1) := by
  apply card_le_div_of_square_part_decompositions hS
  intro m hm
  obtain ⟨hdyadic, s, w, _, hSs, _, hdecomp, _⟩ :=
    mem_dyadicLargeSquarePartExceptionalSet.mp hm
  obtain ⟨_, hmhi, hsmall⟩ := mem_dyadicSquarePartExceptionalSet.mp hdyadic
  obtain ⟨hmpos, _⟩ := positive_nonsquare_of_smallFundamentalSolution hsmall
  exact ⟨hmpos, by omega, s, w, hSs, hdecomp⟩

/-- Every real-power threshold gives an unconditional bound for the large
square-part contribution.  This counts radicands rather than decompositions. -/
theorem dyadicLargeSquarePartExceptional_card_le_rpow
    (θ : ℝ) {Y : ℕ} (hY : 1 ≤ Y) (a : ℝ) :
    ((dyadicLargeSquarePartExceptionalSet θ Y (squarePartPowerThreshold Y a)).card : ℝ) ≤
      2 * (Y : ℝ) ^ (1 - a) := by
  have hS : 2 ≤ squarePartPowerThreshold Y a := two_le_squarePartPowerThreshold hY a
  have hSreal : (2 : ℝ) ≤ squarePartPowerThreshold Y a := by exact_mod_cast hS
  have hcutoff : ((2 * Y - 1 : ℕ) : ℝ) ≤ 2 * (Y : ℝ) := by
    exact_mod_cast Nat.sub_le (2 * Y) 1
  calc
    _ ≤ ((2 * Y - 1 : ℕ) : ℝ) /
        ((squarePartPowerThreshold Y a : ℝ) - 1) :=
      dyadicLargeSquarePartExceptional_card_le_div θ Y _ hS
    _ ≤ (2 * Y : ℝ) / ((squarePartPowerThreshold Y a : ℝ) - 1) :=
      div_le_div_of_nonneg_right hcutoff (by linarith)
    _ ≤ 2 * (Y : ℝ) ^ (1 - a) := dyadic_square_part_tail_le_rpow hY a

/-- The exact small/large decomposition now leaves only the small-square-part
count and the explicit power tail.  No estimate for the small family is assumed. -/
theorem dyadicSquarePartExceptionalCount_le_small_add_rpow
    (θ : ℝ) {Y : ℕ} (hY : 1 ≤ Y) (a : ℝ) :
    (dyadicSquarePartExceptionalCount θ Y : ℝ) ≤
      ((dyadicSmallSquarePartExceptionalSet θ Y (squarePartPowerThreshold Y a)).card : ℝ) +
        2 * (Y : ℝ) ^ (1 - a) := by
  rw [dyadicSquarePartExceptionalCount_eq_small_add_large
    θ Y (squarePartPowerThreshold Y a), Nat.cast_add]
  exact add_le_add le_rfl (dyadicLargeSquarePartExceptional_card_le_rpow θ hY a)

/-- The finite transferred squarefree fibers can replace the small count;
the resulting sum and the large-root tail are both explicit. -/
theorem dyadicSquarePartExceptionalCount_le_sum_transferred_add_rpow
    (θ : ℝ) {Y : ℕ} (hY : 1 ≤ Y) (a : ℝ) :
    (dyadicSquarePartExceptionalCount θ Y : ℝ) ≤
      (∑ s ∈ Finset.Ico 1 (squarePartPowerThreshold Y a),
        ((dyadicTransferredSquarefreeSet θ Y s).card : ℝ)) +
        2 * (Y : ℝ) ^ (1 - a) := by
  apply (dyadicSquarePartExceptionalCount_le_small_add_rpow θ hY a).trans
  apply add_le_add _ le_rfl
  exact_mod_cast dyadicSmallSquarePartExceptional_card_le_sum_transferred
    θ Y (squarePartPowerThreshold Y a)

end PellPaper
