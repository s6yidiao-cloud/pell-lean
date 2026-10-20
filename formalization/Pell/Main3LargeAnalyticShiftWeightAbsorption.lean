import Pell.Main3UnbalancedEnlargedActiveDyadicSplit
import Pell.Main3UnbalancedEnlargedShiftedSquareParameters
import Mathlib.Tactic

/-!
# Absorption of the main3 large-analytic shift weights

The manuscript writes `A_a = 2 * |a|`.  For an index in the main3
large-analytic cover, the canonical shift package gives

`A_a < 4 * Y^(1 / (100 * theta^2))`.

This candidate turns that pointwise fact into the two precise power
absorptions needed for the geometric terms of the large-analytic block
estimate.  It does not assume a fibre bound or the total block-sum estimate.
-/

namespace PellPaper

noncomputable section

/-- The manuscript's positive shift-height parameter `A_a = 2 * |a|`. -/
def main3LargeAnalyticShiftWeight (h : ℤ) (v : ℕ) : ℝ :=
  2 * |(shiftedSquareA h v : ℝ)|

/-- Every main3 large-analytic index satisfies the manuscript's shift-height
budget `A_a <= 4 * Y^(1/(100*theta^2))`. -/
theorem main3LargeAnalyticShiftWeight_le_four_mul_rpow_candidate
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 2 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y) :
    main3LargeAnalyticShiftWeight h v ≤
      4 * (Y : ℝ) ^ main3BalancedRExponent theta := by
  have hiLarge :=
    mem_main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices.mp hi
  have hiBroad :=
    (mem_main3UnbalancedEnlargedActiveDyadicCoverIndices.mp hiLarge.1).1
  have hshift : |(shiftedSquareA h v : ℝ)| <
      2 * (Y : ℝ) ^ main3BalancedRExponent theta :=
    (main3UnbalancedEnlargedShiftedSquareIndex_shift_abs_bounds
      htheta hY hiBroad).2.1
  unfold main3LargeAnalyticShiftWeight
  nlinarith

/-- Raising the manuscript shift-height budget to any nonnegative real power
costs only the corresponding fixed power of `4`. -/
theorem main3LargeAnalyticShiftWeight_rpow_le_candidate
    {theta p : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 2 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (hp : 0 ≤ p) :
    main3LargeAnalyticShiftWeight h v ^ p ≤
      4 ^ p * (Y : ℝ) ^ (main3BalancedRExponent theta * p) := by
  have hy : (0 : ℝ) ≤ (Y : ℝ) := by positivity
  have hA := main3LargeAnalyticShiftWeight_le_four_mul_rpow_candidate
    htheta hY hi
  calc
    main3LargeAnalyticShiftWeight h v ^ p ≤
        (4 * (Y : ℝ) ^ main3BalancedRExponent theta) ^ p :=
      Real.rpow_le_rpow (by
        unfold main3LargeAnalyticShiftWeight
        positivity) hA hp
    _ = 4 ^ p *
        ((Y : ℝ) ^ main3BalancedRExponent theta) ^ p := by
      rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hy _)]
    _ = 4 ^ p *
        (Y : ℝ) ^ (main3BalancedRExponent theta * p) := by
      rw [Real.rpow_mul hy]

/-- The `A_a^(7/8)` geometric contribution is absorbed by the target power
in the total large-analytic estimate. -/
theorem main3LargeAnalytic_sevenEighthShiftTerm_le_target_rpow_candidate
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 2 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y) :
    main3LargeAnalyticShiftWeight h v ^ ((7 : ℝ) / 8) *
        (Y : ℝ) ^ (1 - 1 / (32 * theta ^ 2)) ≤
      4 ^ ((7 : ℝ) / 8) *
        (Y : ℝ) ^ (1 - 1 / (400 * theta ^ 2)) := by
  let y : ℝ := Y
  let delta : ℝ := main3BalancedRExponent theta
  let sourceExponent : ℝ := 1 - 1 / (32 * theta ^ 2)
  let targetExponent : ℝ := 1 - 1 / (400 * theta ^ 2)
  have hypos : 0 < y := by dsimp [y]; positivity
  have hyone : 1 ≤ y := by
    dsimp [y]
    exact_mod_cast (by omega : 1 ≤ Y)
  have hthetaPos : 0 < theta := by linarith
  have hthetaSqPos : 0 < theta ^ 2 := sq_pos_of_pos hthetaPos
  have hshiftPower : main3LargeAnalyticShiftWeight h v ^ ((7 : ℝ) / 8) ≤
      4 ^ ((7 : ℝ) / 8) * y ^ (delta * ((7 : ℝ) / 8)) := by
    simpa only [y, delta] using
      main3LargeAnalyticShiftWeight_rpow_le_candidate
        htheta hY hi (by norm_num : (0 : ℝ) ≤ 7 / 8)
  have hexponent : delta * ((7 : ℝ) / 8) + sourceExponent ≤
      targetExponent := by
    dsimp [delta, sourceExponent, targetExponent,
      main3BalancedRExponent]
    field_simp [hthetaSqPos.ne']
    nlinarith
  have hpower :
      y ^ (delta * ((7 : ℝ) / 8)) * y ^ sourceExponent ≤
        y ^ targetExponent := by
    rw [← Real.rpow_add hypos]
    exact Real.rpow_le_rpow_of_exponent_le hyone hexponent
  change main3LargeAnalyticShiftWeight h v ^ ((7 : ℝ) / 8) *
      y ^ sourceExponent ≤ 4 ^ ((7 : ℝ) / 8) * y ^ targetExponent
  calc
    main3LargeAnalyticShiftWeight h v ^ ((7 : ℝ) / 8) *
        y ^ sourceExponent ≤
      (4 ^ ((7 : ℝ) / 8) * y ^ (delta * ((7 : ℝ) / 8))) *
        y ^ sourceExponent :=
      mul_le_mul_of_nonneg_right hshiftPower (Real.rpow_nonneg hypos.le _)
    _ = 4 ^ ((7 : ℝ) / 8) *
        (y ^ (delta * ((7 : ℝ) / 8)) * y ^ sourceExponent) := by ring
    _ ≤ 4 ^ ((7 : ℝ) / 8) * y ^ targetExponent :=
      mul_le_mul_of_nonneg_left hpower (Real.rpow_nonneg (by norm_num) _)

/-- The `A_a^(9/8)` geometric contribution is also absorbed by the same
target power.  Here the spare factor `Y^(1/2)` supplies ample room. -/
theorem main3LargeAnalytic_nineEighthShiftTerm_le_target_rpow_candidate
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 2 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y) :
    main3LargeAnalyticShiftWeight h v ^ ((9 : ℝ) / 8) *
        (Y : ℝ) ^ ((1 : ℝ) / 2 + 1 / (32 * theta ^ 2)) ≤
      4 ^ ((9 : ℝ) / 8) *
        (Y : ℝ) ^ (1 - 1 / (400 * theta ^ 2)) := by
  let y : ℝ := Y
  let delta : ℝ := main3BalancedRExponent theta
  let sourceExponent : ℝ := (1 : ℝ) / 2 + 1 / (32 * theta ^ 2)
  let targetExponent : ℝ := 1 - 1 / (400 * theta ^ 2)
  have hypos : 0 < y := by dsimp [y]; positivity
  have hyone : 1 ≤ y := by
    dsimp [y]
    exact_mod_cast (by omega : 1 ≤ Y)
  have hthetaPos : 0 < theta := by linarith
  have hthetaSqPos : 0 < theta ^ 2 := sq_pos_of_pos hthetaPos
  have hshiftPower : main3LargeAnalyticShiftWeight h v ^ ((9 : ℝ) / 8) ≤
      4 ^ ((9 : ℝ) / 8) * y ^ (delta * ((9 : ℝ) / 8)) := by
    simpa only [y, delta] using
      main3LargeAnalyticShiftWeight_rpow_le_candidate
        htheta hY hi (by norm_num : (0 : ℝ) ≤ 9 / 8)
  have hexponent : delta * ((9 : ℝ) / 8) + sourceExponent ≤
      targetExponent := by
    dsimp [delta, sourceExponent, targetExponent,
      main3BalancedRExponent]
    field_simp [hthetaSqPos.ne']
    nlinarith [sq_nonneg (theta - 3)]
  have hpower :
      y ^ (delta * ((9 : ℝ) / 8)) * y ^ sourceExponent ≤
        y ^ targetExponent := by
    rw [← Real.rpow_add hypos]
    exact Real.rpow_le_rpow_of_exponent_le hyone hexponent
  change main3LargeAnalyticShiftWeight h v ^ ((9 : ℝ) / 8) *
      y ^ sourceExponent ≤ 4 ^ ((9 : ℝ) / 8) * y ^ targetExponent
  calc
    main3LargeAnalyticShiftWeight h v ^ ((9 : ℝ) / 8) *
        y ^ sourceExponent ≤
      (4 ^ ((9 : ℝ) / 8) * y ^ (delta * ((9 : ℝ) / 8))) *
        y ^ sourceExponent :=
      mul_le_mul_of_nonneg_right hshiftPower (Real.rpow_nonneg hypos.le _)
    _ = 4 ^ ((9 : ℝ) / 8) *
        (y ^ (delta * ((9 : ℝ) / 8)) * y ^ sourceExponent) := by ring
    _ ≤ 4 ^ ((9 : ℝ) / 8) * y ^ targetExponent :=
      mul_le_mul_of_nonneg_left hpower (Real.rpow_nonneg (by norm_num) _)

/-- The sum of the two manuscript shift-weighted geometric terms has a
single absolute coefficient and the final large-analytic target exponent. -/
theorem main3LargeAnalytic_shiftWeightedGeometricTerms_le_target_rpow_candidate
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 2 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y) :
    main3LargeAnalyticShiftWeight h v ^ ((7 : ℝ) / 8) *
          (Y : ℝ) ^ (1 - 1 / (32 * theta ^ 2)) +
        main3LargeAnalyticShiftWeight h v ^ ((9 : ℝ) / 8) *
          (Y : ℝ) ^ ((1 : ℝ) / 2 + 1 / (32 * theta ^ 2)) ≤
      (4 ^ ((7 : ℝ) / 8) + 4 ^ ((9 : ℝ) / 8)) *
        (Y : ℝ) ^ (1 - 1 / (400 * theta ^ 2)) := by
  calc
    main3LargeAnalyticShiftWeight h v ^ ((7 : ℝ) / 8) *
          (Y : ℝ) ^ (1 - 1 / (32 * theta ^ 2)) +
        main3LargeAnalyticShiftWeight h v ^ ((9 : ℝ) / 8) *
          (Y : ℝ) ^ ((1 : ℝ) / 2 + 1 / (32 * theta ^ 2)) ≤
      4 ^ ((7 : ℝ) / 8) *
          (Y : ℝ) ^ (1 - 1 / (400 * theta ^ 2)) +
        4 ^ ((9 : ℝ) / 8) *
          (Y : ℝ) ^ (1 - 1 / (400 * theta ^ 2)) :=
      add_le_add
        (main3LargeAnalytic_sevenEighthShiftTerm_le_target_rpow_candidate
          htheta hY hi)
        (main3LargeAnalytic_nineEighthShiftTerm_le_target_rpow_candidate
          htheta hY hi)
    _ = (4 ^ ((7 : ℝ) / 8) + 4 ^ ((9 : ℝ) / 8)) *
        (Y : ℝ) ^ (1 - 1 / (400 * theta ^ 2)) := by ring

end

end PellPaper
