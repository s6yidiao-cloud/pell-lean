import Pell.Main3UnbalancedEnlargedActiveDyadicSplit
import Pell.Main3UnbalancedEnlargedShiftedSquareParameters
import Mathlib.Tactic

/-!
# Shift dominance on the large analytic main3 cells

The large-analytic dyadic endpoint already dominates `Y`.  Since the shift
has absolute value below `2Y`, the mild explicit assumption `8 ≤ Y` forces
every numerator in that block to satisfy `2 * sqrt |a| ≤ n`.  This is the
large-range hypothesis needed by the zeta and target-embedding bounds.
-/

namespace PellPaper

noncomputable section

/-- A large-analytic endpoint and any larger natural numerator dominate the
square root of the associated shifted-square parameter. -/
theorem main3LargeAnalytic_shift_dominates_of_endpoint_le
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N n : ℕ}
    (htheta : 3 ≤ theta) (hY : 8 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (hNn : N ≤ n) :
    2 * Real.sqrt |(shiftedSquareA h v : ℝ)| ≤ (n : ℝ) := by
  have hiLarge :=
    mem_main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices.mp hi
  have hiBroad :=
    (mem_main3UnbalancedEnlargedActiveDyadicCoverIndices.mp hiLarge.1).1
  have hshift : |(shiftedSquareA h v : ℝ)| < 2 * (Y : ℝ) :=
    (main3UnbalancedEnlargedShiftedSquareIndex_shift_abs_bounds
      htheta (by omega) hiBroad).2.2
  have hthetaPos : 0 < theta := by linarith
  have hthetaSqPos : 0 < theta ^ 2 := sq_pos_of_pos hthetaPos
  have hexponent :
      (1 : ℝ) ≤ (3 : ℝ) / 2 - 1 / (32 * theta ^ 2) := by
    field_simp [hthetaSqPos.ne']
    nlinarith [sq_nonneg (theta - 3)]
  have hYone : (1 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast (by omega : 1 ≤ Y)
  have hYThreshold : (Y : ℝ) ≤
      main3UnbalancedEnlargedDirectNThreshold theta Y := by
    calc
      (Y : ℝ) = (Y : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (Y : ℝ) ^ ((3 : ℝ) / 2 - 1 / (32 * theta ^ 2)) :=
        Real.rpow_le_rpow_of_exponent_le hYone hexponent
      _ = main3UnbalancedEnlargedDirectNThreshold theta Y := rfl
  have hYn : (Y : ℝ) < (n : ℝ) := by
    have hNnR : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hNn
    exact hYThreshold.trans_lt (hiLarge.2.trans_le hNnR)
  have hEightY : 8 * (Y : ℝ) ≤ (Y : ℝ) ^ 2 := by
    have hY8 : (8 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
    nlinarith
  have hshiftSq : 4 * |(shiftedSquareA h v : ℝ)| ≤ (n : ℝ) ^ 2 := by
    have hYnSq : (Y : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by
      exact pow_le_pow_left₀ (by positivity) hYn.le 2
    nlinarith
  have hsqrtSq :
      Real.sqrt |(shiftedSquareA h v : ℝ)| ^ 2 =
        |(shiftedSquareA h v : ℝ)| :=
    Real.sq_sqrt (abs_nonneg _)
  apply (sq_le_sq₀ (by positivity) (by positivity)).1
  rw [mul_pow, hsqrtSq]
  nlinarith

/-- Every point in a large-analytic squarefree shifted-square block satisfies
the manuscript's numerator-dominance hypothesis. -/
theorem mem_main3LargeAnalytic_squarefreeBlock_shift_dominates
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N d w n : ℕ}
    (htheta : 3 ≤ theta) (hY : 8 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (hp : (d, w, n) ∈
      squarefreeShiftedSquareBlock (shiftedSquareA h v) D Y N) :
    2 * Real.sqrt |(shiftedSquareA h v : ℝ)| ≤ (n : ℝ) :=
  main3LargeAnalytic_shift_dominates_of_endpoint_le htheta hY hi
    (mem_squarefreeShiftedSquareBlock.mp hp).2.2.2.2.2.2.2.1

end

end PellPaper
