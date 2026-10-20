import Pell.Main3UnbalancedEnlargedActiveDyadicSplit
import Pell.Main3UnbalancedEnlargedShiftedSquareParameters
import Pell.Main3UnbalancedCeilingParameters
import Mathlib.Tactic

/-!
# Unbalanced-mesh absorption of the main3 quotient error

On a large-analytic main3 index, the endpoint `N` lies above the canonical
threshold `Y^(3/2 - 1/(32*theta^2))`.  At the same time, the original-`theta`
radius gives the sharp shift bound

`|a| < 2 * Y^(1/(100*theta^2))`,

while the unbalanced ceiling mesh satisfies `M <= Y`.  For the harmless
explicit range `65536 <= Y`, these facts imply

`8 * M * sqrt |a| <= n`

at every point of the corresponding squarefree shifted-square block.  The
second theorem records the division form used by the quotient localization.

This file proves only the exponent/error bridge.  It makes no cell-count,
determinant, or asymptotic assertion.
-/

namespace PellPaper

noncomputable section

/-- The chosen unbalanced mesh absorbs eight times the normalized shift error
on every point of a large-analytic squarefree block.  The cover is built at
`theta + 1/4`, whereas its radius and the large-`N` threshold deliberately use
the original `theta`. -/
theorem main3LargeAnalytic_unbalancedMesh_mul_sqrt_shift_le_n
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N d w n : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (hp : (d, w, n) ∈
      squarefreeShiftedSquareBlock (shiftedSquareA h v) D Y N) :
    8 * (main3UnbalancedM theta Y : ℝ) *
        Real.sqrt |(shiftedSquareA h v : ℝ)| ≤ (n : ℝ) := by
  let y : ℝ := Y
  let delta : ℝ := main3BalancedRExponent theta
  let b : ℝ := (3 : ℝ) / 2 - 1 / (32 * theta ^ 2)
  let M : ℕ := main3UnbalancedM theta Y
  have hy65536 : (65536 : ℝ) ≤ y := by
    dsimp [y]
    exact_mod_cast hY
  have hypos : 0 < y := by linarith
  have hyone : 1 ≤ y := by linarith
  have hthetaPos : 0 < theta := by linarith
  have hthetaSqPos : 0 < theta ^ 2 := sq_pos_of_pos hthetaPos
  have hiLarge :=
    mem_main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices.mp hi
  have hiBroad :=
    (mem_main3UnbalancedEnlargedActiveDyadicCoverIndices.mp hiLarge.1).1
  have hshift : |(shiftedSquareA h v : ℝ)| < 2 * y ^ delta := by
    simpa only [y, delta] using
      (main3UnbalancedEnlargedShiftedSquareIndex_shift_abs_bounds
        htheta (by omega : 2 ≤ Y) hiBroad).2.1
  have hMleNat : M ≤ Y := by
    simpa only [M] using
      (main3UnbalancedM_parameter_package theta Y htheta
        (by omega : 2 ≤ Y)).2.1
  have hMle : (M : ℝ) ≤ y := by
    dsimp [y]
    exact_mod_cast hMleNat
  have hsqrtY : (128 : ℝ) ≤ Real.sqrt y := by
    have hsqrtSq : Real.sqrt y ^ 2 = y := Real.sq_sqrt hypos.le
    have hsqrtNonneg := Real.sqrt_nonneg y
    nlinarith
  have hexponent :
      (2 : ℝ) + delta + 1 / 2 ≤ 2 * b := by
    dsimp [delta, b, main3BalancedRExponent]
    field_simp [hthetaSqPos.ne']
    nlinarith [sq_nonneg (theta - 3)]
  have hpower :
      128 * y ^ 2 * y ^ delta ≤ y ^ (2 * b) := by
    calc
      128 * y ^ 2 * y ^ delta =
          128 * y ^ (2 : ℝ) * y ^ delta := by
        rw [← Real.rpow_natCast y 2]
        norm_num
      _ =
          128 * (y ^ (2 : ℝ) * y ^ delta) := by ring
      _ ≤ Real.sqrt y * (y ^ (2 : ℝ) * y ^ delta) := by
        exact mul_le_mul_of_nonneg_right hsqrtY
          (mul_nonneg (Real.rpow_nonneg hypos.le _)
            (Real.rpow_nonneg hypos.le _))
      _ = y ^ ((2 : ℝ) + delta + 1 / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hypos, ← Real.rpow_add hypos]
        congr 1
        ring
      _ ≤ y ^ (2 * b) :=
        Real.rpow_le_rpow_of_exponent_le hyone hexponent
  have hthresholdSq :
      main3UnbalancedEnlargedDirectNThreshold theta Y ^ 2 =
        y ^ (2 * b) := by
    dsimp [main3UnbalancedEnlargedDirectNThreshold, y, b]
    rw [← Real.rpow_mul_natCast hypos.le]
    congr 1
    ring
  have hlhsSq :
      (8 * (M : ℝ) * Real.sqrt |(shiftedSquareA h v : ℝ)|) ^ 2 =
        64 * (M : ℝ) ^ 2 * |(shiftedSquareA h v : ℝ)| := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (abs_nonneg _)]
    ring
  have hsquareBound :
      (8 * (M : ℝ) * Real.sqrt |(shiftedSquareA h v : ℝ)|) ^ 2 ≤
        main3UnbalancedEnlargedDirectNThreshold theta Y ^ 2 := by
    rw [hlhsSq, hthresholdSq]
    calc
      64 * (M : ℝ) ^ 2 * |(shiftedSquareA h v : ℝ)| ≤
          64 * y ^ 2 * |(shiftedSquareA h v : ℝ)| := by
        gcongr
      _ ≤ 64 * y ^ 2 * (2 * y ^ delta) := by
        gcongr
      _ = 128 * y ^ 2 * y ^ delta := by ring
      _ ≤ y ^ (2 * b) := hpower
  have hthresholdNonneg :
      0 ≤ main3UnbalancedEnlargedDirectNThreshold theta Y := by
    unfold main3UnbalancedEnlargedDirectNThreshold
    positivity
  have hmeshThreshold :
      8 * (M : ℝ) * Real.sqrt |(shiftedSquareA h v : ℝ)| ≤
        main3UnbalancedEnlargedDirectNThreshold theta Y := by
    exact (sq_le_sq₀ (by positivity) hthresholdNonneg).mp hsquareBound
  have hNn : N ≤ n :=
    (mem_squarefreeShiftedSquareBlock.mp hp).2.2.2.2.2.2.2.1
  have hNnReal : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hNn
  simpa only [M] using hmeshThreshold.trans (hiLarge.2.trans_le hNnReal).le

/-- Division form of the preceding absorption estimate.  Positivity of both
denominators is derived from the mesh package and literal block membership. -/
theorem main3LargeAnalytic_quotientError_le_inv_unbalancedMesh
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N d w n : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (hp : (d, w, n) ∈
      squarefreeShiftedSquareBlock (shiftedSquareA h v) D Y N) :
    (8 * Real.sqrt |(shiftedSquareA h v : ℝ)|) / (n : ℝ) ≤
      1 / (main3UnbalancedM theta Y : ℝ) := by
  have hnNat : 0 < n := (mem_squarefreeShiftedSquareBlock.mp hp).2.2.1
  have hn : (0 : ℝ) < n := by exact_mod_cast hnNat
  have hMNat : 0 < main3UnbalancedM theta Y :=
    (main3UnbalancedM_parameter_package theta Y htheta
      (by omega : 2 ≤ Y)).1
  have hM : (0 : ℝ) < main3UnbalancedM theta Y := by exact_mod_cast hMNat
  apply (div_le_div_iff₀ hn hM).2
  have hbound :=
    main3LargeAnalytic_unbalancedMesh_mul_sqrt_shift_le_n
      htheta hY hi hp
  nlinarith

end

end PellPaper
