import Pell.ShiftedSquareQuadraticInteger
import Mathlib.Tactic

/-!
# Elementary scale comparison for shifted squares

If `n^2 - a = d^2 w` and `n` dominates `sqrt |a|`, then `n` is comparable
to `d * sqrt w`.  The first two theorems use the literal subtraction
orientation.  The next two adapt them to the project's convention
`d^2 w = n^2 + a`.  A final corollary records the corresponding, slightly
weaker comparison with the parity-normalized source scale `d₀ * sqrt w`.

No squarefreeness, nonsquare, or strict positivity hypothesis is needed for
these inequalities.  Consequently they apply, unchanged, in the stronger
shifted-square contexts used elsewhere in the project.
-/

namespace PellPaper

noncomputable section

/-- The sharp integer-coefficient squared comparison in the literal
orientation `n^2 - a = d^2 w`. -/
theorem shiftedSquare_sub_scale_squared_comparability
    {a : ℤ} {d w n : ℕ}
    (heq : (n : ℤ) ^ 2 - a = (d : ℤ) ^ 2 * (w : ℤ))
    (hn : 2 * Real.sqrt |(a : ℝ)| ≤ (n : ℝ)) :
    3 * (n : ℝ) ^ 2 ≤ 4 * (d : ℝ) ^ 2 * (w : ℝ) ∧
      4 * (d : ℝ) ^ 2 * (w : ℝ) ≤ 5 * (n : ℝ) ^ 2 := by
  have heqR :
      (n : ℝ) ^ 2 - (a : ℝ) = (d : ℝ) ^ 2 * (w : ℝ) := by
    exact_mod_cast heq
  have hsqrtSq :
      (Real.sqrt |(a : ℝ)|) ^ 2 = |(a : ℝ)| :=
    Real.sq_sqrt (abs_nonneg _)
  have hdiff :
      0 ≤ (n : ℝ) - 2 * Real.sqrt |(a : ℝ)| := by
    linarith
  have hsum :
      0 ≤ (n : ℝ) + 2 * Real.sqrt |(a : ℝ)| := by
    positivity
  have hproduct :
      0 ≤ ((n : ℝ) - 2 * Real.sqrt |(a : ℝ)|) *
        ((n : ℝ) + 2 * Real.sqrt |(a : ℝ)|) :=
    mul_nonneg hdiff hsum
  have habs : 4 * |(a : ℝ)| ≤ (n : ℝ) ^ 2 := by
    nlinarith
  constructor
  · nlinarith [le_abs_self (a : ℝ)]
  · nlinarith [neg_abs_le (a : ℝ)]

/-- Coarse linear comparison obtained from the squared bounds.  The factor
two avoids divisions and is uniform at all endpoint cases. -/
theorem shiftedSquare_sub_scale_linear_comparability
    {a : ℤ} {d w n : ℕ}
    (heq : (n : ℤ) ^ 2 - a = (d : ℤ) ^ 2 * (w : ℤ))
    (hn : 2 * Real.sqrt |(a : ℝ)| ≤ (n : ℝ)) :
    (n : ℝ) ≤ 2 * (d : ℝ) * Real.sqrt (w : ℝ) ∧
      (d : ℝ) * Real.sqrt (w : ℝ) ≤ 2 * (n : ℝ) := by
  have hsq := shiftedSquare_sub_scale_squared_comparability heq hn
  have hsqrtW : Real.sqrt (w : ℝ) ^ 2 = (w : ℝ) :=
    Real.sq_sqrt (by positivity)
  constructor
  · apply (sq_le_sq₀ (by positivity) (by positivity)).1
    calc
      (n : ℝ) ^ 2 ≤ 4 * ((d : ℝ) ^ 2 * (w : ℝ)) := by
        nlinarith [hsq.1]
      _ = (2 * (d : ℝ) * Real.sqrt (w : ℝ)) ^ 2 := by
        rw [mul_pow, mul_pow, hsqrtW]
        ring
  · apply (sq_le_sq₀ (by positivity) (by positivity)).1
    calc
      ((d : ℝ) * Real.sqrt (w : ℝ)) ^ 2 =
          (d : ℝ) ^ 2 * (w : ℝ) := by
        rw [mul_pow, hsqrtW]
      _ ≤ 4 * (n : ℝ) ^ 2 := by
        nlinarith [hsq.2, sq_nonneg (n : ℝ)]
      _ = (2 * (n : ℝ)) ^ 2 := by ring

/-- Squared comparison in the canonical project orientation
`d^2 w = n^2 + a`.  It is the subtraction theorem with shift `-a`. -/
theorem shiftedSquare_scale_squared_comparability
    {a : ℤ} {d w n : ℕ}
    (heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a)
    (hn : 2 * Real.sqrt |(a : ℝ)| ≤ (n : ℝ)) :
    3 * (n : ℝ) ^ 2 ≤ 4 * (d : ℝ) ^ 2 * (w : ℝ) ∧
      4 * (d : ℝ) ^ 2 * (w : ℝ) ≤ 5 * (n : ℝ) ^ 2 := by
  apply shiftedSquare_sub_scale_squared_comparability (a := -a)
  · simpa only [sub_neg_eq_add] using heq.symm
  · simpa only [Int.cast_neg, abs_neg] using hn

/-- Coarse source-scale comparison in the canonical project orientation. -/
theorem shiftedSquare_scale_linear_comparability
    {a : ℤ} {d w n : ℕ}
    (heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a)
    (hn : 2 * Real.sqrt |(a : ℝ)| ≤ (n : ℝ)) :
    (n : ℝ) ≤ 2 * (d : ℝ) * Real.sqrt (w : ℝ) ∧
      (d : ℝ) * Real.sqrt (w : ℝ) ≤ 2 * (n : ℝ) := by
  apply shiftedSquare_sub_scale_linear_comparability (a := -a)
  · simpa only [sub_neg_eq_add] using heq.symm
  · simpa only [Int.cast_neg, abs_neg] using hn

/-- The parity-normalized source scale `d₀ * sqrt w` is comparable to `n`
with constants `4` and `2`. -/
theorem shiftedSquareD₀_scale_linear_comparability
    {a : ℤ} {d w n : ℕ}
    (heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a)
    (hn : 2 * Real.sqrt |(a : ℝ)| ≤ (n : ℝ)) :
    (n : ℝ) ≤
        4 * (shiftedSquareD₀ d : ℝ) * Real.sqrt (w : ℝ) ∧
      (shiftedSquareD₀ d : ℝ) * Real.sqrt (w : ℝ) ≤
        2 * (n : ℝ) := by
  have hmain := shiftedSquare_scale_linear_comparability heq hn
  have hq₂le : shiftedSquareQ₂ d ≤ 2 := by
    by_cases hdEven : Even d
    · simp [shiftedSquareQ₂_eq_two_of_even hdEven]
    · simp [shiftedSquareQ₂_eq_one_of_not_even hdEven]
  have hdleNat : d ≤ 2 * shiftedSquareD₀ d := by
    calc
      d = shiftedSquareQ₂ d * shiftedSquareD₀ d :=
        (shiftedSquareQ₂_mul_D₀ d).symm
      _ ≤ 2 * shiftedSquareD₀ d :=
        Nat.mul_le_mul_right (shiftedSquareD₀ d) hq₂le
  have hd₀leNat : shiftedSquareD₀ d ≤ d := by
    exact Nat.div_le_self d (shiftedSquareQ₂ d)
  have hdle : (d : ℝ) ≤ 2 * (shiftedSquareD₀ d : ℝ) := by
    exact_mod_cast hdleNat
  have hd₀le : (shiftedSquareD₀ d : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast hd₀leNat
  constructor
  · calc
      (n : ℝ) ≤ 2 * (d : ℝ) * Real.sqrt (w : ℝ) := hmain.1
      _ ≤ 2 * (2 * (shiftedSquareD₀ d : ℝ)) *
          Real.sqrt (w : ℝ) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hdle (by norm_num))
          (Real.sqrt_nonneg _)
      _ = 4 * (shiftedSquareD₀ d : ℝ) *
          Real.sqrt (w : ℝ) := by ring
  · calc
      (shiftedSquareD₀ d : ℝ) * Real.sqrt (w : ℝ) ≤
          (d : ℝ) * Real.sqrt (w : ℝ) :=
        mul_le_mul_of_nonneg_right hd₀le (Real.sqrt_nonneg _)
      _ ≤ 2 * (n : ℝ) := hmain.2

end

end PellPaper
