import Pell.FixedHeightGlobalSquarefree

/-!
# Global squarefree power bounds at arbitrary natural cutoffs

The finite dyadic summation in `FixedHeightGlobalSquarefree` extends to every
natural cutoff by rounding a positive cutoff upward to the next power of two.
The rounding costs a factor at most `2^p` for a positive exponent `p`.
The zero cutoff is handled exactly by its empty exceptional set.
-/

namespace PellPaper

/-- The global squarefree count vanishes at cutoff zero. -/
@[simp] theorem squarefreeExceptionalCount_zero (φ : ℝ) :
    squarefreeExceptionalCount φ 0 = 0 := by
  simp [squarefreeExceptionalCount]

/-- A uniform bound on the dyadic blocks gives a power bound at every
natural cutoff, with the geometric-sum and dyadic-rounding factors explicit.
-/
theorem squarefreeExceptionalCount_le_power_of_dyadic_bound
    {φ C p : ℝ} (hC : 0 ≤ C) (hp : 0 < p)
    (hdyadic : ∀ k : ℕ,
      (squarefreeDyadicExceptionalCount φ (2 ^ k) : ℝ) ≤
        C * ((2 ^ k : ℕ) : ℝ) ^ p)
    (X : ℕ) :
    (squarefreeExceptionalCount φ X : ℝ) ≤
      (C * (2 : ℝ) ^ p / ((2 : ℝ) ^ p - 1)) * (X : ℝ) ^ p := by
  by_cases hX : X = 0
  · subst X
    simp [Real.zero_rpow (ne_of_gt hp)]
  · have hDpos : 0 < (2 : ℝ) ^ p - 1 :=
      sub_pos.mpr (Real.one_lt_rpow (by norm_num) hp)
    have hcutoff : X < 2 ^ (Nat.log 2 X + 1) := by
      exact Nat.lt_pow_succ_log_self Nat.one_lt_two X
    have hround : 2 ^ (Nat.log 2 X + 1) ≤ 2 * X := by
      rw [pow_succ]
      calc
        2 ^ Nat.log 2 X * 2 ≤ X * 2 :=
          Nat.mul_le_mul_right 2 (Nat.pow_log_le_self 2 hX)
        _ = 2 * X := by omega
    have hroundR : ((2 ^ (Nat.log 2 X + 1) : ℕ) : ℝ) ≤ 2 * (X : ℝ) := by
      exact_mod_cast hround
    have hpow : ((2 ^ (Nat.log 2 X + 1) : ℕ) : ℝ) ^ p ≤
        (2 : ℝ) ^ p * (X : ℝ) ^ p := by
      calc
        ((2 ^ (Nat.log 2 X + 1) : ℕ) : ℝ) ^ p ≤ (2 * (X : ℝ)) ^ p :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hroundR hp.le
        _ = (2 : ℝ) ^ p * (X : ℝ) ^ p :=
          Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)
    calc
      (squarefreeExceptionalCount φ X : ℝ) ≤
          C * ((2 ^ (Nat.log 2 X + 1) : ℕ) : ℝ) ^ p /
            ((2 : ℝ) ^ p - 1) :=
        squarefreeExceptionalCount_le_geometric_of_dyadic_bound_of_lt_pow
          hC hp hdyadic hcutoff
      _ ≤ C * ((2 : ℝ) ^ p * (X : ℝ) ^ p) / ((2 : ℝ) ^ p - 1) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC) hDpos.le
      _ = (C * (2 : ℝ) ^ p / ((2 : ℝ) ^ p - 1)) * (X : ℝ) ^ p := by ring

/-- The fixed-height squarefree estimate gives a single nonnegative constant
valid at every natural cutoff.  The constant may depend on the fixed height
and saving exponent, and the analytic input remains an explicit hypothesis.
-/
theorem exists_squarefree_global_power_bound_of_fixedHeightSquarefree
    (hfixed : FixedHeightSquarefree) {φ d : ℝ}
    (hφ : 3 ≤ φ) (hdpos : 0 < d) (hd : d < Delta φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ,
      (squarefreeExceptionalCount φ X : ℝ) ≤ C * (X : ℝ) ^ (1 - d) := by
  obtain ⟨C, hC, hdyadic⟩ :=
    exists_all_dyadic_bound_of_fixedHeightSquarefree hfixed hφ hdpos hd
  have hp : 0 < 1 - d := fixedHeight_power_exponent_pos hd
  refine ⟨C * (2 : ℝ) ^ (1 - d) / ((2 : ℝ) ^ (1 - d) - 1), ?_, ?_⟩
  · exact div_nonneg (mul_nonneg hC (Real.rpow_nonneg (by norm_num) _))
      (sub_pos.mpr (Real.one_lt_rpow (by norm_num) hp)).le
  · exact squarefreeExceptionalCount_le_power_of_dyadic_bound hC hp hdyadic

end PellPaper
