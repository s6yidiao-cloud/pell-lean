import Pell.FixedHeight
import Pell.PowerSaving
import Pell.SquarefreeGlobalReduction

/-!
# From fixed-height to global squarefree bounds

This file performs the finite bookkeeping which turns the eventual dyadic
estimate `FixedHeightSquarefree` into a uniform estimate on every dyadic
scale.  The finitely many scales before the `IsBigO` threshold are handled by
the elementary interval-length bound.  The resulting all-scale estimate can
then be summed by `SquarefreeGlobalReduction`.
-/

open Filter

namespace PellPaper

/-- For an exponent below `Delta θ`, the dyadic power exponent occurring in
the fixed-height estimate is positive. -/
theorem fixedHeight_power_exponent_pos {θ δ : ℝ}
    (hδ : δ < Delta θ) : 0 < 1 - δ := by
  have hhalf := Delta_le_one_half θ
  linarith

/-- The eventual fixed-height estimate can be made uniform over the special
dyadic scales.  The constant absorbs the finitely many scales below its
eventual threshold using `squarefreeDyadicExceptionalCount_le_scale`. -/
theorem exists_all_dyadic_bound_of_fixedHeightSquarefree
    (hfixed : FixedHeightSquarefree) {θ δ : ℝ}
    (hθ : 3 ≤ θ) (hδpos : 0 < δ) (hδ : δ < Delta θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ,
      (squarefreeDyadicExceptionalCount θ (2 ^ k) : ℝ) ≤
        C * ((2 ^ k : ℕ) : ℝ) ^ (1 - δ) := by
  have hp : 0 < 1 - δ := fixedHeight_power_exponent_pos hδ
  obtain ⟨c, hc⟩ := Asymptotics.isBigO_iff.mp
    (hfixed θ hθ δ hδpos hδ)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hc
  let C : ℝ := max c ((2 ^ N : ℕ) : ℝ)
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    exact (Nat.cast_nonneg _).trans (le_max_right _ _)
  · intro k
    have hscale_nonneg : 0 ≤ ((2 ^ k : ℕ) : ℝ) := Nat.cast_nonneg _
    have hpow_nonneg : 0 ≤ ((2 ^ k : ℕ) : ℝ) ^ (1 - δ) :=
      Real.rpow_nonneg hscale_nonneg _
    by_cases hk : k < N
    · have hpow_nat : 2 ^ k ≤ 2 ^ N :=
        Nat.pow_le_pow_right (by omega) (Nat.le_of_lt hk)
      have hscale_le_C : ((2 ^ k : ℕ) : ℝ) ≤ C := by
        calc
          ((2 ^ k : ℕ) : ℝ) ≤ ((2 ^ N : ℕ) : ℝ) := by
            exact_mod_cast hpow_nat
          _ ≤ C := by
            dsimp [C]
            exact le_max_right _ _
      have hcount_le_scale :
          (squarefreeDyadicExceptionalCount θ (2 ^ k) : ℝ) ≤
            ((2 ^ k : ℕ) : ℝ) := by
        exact_mod_cast squarefreeDyadicExceptionalCount_le_scale θ (2 ^ k)
      have hC_nonneg : 0 ≤ C := by
        dsimp [C]
        exact (Nat.cast_nonneg _).trans (le_max_right _ _)
      have hpow_one : 1 ≤ ((2 ^ k : ℕ) : ℝ) ^ (1 - δ) := by
        apply Real.one_le_rpow
        · exact_mod_cast Nat.one_le_two_pow
        · exact hp.le
      exact hcount_le_scale.trans
        (hscale_le_C.trans (le_mul_of_one_le_right hC_nonneg hpow_one))
    · have hNk : N ≤ k := Nat.le_of_not_gt hk
      have hNscale : N ≤ 2 ^ k := by
        exact hNk.trans (Nat.le_of_lt Nat.lt_two_pow_self)
      have hbound := hN (2 ^ k) hNscale
      have hcount_nonneg :
          0 ≤ (squarefreeDyadicExceptionalCount θ (2 ^ k) : ℝ) :=
        Nat.cast_nonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg hcount_nonneg,
        Real.norm_eq_abs, abs_of_nonneg hpow_nonneg] at hbound
      calc
        (squarefreeDyadicExceptionalCount θ (2 ^ k) : ℝ) ≤
            c * ((2 ^ k : ℕ) : ℝ) ^ (1 - δ) := hbound
        _ ≤ C * ((2 ^ k : ℕ) : ℝ) ^ (1 - δ) := by
          apply mul_le_mul_of_nonneg_right
          · dsimp [C]
            exact le_max_left _ _
          · exact hpow_nonneg

/-- The fixed-height squarefree estimate gives a single constant valid for
all power-of-two cutoffs.  This is the finite global squarefree conclusion;
the denominator is positive because `1 - δ > 0`. -/
theorem exists_squarefree_global_geometric_bound_of_fixedHeightSquarefree
    (hfixed : FixedHeightSquarefree) {θ δ : ℝ}
    (hθ : 3 ≤ θ) (hδpos : 0 < δ) (hδ : δ < Delta θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K : ℕ,
      (squarefreeExceptionalCount θ (2 ^ K - 1) : ℝ) ≤
        C * ((2 ^ K : ℕ) : ℝ) ^ (1 - δ) /
          ((2 : ℝ) ^ (1 - δ) - 1) := by
  obtain ⟨C, hC, hdyadic⟩ :=
    exists_all_dyadic_bound_of_fixedHeightSquarefree hfixed hθ hδpos hδ
  refine ⟨C, hC, ?_⟩
  intro K
  exact squarefreeExceptionalCount_le_geometric_of_dyadic_bound hC
    (fixedHeight_power_exponent_pos hδ) hdyadic K

end PellPaper
