import Pell.GeneralScaledFiberBound

/-!
# Finite root bands with an endpoint height budget

For positive roots in the closed interval `Finset.Icc L U`, the height
budget at `U` implies every individual height budget.  The natural cutoff
`(2 * Y - 1) / L ^ 2` bounds all the individual scaled cutoffs, so summing
the ordinary transferred-fiber bounds costs exactly `U - L + 1` roots.

The conditional constant is uniform in the original height, scale, and
band endpoints.  The root-count factor is retained, and this finite
summation does not by itself assert a power saving.
-/

open scoped BigOperators

namespace PellPaper

/-- Summing a scaled fiber bound over a positive closed root band, using
only the upper endpoint for the height budget and the lower endpoint for
the cutoff.  The same fiber-bound constant is retained. -/
theorem sum_dyadicTransferredSquarefreeSet_card_le_rootBand_scaled_power_of_fiber_bound
    {theta phi d C : ℝ} {Y L U : ℕ}
    (hphi : 0 ≤ phi) (hd : d ≤ 1) (hC : 0 ≤ C)
    (hfiber : ∀ s : ℕ, 0 < s →
      (s : ℝ) ^ (2 * phi) ≤ (Y : ℝ) ^ (phi - theta) →
      ((dyadicTransferredSquarefreeSet theta Y s).card : ℝ) ≤
        C * (((2 * Y - 1) / s ^ 2 : ℕ) : ℝ) ^ (1 - d))
    (hL : 0 < L) (hLU : L ≤ U)
    (hbudget : (U : ℝ) ^ (2 * phi) ≤ (Y : ℝ) ^ (phi - theta)) :
    (∑ s ∈ Finset.Icc L U,
      ((dyadicTransferredSquarefreeSet theta Y s).card : ℝ)) ≤
        ((U - L + 1 : ℕ) : ℝ) * C *
          (((2 * Y - 1) / L ^ 2 : ℕ) : ℝ) ^ (1 - d) := by
  have hterm : ∀ s ∈ Finset.Icc L U,
      ((dyadicTransferredSquarefreeSet theta Y s).card : ℝ) ≤
        C * (((2 * Y - 1) / L ^ 2 : ℕ) : ℝ) ^ (1 - d) := by
    intro s hs
    obtain ⟨hLs, hsU⟩ := Finset.mem_Icc.mp hs
    have hspos : 0 < s := hL.trans_le hLs
    have hsbudget : (s : ℝ) ^ (2 * phi) ≤ (Y : ℝ) ^ (phi - theta) := by
      exact (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hsU)
        (mul_nonneg (by norm_num) hphi)).trans hbudget
    have hcutoff : (2 * Y - 1) / s ^ 2 ≤ (2 * Y - 1) / L ^ 2 := by
      exact Nat.div_le_div_left (Nat.pow_le_pow_left hLs 2) (pow_pos hL 2)
    calc
      ((dyadicTransferredSquarefreeSet theta Y s).card : ℝ) ≤
          C * (((2 * Y - 1) / s ^ 2 : ℕ) : ℝ) ^ (1 - d) :=
        hfiber s hspos hsbudget
      _ ≤ C * (((2 * Y - 1) / L ^ 2 : ℕ) : ℝ) ^ (1 - d) := by
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hcutoff)
            (sub_nonneg.mpr hd)) hC
  calc
    (∑ s ∈ Finset.Icc L U,
        ((dyadicTransferredSquarefreeSet theta Y s).card : ℝ)) ≤
        ∑ _s ∈ Finset.Icc L U,
          C * (((2 * Y - 1) / L ^ 2 : ℕ) : ℝ) ^ (1 - d) :=
      Finset.sum_le_sum hterm
    _ = ((U - L + 1 : ℕ) : ℝ) * C *
          (((2 * Y - 1) / L ^ 2 : ℕ) : ℝ) ^ (1 - d) := by
      have hcount : U + 1 - L = U - L + 1 := by omega
      simp only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, hcount]
      ring

/-- Conditional finite-band bound for the ordinary transferred fibers.
For fixed target height and saving exponent, one constant works for every
original height `theta ≤ phi`, scale, and positive nonempty root band
satisfying the single upper-endpoint height budget.  Both the exact root
count and the natural lower-endpoint scaled cutoff are retained. -/
theorem exists_sum_dyadicTransferredSquarefreeSet_card_rootBand_scaled_power_bound_of_FixedHeightSquarefree
    (hfixed : FixedHeightSquarefree) {phi d : ℝ}
    (hphi : 3 ≤ phi) (hdpos : 0 < d) (hd : d < Delta phi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ theta : ℝ, theta ≤ phi → ∀ Y L U : ℕ,
      0 < L → L ≤ U →
      (U : ℝ) ^ (2 * phi) ≤ (Y : ℝ) ^ (phi - theta) →
      (∑ s ∈ Finset.Icc L U,
        ((dyadicTransferredSquarefreeSet theta Y s).card : ℝ)) ≤
          ((U - L + 1 : ℕ) : ℝ) * C *
            (((2 * Y - 1) / L ^ 2 : ℕ) : ℝ) ^ (1 - d) := by
  obtain ⟨C, hC, hfiber⟩ :=
    exists_dyadicTransferredSquarefreeSet_scaled_power_bound_of_FixedHeightSquarefree
      hfixed hphi hdpos hd
  refine ⟨C, hC, ?_⟩
  intro theta htheta_phi Y L U hL hLU hbudget
  have hp : 0 < 1 - d := fixedHeight_power_exponent_pos hd
  exact sum_dyadicTransferredSquarefreeSet_card_le_rootBand_scaled_power_of_fiber_bound
    (by linarith) (by linarith) hC (hfiber theta htheta_phi Y) hL hLU hbudget

end PellPaper
