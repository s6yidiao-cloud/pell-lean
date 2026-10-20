import Pell.DivisorCountSubpower
import Mathlib.Analysis.PSeries

/-!
# A convergent divisor-weighted conductor budget

The divisor sum at a positive conductor is at most the conductor times its
divisor count. The checked subpower estimate then proves convergence with
denominator exponent `5/2`. This is the unconditional analytic budget for a
future conductor descent; it does not assume or prove a class-number bound.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- The sum of positive divisors is bounded by `n` times their count,
including `n = 0` with Mathlib's empty divisor set convention. -/
theorem sum_divisors_le_mul_card (n : ℕ) :
    (∑ d ∈ n.divisors, (d : ℝ)) ≤ (n : ℝ) * n.divisors.card := by
  calc
    (∑ d ∈ n.divisors, (d : ℝ)) ≤ ∑ _d ∈ n.divisors, (n : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2)
        (Nat.dvd_of_mem_divisors hd)
    _ = (n : ℝ) * n.divisors.card := by simp [mul_comm]

/-- The literal divisor-weighted conductor series converges. The exponent is
real, and its totalized term at conductor zero is zero. -/
theorem summable_sum_divisors_div_rpow_five_halves :
    Summable (fun n : ℕ ↦ (∑ d ∈ n.divisors, (d : ℝ)) /
      (n : ℝ) ^ (5 / 2 : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := exists_pos_card_divisors_le_rpow (1 / 4) (by norm_num)
  have hs : Summable (fun n : ℕ ↦ C * (n : ℝ) ^ (-5 / 4 : ℝ)) :=
    (Real.summable_nat_rpow.mpr (by norm_num)).mul_left C
  apply Summable.of_nonneg_of_le (fun n ↦ by positivity) _ hs
  intro n
  by_cases hn : n = 0
  · subst n
    simp
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hnreal : 0 < (n : ℝ) := by exact_mod_cast hnpos
    calc
      (∑ d ∈ n.divisors, (d : ℝ)) / (n : ℝ) ^ (5 / 2 : ℝ) ≤
          ((n : ℝ) * (C * (n : ℝ) ^ (1 / 4 : ℝ))) /
            (n : ℝ) ^ (5 / 2 : ℝ) := by
        apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg hnreal.le _)
        exact (sum_divisors_le_mul_card n).trans
          (mul_le_mul_of_nonneg_left (hbound n hnpos) hnreal.le)
      _ = C * (n : ℝ) ^ (-5 / 4 : ℝ) := by
        rw [mul_left_comm (n : ℝ) C, mul_div_assoc]
        congr 1
        nth_rw 1 [← Real.rpow_one (n : ℝ)]
        rw [← Real.rpow_add hnreal, ← Real.rpow_sub hnreal]
        norm_num

/-- One positive constant bounds every finite collection of conductors. -/
theorem exists_pos_sum_divisors_div_rpow_five_halves_le :
    ∃ C : ℝ, 0 < C ∧ ∀ s : Finset ℕ,
      (∑ n ∈ s, (∑ d ∈ n.divisors, (d : ℝ)) /
        (n : ℝ) ^ (5 / 2 : ℝ)) ≤ C := by
  let w : ℕ → ℝ := fun n ↦ (∑ d ∈ n.divisors, (d : ℝ)) /
    (n : ℝ) ^ (5 / 2 : ℝ)
  have hw : ∀ n, 0 ≤ w n := fun n ↦ by dsimp [w]; positivity
  have hs : Summable w := summable_sum_divisors_div_rpow_five_halves
  have ht : 0 ≤ ∑' n, w n := tsum_nonneg hw
  refine ⟨(∑' n, w n) + 1, by linarith, ?_⟩
  intro s
  exact (hs.sum_le_tsum s (fun n _ ↦ hw n)).trans (by linarith)

end
end PellPaper
