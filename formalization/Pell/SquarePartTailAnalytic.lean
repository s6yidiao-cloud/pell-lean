import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Tactic
import Pell.SquarePartTail

/-!
# The elementary large-square-divisor tail estimate

For `S ≥ 2`, comparison with the telescoping sum
`1 / (s - 1) - 1 / s` gives an explicit bound `X / (S - 1)` for
the sum of floors counting large square divisors.  There is no error term,
since each natural-number quotient is bounded above by its real quotient.
-/

open scoped BigOperators

namespace PellPaper

/-- A reciprocal square is bounded by a telescoping difference. -/
theorem reciprocal_square_le_sub {s : ℕ} (hs : 2 ≤ s) :
    1 / (s : ℝ) ^ 2 ≤ 1 / ((s : ℝ) - 1) - 1 / (s : ℝ) := by
  have hs2 : (2 : ℝ) ≤ s := by exact_mod_cast hs
  have hs0 : (0 : ℝ) < s := by linarith
  have hs1 : (0 : ℝ) < (s : ℝ) - 1 := by linarith
  calc
    1 / (s : ℝ) ^ 2 ≤ 1 / ((s : ℝ) * ((s : ℝ) - 1)) := by
      apply one_div_le_one_div_of_le (mul_pos hs0 hs1)
      nlinarith
    _ = 1 / ((s : ℝ) - 1) - 1 / (s : ℝ) := by
      field_simp
      ring

/-- An explicit finite reciprocal-square tail bound, retaining the terminal
term when the interval is nonempty. -/
theorem sum_reciprocal_square_le_sub {S N : ℕ} (hS : 2 ≤ S) (hSN : S ≤ N) :
    (∑ s ∈ Finset.Icc S N, 1 / (s : ℝ) ^ 2) ≤
      1 / ((S : ℝ) - 1) - 1 / (N : ℝ) := by
  calc
    _ ≤ ∑ s ∈ Finset.Icc S N,
        (1 / ((s : ℝ) - 1) - 1 / (s : ℝ)) := by
      apply Finset.sum_le_sum
      intro s hs
      exact reciprocal_square_le_sub (hS.trans (Finset.mem_Icc.mp hs).1)
    _ = 1 / ((S : ℝ) - 1) - 1 / (N : ℝ) := by
      have h := Finset.sum_Icc_sub hSN (fun s : ℕ => -(1 / ((s : ℝ) - 1)))
      simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, neg_sub_neg] using h

/-- The bound also holds when the summation interval is empty. -/
theorem sum_reciprocal_square_le {S N : ℕ} (hS : 2 ≤ S) :
    (∑ s ∈ Finset.Icc S N, 1 / (s : ℝ) ^ 2) ≤ 1 / ((S : ℝ) - 1) := by
  by_cases hSN : S ≤ N
  · exact (sum_reciprocal_square_le_sub hS hSN).trans
      (sub_le_self _ (by positivity))
  · rw [Finset.Icc_eq_empty_of_lt (lt_of_not_ge hSN), Finset.sum_empty]
    have hS2 : (2 : ℝ) ≤ S := by exact_mod_cast hS
    exact one_div_nonneg.mpr (by linarith)

/-- The sum of the exact counts of square multiples is at most `X / (S - 1)`.
The upper summation cutoff `N` is arbitrary. -/
theorem square_divisor_sum_le {X S N : ℕ} (hS : 2 ≤ S) :
    ((∑ s ∈ Finset.Icc S N, X / s ^ 2 : ℕ) : ℝ) ≤
      (X : ℝ) / ((S : ℝ) - 1) := by
  calc
    _ = ∑ s ∈ Finset.Icc S N, ((X / s ^ 2 : ℕ) : ℝ) := by
      rw [Nat.cast_sum]
    _ ≤ ∑ s ∈ Finset.Icc S N, (X : ℝ) * (1 / (s : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro s _
      have h : ((X / s ^ 2 : ℕ) : ℝ) ≤ (X : ℝ) / ((s ^ 2 : ℕ) : ℝ) :=
        Nat.cast_div_le
      simpa only [Nat.cast_pow, mul_one_div] using h
    _ = (X : ℝ) * ∑ s ∈ Finset.Icc S N, 1 / (s : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
    _ ≤ (X : ℝ) * (1 / ((S : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_left (sum_reciprocal_square_le hS) (Nat.cast_nonneg X)
    _ = (X : ℝ) / ((S : ℝ) - 1) := by rw [mul_one_div]

/-- A sharp explicit large-square-divisor count. -/
theorem squareDivisorTail_card_le_div {X S : ℕ} (hS : 2 ≤ S) :
    ((squareDivisorTail X S).card : ℝ) ≤ (X : ℝ) / ((S : ℝ) - 1) := by
  have h : ((squareDivisorTail X S).card : ℝ) ≤
      ((∑ s ∈ Finset.Icc S X, X / s ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast squareDivisorTail_card_le X S
  exact h.trans (square_divisor_sum_le hS)

/-- Any specified family of positive radicands with large square divisors
inherits the analytic tail estimate. -/
theorem card_le_div_of_square_divisors {A : Finset ℕ} {X S : ℕ} (hS : 2 ≤ S)
    (hA : ∀ m ∈ A, 0 < m ∧ m ≤ X ∧ ∃ s : ℕ, S ≤ s ∧ s ^ 2 ∣ m) :
    (A.card : ℝ) ≤ (X : ℝ) / ((S : ℝ) - 1) := by
  have h : (A.card : ℝ) ≤ ((∑ s ∈ Finset.Icc S X, X / s ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast card_le_square_divisor_sum hA
  exact h.trans (square_divisor_sum_le hS)

/-- A version stated directly with square-part decompositions. -/
theorem card_le_div_of_square_part_decompositions {A : Finset ℕ} {X S : ℕ}
    (hS : 2 ≤ S)
    (hA : ∀ m ∈ A, 0 < m ∧ m ≤ X ∧
      ∃ s w : ℕ, S ≤ s ∧ m = s ^ 2 * w) :
    (A.card : ℝ) ≤ (X : ℝ) / ((S : ℝ) - 1) := by
  apply card_le_div_of_square_divisors hS
  intro m hm
  obtain ⟨hm0, hmX, s, w, hSs, hdecomp⟩ := hA m hm
  exact ⟨hm0, hmX, s, hSs, ⟨w, hdecomp⟩⟩

/-- The convenient `2 X / S` form used when the threshold itself is a power
of the main cutoff. -/
theorem squareDivisorTail_card_le_two_mul_div {X S : ℕ} (hS : 2 ≤ S) :
    ((squareDivisorTail X S).card : ℝ) ≤ 2 * (X : ℝ) / (S : ℝ) := by
  have hS2 : (2 : ℝ) ≤ S := by exact_mod_cast hS
  have hS0 : (0 : ℝ) < S := by linarith
  have hS1 : (0 : ℝ) < (S : ℝ) - 1 := by linarith
  apply (squareDivisorTail_card_le_div hS).trans
  apply (div_le_div_iff₀ hS1 hS0).mpr
  nlinarith [Nat.cast_nonneg (α := ℝ) X]

end PellPaper
