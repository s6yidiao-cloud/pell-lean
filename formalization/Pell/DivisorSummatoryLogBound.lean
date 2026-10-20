import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

/-!
# A logarithmic summatory bound for the divisor-counting function

This is the elementary average-order input needed by the direct
shifted-square congruence estimate.  Mathlib already proves the exact identity
expressing the summatory divisor function as a sum of floors.  Casting those
floors to `ℝ` and applying the standard harmonic-number bound gives the
required uniform logarithmic estimate.
-/

namespace PellPaper

open ArithmeticFunction

noncomputable section

/-- The exact Dirichlet-hyperbola identity, restated using cardinalities of
the positive-divisor finsets. -/
theorem sum_Ioc_card_divisors_eq_sum_div (Z : ℕ) :
    ∑ n ∈ Finset.Ioc 0 Z, n.divisors.card =
      ∑ n ∈ Finset.Ioc 0 Z, Z / n := by
  simpa only [ArithmeticFunction.sigma_zero_apply] using
    ArithmeticFunction.sum_Ioc_sigma0_eq_sum_div Z

/-- The summatory divisor-counting function is at most
`Z * (1 + log Z)`.  The statement is valid also at `Z = 0`. -/
theorem sum_Ioc_card_divisors_cast_le_mul_one_add_log (Z : ℕ) :
    ((∑ n ∈ Finset.Ioc 0 Z, n.divisors.card : ℕ) : ℝ) ≤
      (Z : ℝ) * (1 + Real.log (Z : ℝ)) := by
  rw [sum_Ioc_card_divisors_eq_sum_div, Nat.cast_sum]
  calc
    ∑ n ∈ Finset.Ioc 0 Z, ((Z / n : ℕ) : ℝ) ≤
        ∑ n ∈ Finset.Ioc 0 Z, (Z : ℝ) / (n : ℝ) := by
      gcongr with n hn
      exact Nat.cast_div_le
    _ = (Z : ℝ) * (harmonic Z : ℝ) := by
      have hfin : Finset.Ioc 0 Z = Finset.Icc 1 Z := by
        ext n
        simp only [Finset.mem_Ioc, Finset.mem_Icc]
        omega
      rw [hfin, harmonic_eq_sum_Icc]
      simp [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
        Finset.mul_sum, div_eq_mul_inv]
    _ ≤ (Z : ℝ) * (1 + Real.log (Z : ℝ)) := by
      exact mul_le_mul_of_nonneg_left (harmonic_le_one_add_log Z)
        (Nat.cast_nonneg Z)

end

end PellPaper
