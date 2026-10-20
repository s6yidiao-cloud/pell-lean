import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Elementary prime-power factors in the divisor estimate

These are independently authored Bernoulli estimates for the factors `k + 1`
in the divisor-count product.  They use only Mathlib, and hold for every
positive real exponent.  They neither assume nor yet prove a divisor-count
asymptotic.  The coefficient in the first estimate is independent of `p` and
`k`; the second has coefficient one above the explicit large-prime threshold.
-/

namespace PellPaper

/-- Bernoulli bounds a linear factor by a fixed multiple of a geometric one. -/
theorem nat_succ_le_geometric_multiple {x : ℝ} (hx : 1 < x) (k : ℕ) :
    (k : ℝ) + 1 ≤ (x / (x - 1)) * x ^ k := by
  calc
    (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ x ^ (k + 1) / (x - 1) := Nat.cast_le_pow_div_sub hx (k + 1)
    _ = (x / (x - 1)) * x ^ k := by rw [pow_succ]; ring

/-- Every prime-power divisor factor has one uniform geometric coefficient. -/
theorem nat_succ_le_uniform_rpow_factor {ε : ℝ} (hε : 0 < ε)
    {p : ℕ} (hp : 2 ≤ p) (k : ℕ) :
    (k : ℝ) + 1 ≤
      ((2 : ℝ) ^ ε / ((2 : ℝ) ^ ε - 1)) * ((p : ℝ) ^ ε) ^ k := by
  have hx : 1 < (2 : ℝ) ^ ε := Real.one_lt_rpow (by norm_num) hε
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  refine (nat_succ_le_geometric_multiple hx k).trans ?_
  apply mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity)
      (Real.rpow_le_rpow (by norm_num) hp' hε.le) k)
  exact div_nonneg (by positivity) (sub_nonneg.mpr hx.le)

/-- Above `p^ε ≥ 2`, no constant is lost in a prime-power divisor factor. -/
theorem nat_succ_le_rpow_factor_of_two_le {p ε : ℝ}
    (hpε : 2 ≤ p ^ ε) (k : ℕ) :
    (k : ℝ) + 1 ≤ (p ^ ε) ^ k := by
  have hbern := one_add_mul_sub_le_pow (show (-1 : ℝ) ≤ 2 by norm_num) k
  calc
    (k : ℝ) + 1 ≤ (2 : ℝ) ^ k := by
      norm_num at hbern
      simpa [add_comm] using hbern
    _ ≤ (p ^ ε) ^ k := pow_le_pow_left₀ (by norm_num) hpε k

end PellPaper
