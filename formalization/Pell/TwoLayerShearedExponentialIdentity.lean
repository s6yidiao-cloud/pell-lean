import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Sheared logarithmic coordinates for two-layer monomials

The two-layer determinant bookkeeping replaces the ordinary exponent pair
`(a,b)` by the sheared pair `(a + 2b,b)`.  This file records the exact
exponential identity behind that replacement.  It is a local identity for
positive real scales, independent of any determinant estimate or rank
argument.
-/

namespace PellPaper

/-- A two-layer monomial at positive real scales has the exact exponential
description in the sheared coordinates `(a + 2b,b)`:
`S^a T^b = exp ((a + 2b) log S + b (log T - 2 log S))`.

The natural exponents are retained on the left, while every exponent in the
logarithmic expression is cast to `ℝ`. -/
theorem twoLayer_pow_mul_eq_exp_shearedLog
    {S T : ℝ} (hS : 0 < S) (hT : 0 < T) (a b : ℕ) :
    S ^ a * T ^ b =
      Real.exp (((a + 2 * b : ℕ) : ℝ) * Real.log S +
        (b : ℝ) * (Real.log T - 2 * Real.log S)) := by
  have hS_pow : S ^ a = Real.exp ((a : ℝ) * Real.log S) := by
    rw [Real.exp_nat_mul, Real.exp_log hS]
  have hT_pow : T ^ b = Real.exp ((b : ℝ) * Real.log T) := by
    rw [Real.exp_nat_mul, Real.exp_log hT]
  rw [hS_pow, hT_pow, ← Real.exp_add]
  congr 1
  push_cast
  ring

end PellPaper
