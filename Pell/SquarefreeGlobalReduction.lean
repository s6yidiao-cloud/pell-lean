import Pell.SquarefreeDyadicCover
import Mathlib.Algebra.Field.GeomSum

/-!
# Finite global summation for squarefree Pell exceptions

The fixed-height proposition is a dyadic statement.  This file proves the
purely finite passage from a power bound on every dyadic block to a bound for
the squarefree global exceptional set below a power-of-two cutoff.  The
analytic estimate for the blocks remains an explicit hypothesis.
-/

namespace PellPaper

/-- A finite geometric sum with ratio greater than one is bounded by its last
power divided by `r - 1`. -/
theorem sum_pow_le_geometric {r : ℝ} (hr : 1 < r) (K : ℕ) :
    ∑ k ∈ Finset.range K, r ^ k ≤ r ^ K / (r - 1) := by
  rw [geom_sum_eq (ne_of_gt hr) K]
  apply div_le_div_of_nonneg_right
  · linarith
  · linarith

/-- A power of a dyadic natural scale is a geometric term with ratio
`2^p`. -/
theorem cast_two_pow_rpow_eq_rpow_pow (p : ℝ) (k : ℕ) :
    ((2 ^ k : ℕ) : ℝ) ^ p = ((2 : ℝ) ^ p) ^ k := by
  rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast (2 : ℝ) k,
    ← Real.rpow_mul (by positivity : 0 ≤ (2 : ℝ)), mul_comm,
    Real.rpow_mul_natCast (by positivity : 0 ≤ (2 : ℝ))]

/-- The powers of the dyadic scales have an explicit finite geometric-series
bound for every positive real exponent. -/
theorem sum_cast_two_pow_rpow_le (p : ℝ) (hp : 0 < p) (K : ℕ) :
    ∑ k ∈ Finset.range K, ((2 ^ k : ℕ) : ℝ) ^ p ≤
      ((2 ^ K : ℕ) : ℝ) ^ p / ((2 : ℝ) ^ p - 1) := by
  simp_rw [cast_two_pow_rpow_eq_rpow_pow]
  exact sum_pow_le_geometric (Real.one_lt_rpow (by norm_num) hp) K

/-- A pointwise dyadic power bound gives a global squarefree exceptional-set
bound below the strict cutoff `2^K`.  This is finite and uniform in `K`; the
constant `C` and exponent `p` are parameters of the assumed blockwise bound.
-/
theorem squarefreeExceptionalCount_le_geometric_of_dyadic_bound
    {θ C p : ℝ} (hC : 0 ≤ C) (hp : 0 < p)
    (hdyadic : ∀ k : ℕ,
      (squarefreeDyadicExceptionalCount θ (2 ^ k) : ℝ) ≤
        C * ((2 ^ k : ℕ) : ℝ) ^ p)
    (K : ℕ) :
    (squarefreeExceptionalCount θ (2 ^ K - 1) : ℝ) ≤
      C * ((2 ^ K : ℕ) : ℝ) ^ p / ((2 : ℝ) ^ p - 1) := by
  have hcover := squarefreeExceptionalCount_le_sum_squarefreeDyadicExceptionalCount θ K
  have hcoverR : (squarefreeExceptionalCount θ (2 ^ K - 1) : ℝ) ≤
      ∑ k ∈ Finset.range K,
        (squarefreeDyadicExceptionalCount θ (2 ^ k) : ℝ) := by
    exact_mod_cast hcover
  calc
    (squarefreeExceptionalCount θ (2 ^ K - 1) : ℝ) ≤
        ∑ k ∈ Finset.range K,
          (squarefreeDyadicExceptionalCount θ (2 ^ k) : ℝ) := hcoverR
    _ ≤ ∑ k ∈ Finset.range K, C * ((2 ^ k : ℕ) : ℝ) ^ p := by
      exact Finset.sum_le_sum fun k hk => hdyadic k
    _ = C * ∑ k ∈ Finset.range K, ((2 ^ k : ℕ) : ℝ) ^ p := by
      rw [Finset.mul_sum]
    _ ≤ C * (((2 ^ K : ℕ) : ℝ) ^ p / ((2 : ℝ) ^ p - 1)) := by
      exact mul_le_mul_of_nonneg_left (sum_cast_two_pow_rpow_le p hp K) hC
    _ = C * ((2 ^ K : ℕ) : ℝ) ^ p / ((2 : ℝ) ^ p - 1) := by ring

/-- The same finite reduction applies to any integer cutoff strictly below
`2^K`, with the same explicit dyadic majorant. -/
theorem squarefreeExceptionalCount_le_geometric_of_dyadic_bound_of_lt_pow
    {θ C p : ℝ} (hC : 0 ≤ C) (hp : 0 < p)
    (hdyadic : ∀ k : ℕ,
      (squarefreeDyadicExceptionalCount θ (2 ^ k) : ℝ) ≤
        C * ((2 ^ k : ℕ) : ℝ) ^ p)
    {X K : ℕ} (hX : X < 2 ^ K) :
    (squarefreeExceptionalCount θ X : ℝ) ≤
      C * ((2 ^ K : ℕ) : ℝ) ^ p / ((2 : ℝ) ^ p - 1) := by
  have hcover :=
    squarefreeExceptionalCount_le_sum_squarefreeDyadicExceptionalCount_of_lt_pow
      θ hX
  have hcoverR : (squarefreeExceptionalCount θ X : ℝ) ≤
      ∑ k ∈ Finset.range K,
        (squarefreeDyadicExceptionalCount θ (2 ^ k) : ℝ) := by
    exact_mod_cast hcover
  calc
    (squarefreeExceptionalCount θ X : ℝ) ≤
        ∑ k ∈ Finset.range K,
          (squarefreeDyadicExceptionalCount θ (2 ^ k) : ℝ) := hcoverR
    _ ≤ ∑ k ∈ Finset.range K, C * ((2 ^ k : ℕ) : ℝ) ^ p := by
      exact Finset.sum_le_sum fun k hk => hdyadic k
    _ = C * ∑ k ∈ Finset.range K, ((2 ^ k : ℕ) : ℝ) ^ p := by
      rw [Finset.mul_sum]
    _ ≤ C * (((2 ^ K : ℕ) : ℝ) ^ p / ((2 : ℝ) ^ p - 1)) := by
      exact mul_le_mul_of_nonneg_left (sum_cast_two_pow_rpow_le p hp K) hC
    _ = C * ((2 ^ K : ℕ) : ℝ) ^ p / ((2 : ℝ) ^ p - 1) := by ring

end PellPaper
