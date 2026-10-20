import Pell.WilsonSquareDiagonalDivisorBounds

/-!
# Euler-factor cancellation on Wilson's square diagonal

For the specialization `f(n) = 1 / tau(n)`, Wilson's complementary local
factor is `fHat(p) = 1/2`.  Lemma 2.2 therefore introduces

`g_P(n) = ∏_{p ∣ P, p ∣ n} (1 - 1/(2p))⁻¹`.

The square contribution actually carries `(phi(n)/n) * g_P(n)`.  Prime by
prime this product is at most one: outside `P` its local factor is
`1 - 1/p`, and inside `P` it is

`(1 - 1/p) / (1 - 1/(2p))`.

This file proves that cancellation exactly and transfers the already proved
`sum tau(n^2) = O(N log^2 N)` estimate to the weighted diagonal.  No
analytic estimate is used here.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- Wilson's finite `g_z` Euler product for the reciprocal-divisor
specialization, with the sieve product supplied explicitly as `P`. -/
def main4WilsonReciprocalDivisorSieveFactor (P n : ℕ) : ℝ :=
  ∏ p ∈ n.primeFactors.filter (fun p ↦ p ∣ P),
    (1 - (2 * (p : ℝ))⁻¹)⁻¹

/-- The combined local factor of `phi(n)/n` and Wilson's `g_z(n)`. -/
def main4WilsonReciprocalDivisorCombinedLocalFactor (P p : ℕ) : ℝ :=
  (1 - (p : ℝ)⁻¹) *
    if p ∣ P then (1 - (2 * (p : ℝ))⁻¹)⁻¹ else 1

/-- Real Euler product formula for the totient ratio. -/
theorem main4WilsonTotientRatio_eq_prod_primeFactors
    (n : ℕ) (hn : n ≠ 0) :
    (n.totient : ℝ) / (n : ℝ) =
      ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹) := by
  have hq := Nat.totient_eq_mul_prod_factors n
  have hr : (n.totient : ℝ) =
      (n : ℝ) * ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹) := by
    simpa using congrArg (fun x : ℚ ↦ (x : ℝ)) hq
  rw [hr]
  field_simp

private theorem reciprocalDivisorCombinedLocalFactor_mem_unitInterval
    (p P : ℕ) (hp : p.Prime) :
    0 ≤ main4WilsonReciprocalDivisorCombinedLocalFactor P p ∧
      main4WilsonReciprocalDivisorCombinedLocalFactor P p ≤ 1 := by
  have hpR : 2 ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hpR0 : 0 < (p : ℝ) := lt_of_lt_of_le (by norm_num) hpR
  have hnum : 0 ≤ 1 - (p : ℝ)⁻¹ := by
    have hinv : (p : ℝ)⁻¹ ≤ 1 := by
      rw [inv_le_one₀ hpR0]
      exact_mod_cast hp.one_le
    linarith
  by_cases hP : p ∣ P
  · have hden : 0 < 1 - (2 * (p : ℝ))⁻¹ := by
      have hinv : (2 * (p : ℝ))⁻¹ < 1 := by
        rw [inv_lt_one₀ (by positivity : (0 : ℝ) < 2 * (p : ℝ))]
        nlinarith
      linarith
    have hratioNonneg :
        0 ≤ (1 - (p : ℝ)⁻¹) * (1 - (2 * (p : ℝ))⁻¹)⁻¹ :=
      mul_nonneg hnum (inv_nonneg.mpr hden.le)
    have hratioLe :
        (1 - (p : ℝ)⁻¹) * (1 - (2 * (p : ℝ))⁻¹)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one₀ hden]
      have hhalf : (2 * (p : ℝ))⁻¹ ≤ (p : ℝ)⁻¹ :=
        inv_anti₀ hpR0 (by nlinarith)
      linarith
    simpa [main4WilsonReciprocalDivisorCombinedLocalFactor, hP] using
      And.intro hratioNonneg hratioLe
  · have hinvNonneg : 0 ≤ (p : ℝ)⁻¹ := by positivity
    constructor
    · simpa [main4WilsonReciprocalDivisorCombinedLocalFactor, hP] using hnum
    · simp only [main4WilsonReciprocalDivisorCombinedLocalFactor, hP,
        ↓reduceIte, mul_one]
      linarith

/-- Exact prime-by-prime combination of the totient ratio and Wilson's
reciprocal-divisor sieve factor. -/
theorem main4WilsonTotientRatio_mul_sieveFactor_eq_prod_combinedLocalFactor
    (P n : ℕ) (hn : n ≠ 0) :
    (n.totient : ℝ) / (n : ℝ) *
        main4WilsonReciprocalDivisorSieveFactor P n =
      ∏ p ∈ n.primeFactors,
        main4WilsonReciprocalDivisorCombinedLocalFactor P p := by
  rw [main4WilsonTotientRatio_eq_prod_primeFactors n hn]
  simp only [main4WilsonReciprocalDivisorSieveFactor, Finset.prod_filter,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  simp only [main4WilsonReciprocalDivisorCombinedLocalFactor]

/-- Wilson's full local correction `(phi(n)/n) * g_z(n)` is nonnegative. -/
theorem main4WilsonTotientRatio_mul_reciprocalDivisorSieveFactor_nonneg
    (P n : ℕ) (hn : n ≠ 0) :
    0 ≤ (n.totient : ℝ) / (n : ℝ) *
      main4WilsonReciprocalDivisorSieveFactor P n := by
  rw [main4WilsonTotientRatio_mul_sieveFactor_eq_prod_combinedLocalFactor
    P n hn]
  apply Finset.prod_nonneg
  intro p hp
  exact (reciprocalDivisorCombinedLocalFactor_mem_unitInterval p P
    (Nat.prime_of_mem_primeFactors hp)).1

/-- Wilson's full local correction `(phi(n)/n) * g_z(n)` is at most one. -/
theorem main4WilsonTotientRatio_mul_reciprocalDivisorSieveFactor_le_one
    (P n : ℕ) (hn : n ≠ 0) :
    (n.totient : ℝ) / (n : ℝ) *
        main4WilsonReciprocalDivisorSieveFactor P n ≤ 1 := by
  rw [main4WilsonTotientRatio_mul_sieveFactor_eq_prod_combinedLocalFactor
    P n hn]
  apply Finset.prod_le_one
  · intro p hp
    exact (reciprocalDivisorCombinedLocalFactor_mem_unitInterval p P
      (Nat.prime_of_mem_primeFactors hp)).1
  · intro p hp
    exact (reciprocalDivisorCombinedLocalFactor_mem_unitInterval p P
      (Nat.prime_of_mem_primeFactors hp)).2

/-- The square-diagonal main term, including the full `phi/n * g_z` factor,
is bounded by the elementary unweighted divisor sum. -/
theorem sum_Ioc_card_divisors_sq_mul_totientRatio_sieveFactor_le
    (P N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N,
        ((n ^ 2).divisors.card : ℝ) *
          ((n.totient : ℝ) / (n : ℝ) *
            main4WilsonReciprocalDivisorSieveFactor P n) ≤
      (N : ℝ) * (1 + Real.log (N : ℝ)) ^ 2 := by
  calc
    ∑ n ∈ Finset.Ioc 0 N,
        ((n ^ 2).divisors.card : ℝ) *
          ((n.totient : ℝ) / (n : ℝ) *
            main4WilsonReciprocalDivisorSieveFactor P n) ≤
        ∑ n ∈ Finset.Ioc 0 N, ((n ^ 2).divisors.card : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hn0 : n ≠ 0 := Nat.ne_of_gt (Finset.mem_Ioc.mp hn).1
      calc
        ((n ^ 2).divisors.card : ℝ) *
            ((n.totient : ℝ) / (n : ℝ) *
              main4WilsonReciprocalDivisorSieveFactor P n) ≤
            ((n ^ 2).divisors.card : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left
            (main4WilsonTotientRatio_mul_reciprocalDivisorSieveFactor_le_one
              P n hn0) (by positivity)
        _ = ((n ^ 2).divisors.card : ℝ) := by ring
    _ ≤ (N : ℝ) * (1 + Real.log (N : ℝ)) ^ 2 :=
      sum_Ioc_card_divisors_sq_real_le_mul_one_add_log_sq N

end

end PellPaper
