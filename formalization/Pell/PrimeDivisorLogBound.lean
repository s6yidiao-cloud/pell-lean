import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# A logarithmic bound for distinct prime divisors

A finite set of distinct primes dividing a nonzero integer has product at
most its absolute value.  If every prime is at least a real number `B > 1`,
taking logarithms bounds the cardinality by `log |n| / log B`.  The filtered
version counts the actual divisors in a supplied finite prime set.  No
prime-distribution or prime-counting estimate is assumed.
-/

namespace PellPaper

open scoped BigOperators

/-- Distinct prime divisors of a nonzero integer, all at least `B > 1`,
number at most `log |n| / log B`. -/
theorem card_prime_divisors_le_log_div_log
    (P : Finset ℕ) (n : ℤ) (B : ℝ) (hn : n ≠ 0) (hB : 1 < B)
    (hprime : ∀ p ∈ P, p.Prime)
    (hlower : ∀ p ∈ P, B ≤ (p : ℝ))
    (hdvd : ∀ p ∈ P, (p : ℤ) ∣ n) :
    (P.card : ℝ) ≤ Real.log (n.natAbs : ℝ) / Real.log B := by
  have hBpos : 0 < B := lt_trans zero_lt_one hB
  have hnAbs : n.natAbs ≠ 0 := by simpa using hn
  have hsubset : P ⊆ n.natAbs.primeFactors := by
    intro p hp
    exact (hprime p hp).mem_primeFactors (Int.natCast_dvd.mp (hdvd p hp)) hnAbs
  have hprod_dvd : (∏ p ∈ P, p) ∣ n.natAbs :=
    (Finset.prod_dvd_prod_of_subset P n.natAbs.primeFactors id hsubset).trans
      (Nat.prod_primeFactors_dvd n.natAbs)
  have hprod_le : (∏ p ∈ P, (p : ℝ)) ≤ (n.natAbs : ℝ) := by
    rw [← Nat.cast_prod]
    exact Nat.cast_le.mpr (Nat.le_of_dvd (Nat.pos_of_ne_zero hnAbs) hprod_dvd)
  have hpow_le : B ^ P.card ≤ (n.natAbs : ℝ) := by
    calc
      B ^ P.card = ∏ _p ∈ P, B := (Finset.prod_const B).symm
      _ ≤ ∏ p ∈ P, (p : ℝ) :=
        Finset.prod_le_prod (fun _ _ => hBpos.le) hlower
      _ ≤ (n.natAbs : ℝ) := hprod_le
  apply (le_div_iff₀ (Real.log_pos hB)).mpr
  simpa only [Real.log_pow] using Real.log_le_log (pow_pos hBpos _) hpow_le

/-- The literal divisibility filter on any finite set of primes at least
`B > 1` satisfies the same logarithmic cardinality bound. -/
theorem card_filter_int_dvd_le_log_div_log
    (P : Finset ℕ) (n : ℤ) (B : ℝ) (hn : n ≠ 0) (hB : 1 < B)
    (hprime : ∀ p ∈ P, p.Prime)
    (hlower : ∀ p ∈ P, B ≤ (p : ℝ)) :
    ((P.filter (fun p : ℕ => (p : ℤ) ∣ n)).card : ℝ) ≤
      Real.log (n.natAbs : ℝ) / Real.log B := by
  apply card_prime_divisors_le_log_div_log _ n B hn hB
  · intro p hp
    exact hprime p (Finset.mem_filter.mp hp).1
  · intro p hp
    exact hlower p (Finset.mem_filter.mp hp).1
  · intro p hp
    exact (Finset.mem_filter.mp hp).2

end PellPaper
