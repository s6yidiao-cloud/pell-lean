import Pell.DivisorCountPrimePowerBound
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# The divisor count is bounded by every positive real power

The constant is chosen before the integer being counted.  A finite prime
threshold separates the factors whose Bernoulli estimate costs a fixed
coefficient from the remaining factors, whose coefficient is one.  Exact
prime factorization closes the product.  This is an unconditional estimate
for the actual finite set `Nat.divisors`, including the endpoint `n = 1`.

This proof was independently authored from the project's approved Bernoulli
argument; no external project source or mathematical axiom is imported.
-/

namespace PellPaper

open scoped BigOperators

/-- The actual number of positive divisors is at most a constant times any
positive real power; the constant is uniform in every positive integer. -/
theorem exists_pos_card_divisors_le_rpow (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε := by
  classical
  let x : ℝ := (2 : ℝ) ^ ε
  let A : ℝ := x / (x - 1)
  let N : ℕ := ⌈(2 : ℝ) ^ ε⁻¹⌉₊
  have hx : 1 < x := Real.one_lt_rpow (by norm_num) hε
  have hA : 1 ≤ A := (le_div_iff₀ (sub_pos.mpr hx)).mpr (by linarith)
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  refine ⟨A ^ N, pow_pos hApos _, ?_⟩
  intro n hn
  have hn0 : n ≠ 0 := ne_of_gt hn
  have hthreshold (p : ℕ) (hp : N ≤ p) : 2 ≤ (p : ℝ) ^ ε := by
    have hbase : (2 : ℝ) ^ ε⁻¹ ≤ p :=
      (Nat.le_ceil _).trans (by exact_mod_cast hp)
    calc
      (2 : ℝ) = ((2 : ℝ) ^ ε⁻¹) ^ ε :=
        (Real.rpow_inv_rpow (by norm_num) (ne_of_gt hε)).symm
      _ ≤ (p : ℝ) ^ ε := Real.rpow_le_rpow (by positivity) hbase hε.le
  have hfactor (p : ℕ) (hp : p ∈ n.primeFactors) :
      (n.factorization p : ℝ) + 1 ≤
        (if p < N then A else 1) * ((p : ℝ) ^ ε) ^ n.factorization p := by
    split_ifs with hsmall
    · exact nat_succ_le_uniform_rpow_factor hε
        (Nat.prime_of_mem_primeFactors hp).two_le _
    · simpa only [one_mul] using nat_succ_le_rpow_factor_of_two_le
        (hthreshold p (Nat.le_of_not_gt hsmall)) (n.factorization p)
  have hsmallcard : (n.primeFactors.filter (· < N)).card ≤ N := by
    calc
      (n.primeFactors.filter (· < N)).card ≤ (Finset.range N).card := by
        apply Finset.card_le_card
        intro p hp
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
      _ = N := Finset.card_range N
  have hconst : (∏ p ∈ n.primeFactors, if p < N then A else 1) ≤ A ^ N := by
    simp only [Finset.prod_ite, Finset.prod_const, one_pow, mul_one]
    exact pow_le_pow_right₀ hA hsmallcard
  have hprod : (∏ p ∈ n.primeFactors, ((p : ℝ) ^ ε) ^ n.factorization p) =
      (n : ℝ) ^ ε := by
    calc
      (∏ p ∈ n.primeFactors, ((p : ℝ) ^ ε) ^ n.factorization p) =
          ∏ p ∈ n.primeFactors, ((p : ℝ) ^ n.factorization p) ^ ε := by
        apply Finset.prod_congr rfl
        intro p _hp
        rw [← Real.rpow_mul_natCast, ← Real.rpow_natCast_mul]
        · rw [mul_comm]
        all_goals exact Nat.cast_nonneg p
      _ = (∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p) ^ ε :=
        Real.finsetProd_rpow _ _ (fun p _ => pow_nonneg (Nat.cast_nonneg p) _) ε
      _ = (n : ℝ) ^ ε := by
        congr 1
        exact_mod_cast (Nat.prod_primeFactors_pow_factorization hn0).symm
  calc
    (n.divisors.card : ℝ) =
        ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) := by
      rw [Nat.card_divisors hn0]
      push_cast
      rfl
    _ ≤ ∏ p ∈ n.primeFactors,
        ((if p < N then A else 1) * ((p : ℝ) ^ ε) ^ n.factorization p) := by
      apply Finset.prod_le_prod
      · intro p _hp
        positivity
      · exact hfactor
    _ = (∏ p ∈ n.primeFactors, if p < N then A else 1) * (n : ℝ) ^ ε := by
      rw [Finset.prod_mul_distrib, hprod]
    _ ≤ A ^ N * (n : ℝ) ^ ε :=
      mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg (Nat.cast_nonneg n) ε)

end PellPaper
