import Pell.CorollaryOddClassMain4WilsonDivisorWeight
import Pell.DivisorCardinalityMonotonicity
import Mathlib.Data.Finset.NatDivisors
import Mathlib.NumberTheory.SelbergSieve

/-!
# Wilson's reciprocal-divisor neutralizer

This module formalizes the finite, non-analytic specialization of Lemma 2.1
in Cameron Wilson, *An improved large sieve for quadratic characters via
Hooley neutralisers and its applications*, at the weight `f(n) = 1 / tau(n)`.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- Wilson's `\hat f(d) = \prod_{p \mid d} (1 - f(p))`, specialized to
`f(n) = 1 / tau(n)`.  Only positive `d` occur in divisor sums. -/
def main4WilsonReciprocalDivisorComplementWeight (d : ℕ) : ℝ :=
  ∏ p ∈ d.primeFactors,
    (1 - main4WilsonReciprocalDivisorWeight p)

/-- For `f(n) = 1 / tau(n)`, Wilson's complementary weight agrees with
`f` on squarefree integers: both have local value `1/2`. -/
theorem main4WilsonReciprocalDivisorComplementWeight_eq_of_squarefree
    {d : ℕ} (hd : Squarefree d) :
    main4WilsonReciprocalDivisorComplementWeight d =
      main4WilsonReciprocalDivisorWeight d := by
  unfold main4WilsonReciprocalDivisorComplementWeight
  have hfactor : ∀ p ∈ d.primeFactors, d.factorization p + 1 = 2 := by
    intro p hp
    rw [Nat.factorization_eq_one_of_squarefree hd
      (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp)]
  calc
    (∏ p ∈ d.primeFactors,
        (1 - main4WilsonReciprocalDivisorWeight p)) =
        ∏ _p ∈ d.primeFactors, (1 / 2 : ℝ) := by
          apply Finset.prod_congr rfl
          intro p hp
          rw [main4WilsonReciprocalDivisorWeight_prime
            (Nat.prime_of_mem_primeFactors hp)]
          norm_num
    _ = main4WilsonReciprocalDivisorWeight d := by
      unfold main4WilsonReciprocalDivisorWeight
      rw [Nat.card_divisors hd.ne_zero]
      have hprod :
          (∏ p ∈ d.primeFactors, (d.factorization p + 1)) =
            ∏ _p ∈ d.primeFactors, 2 := by
        apply Finset.prod_congr rfl
        exact hfactor
      rw [hprod]
      simp [one_div, Nat.cast_pow]

private theorem sum_divisors_prime_mul
    (lambdaPlus : ℕ → ℝ) {p q : ℕ}
    (hp : p.Prime) (hpq : p.Coprime q) :
    (∑ d ∈ (p * q).divisors, lambdaPlus d) =
      (∑ d ∈ q.divisors, lambdaPlus d) +
        ∑ d ∈ q.divisors, lambdaPlus (p * d) := by
  calc
    _ = ∑ x ∈ (p.divisors ×ˢ q.divisors).attach,
          lambdaPlus (x.1.1 * x.1.2) := by
        rw [hpq.divisors_mul, Finset.sum_map]
        apply Finset.sum_congr rfl
        intro x _hx
        rfl
    _ = ∑ x ∈ p.divisors ×ˢ q.divisors,
          lambdaPlus (x.1 * x.2) :=
        Finset.sum_attach (p.divisors ×ˢ q.divisors)
          (fun x ↦ lambdaPlus (x.1 * x.2))
    _ = _ := by
      rw [Finset.sum_product, hp.sum_divisors]
      simp [add_comm]

/-- The reciprocal-divisor weight on a finite product of distinct primes is
majorized by any upper-Moebius neutralizer on that divisor lattice. -/
private theorem reciprocalDivisorWeight_prod_primes_le_neutralizer
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (lambdaPlus : ℕ → ℝ)
    (hUpper : ∀ r : ℕ, r ∣ ∏ p ∈ s, p →
      (if r = 1 then 1 else 0) ≤
        ∑ d ∈ r.divisors, lambdaPlus d) :
    main4WilsonReciprocalDivisorWeight (∏ p ∈ s, p) ≤
      ∑ d ∈ (∏ p ∈ s, p).divisors,
        lambdaPlus d * main4WilsonReciprocalDivisorWeight d := by
  classical
  induction s using Finset.induction_on generalizing lambdaPlus with
  | empty =>
      simpa using hUpper 1 (by simp)
  | @insert p s hpnot ih =>
      have hp : p.Prime := hs p (Finset.mem_insert_self p s)
      have hs' : ∀ q ∈ s, q.Prime := by
        intro q hq
        exact hs q (Finset.mem_insert_of_mem hq)
      let q := ∏ r ∈ s, r
      have hpq : p.Coprime q := by
        rw [hp.coprime_iff_not_dvd]
        apply hp.prime.not_dvd_finsetProd
        intro r hr hpr
        have hprEq : p = r :=
          (Nat.prime_dvd_prime_iff_eq hp (hs' r hr)).mp hpr
        exact hpnot (hprEq ▸ hr)
      let lambdaNext : ℕ → ℝ := fun d ↦
        2 * lambdaPlus d + lambdaPlus (p * d)
      have hUpperNext : ∀ r : ℕ, r ∣ q →
          (if r = 1 then 1 else 0) ≤
            ∑ d ∈ r.divisors, lambdaNext d := by
        intro r hr
        have hpr : p * r ∣ p * q := Nat.mul_dvd_mul_left p hr
        have hcopr : p.Coprime r := hpq.coprime_dvd_right hr
        have hrBig : r ∣ p * q :=
          hr.trans ⟨p, by simp [Nat.mul_comm]⟩
        have hrBound := hUpper r (by
          simpa [Finset.prod_insert hpnot, q] using hrBig)
        have hprBound := hUpper (p * r) (by
          simpa [Finset.prod_insert hpnot, q] using hpr)
        have hsplit := sum_divisors_prime_mul lambdaPlus hp hcopr
        have hsum :
            (∑ d ∈ r.divisors, lambdaNext d) =
              (∑ d ∈ r.divisors, lambdaPlus d) +
                ∑ d ∈ (p * r).divisors, lambdaPlus d := by
          rw [hsplit]
          simp only [lambdaNext, Finset.sum_add_distrib]
          rw [← Finset.mul_sum]
          ring
        rw [hsum]
        by_cases hrOne : r = 1
        · subst r
          simp only [if_pos] at hrBound ⊢
          have hprNonneg :
              (0 : ℝ) ≤ ∑ d ∈ (p * 1).divisors, lambdaPlus d := by
            simpa [hp.ne_one] using hprBound
          linarith
        · simp only [if_neg hrOne] at hrBound ⊢
          have hprOne : p * r ≠ 1 := by
            intro h
            exact hp.ne_one (Nat.eq_one_of_dvd_one ⟨r, h.symm⟩)
          have hprNonneg :
              (0 : ℝ) ≤ ∑ d ∈ (p * r).divisors, lambdaPlus d := by
            simpa [hprOne] using hprBound
          linarith
      have hInduction := ih hs' lambdaNext hUpperNext
      have hprimeWeight :
          main4WilsonReciprocalDivisorWeight p = (1 / 2 : ℝ) :=
        main4WilsonReciprocalDivisorWeight_prime hp
      have hleft :
          main4WilsonReciprocalDivisorWeight (p * q) =
            (1 / 2 : ℝ) * main4WilsonReciprocalDivisorWeight q := by
        rw [main4WilsonReciprocalDivisorWeight_mul_of_coprime hpq,
          hprimeWeight]
      have hright :
          (∑ d ∈ (p * q).divisors,
              lambdaPlus d * main4WilsonReciprocalDivisorWeight d) =
            (1 / 2 : ℝ) *
              ∑ d ∈ q.divisors,
                lambdaNext d * main4WilsonReciprocalDivisorWeight d := by
        rw [sum_divisors_prime_mul
          (fun d ↦ lambdaPlus d * main4WilsonReciprocalDivisorWeight d)
          hp hpq]
        rw [Finset.mul_sum]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro d hd
        have hpd : p.Coprime d :=
          hpq.coprime_dvd_right (Nat.dvd_of_mem_divisors hd)
        rw [main4WilsonReciprocalDivisorWeight_mul_of_coprime hpd,
          hprimeWeight]
        simp only [lambdaNext]
        ring
      rw [Finset.prod_insert hpnot, hleft, hright]
      exact mul_le_mul_of_nonneg_left hInduction (by norm_num)

/-- Wilson's Lemma 2.1 on a squarefree integer, specialized to
`f(n) = 1 / tau(n)`.  This is the finite heart of the neutralizer argument;
it uses no size, support, or analytic estimate for `lambdaPlus`. -/
theorem main4WilsonReciprocalDivisorWeight_le_neutralizer_of_squarefree
    {q : ℕ} (hq : Squarefree q) (lambdaPlus : ℕ → ℝ)
    (hUpper : BoundingSieve.IsUpperMoebius lambdaPlus) :
    main4WilsonReciprocalDivisorWeight q ≤
      ∑ d ∈ q.divisors,
        lambdaPlus d * main4WilsonReciprocalDivisorComplementWeight d := by
  have hprime : ∀ p ∈ q.primeFactors, p.Prime := by
    intro p hp
    exact Nat.prime_of_mem_primeFactors hp
  have hcore := reciprocalDivisorWeight_prod_primes_le_neutralizer
    q.primeFactors hprime lambdaPlus (fun r _hr ↦ hUpper r)
  rw [Nat.prod_primeFactors_of_squarefree hq] at hcore
  calc
    main4WilsonReciprocalDivisorWeight q ≤
        ∑ d ∈ q.divisors,
          lambdaPlus d * main4WilsonReciprocalDivisorWeight d := hcore
    _ = ∑ d ∈ q.divisors,
          lambdaPlus d *
            main4WilsonReciprocalDivisorComplementWeight d := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [main4WilsonReciprocalDivisorComplementWeight_eq_of_squarefree
        (hq.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd))]

/-- Source-faithful reciprocal-divisor specialization of Wilson's Lemma 2.1.

The squarefree number `P` represents the finite product of the sieve primes
(Wilson takes the odd primes at most `z`).  The divisors of `gcd n P` are
exactly the integers satisfying `d | n` and `d | P`.  Oddness of `P` is not
used by this finite inequality. -/
theorem main4WilsonReciprocalDivisorWeight_le_neutralizer_gcd
    (P n : ℕ) (hP : Squarefree P) (hn : n ≠ 0)
    (lambdaPlus : ℕ → ℝ)
    (hUpper : BoundingSieve.IsUpperMoebius lambdaPlus) :
    main4WilsonReciprocalDivisorWeight n ≤
      ∑ d ∈ (Nat.gcd n P).divisors,
        lambdaPlus d * main4WilsonReciprocalDivisorComplementWeight d := by
  let q := Nat.gcd n P
  have hqNe : q ≠ 0 := Nat.gcd_ne_zero_left hn
  have hqSquarefree : Squarefree q :=
    hP.squarefree_of_dvd (Nat.gcd_dvd_right n P)
  have hcard : q.divisors.card ≤ n.divisors.card :=
    card_divisors_le_card_divisors_of_dvd hn (Nat.gcd_dvd_left n P)
  have hqCardPos : 0 < q.divisors.card :=
    Finset.card_pos.mpr ⟨1, by simp [hqNe]⟩
  have hweight :
      main4WilsonReciprocalDivisorWeight n ≤
        main4WilsonReciprocalDivisorWeight q := by
    unfold main4WilsonReciprocalDivisorWeight
    apply one_div_le_one_div_of_le
    · exact_mod_cast hqCardPos
    · exact_mod_cast hcard
  exact hweight.trans
    (main4WilsonReciprocalDivisorWeight_le_neutralizer_of_squarefree
      hqSquarefree lambdaPlus hUpper)

/-- Wilson's Lemma 2.1 in the paper's literal `d | n`, `d | P` indexing. -/
theorem main4WilsonReciprocalDivisorWeight_le_neutralizer
    (P n : ℕ) (hP : Squarefree P) (hn : n ≠ 0)
    (lambdaPlus : ℕ → ℝ)
    (hUpper : BoundingSieve.IsUpperMoebius lambdaPlus) :
    main4WilsonReciprocalDivisorWeight n ≤
      ∑ d ∈ n.divisors.filter (fun d ↦ d ∣ P),
        lambdaPlus d * main4WilsonReciprocalDivisorComplementWeight d := by
  have hdivisors :
      (Nat.gcd n P).divisors =
        n.divisors.filter (fun d ↦ d ∣ P) := by
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter]
    constructor
    · rintro ⟨hd, _hgcdNe⟩
      exact ⟨⟨(Nat.dvd_gcd_iff.mp hd).1, hn⟩,
        (Nat.dvd_gcd_iff.mp hd).2⟩
    · rintro ⟨⟨hdn, _hn⟩, hdP⟩
      exact ⟨Nat.dvd_gcd hdn hdP, Nat.gcd_ne_zero_left hn⟩
  rw [← hdivisors]
  exact main4WilsonReciprocalDivisorWeight_le_neutralizer_gcd
    P n hP hn lambdaPlus hUpper

end

end PellPaper
