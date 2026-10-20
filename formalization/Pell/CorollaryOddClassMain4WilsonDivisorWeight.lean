import Pell.CorollaryOddClassMain4WilsonRectangleAdapter

/-!
# Elementary hypotheses for Wilson's reciprocal-divisor weight

This module verifies the algebraic hypotheses in Wilson's Theorem 1.1
for `f(m) = 1 / tau(m)`.  It also reduces the theorem's prime-harmonic
hypothesis with `alpha = 1/2` to the ordinary reciprocal-prime sum.  No
Mertens estimate or large-sieve estimate is asserted here.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

@[simp]
theorem main4WilsonReciprocalDivisorWeight_one :
    main4WilsonReciprocalDivisorWeight 1 = 1 := by
  simp [main4WilsonReciprocalDivisorWeight]

/-- The reciprocal-divisor weight is multiplicative on coprime inputs. -/
theorem main4WilsonReciprocalDivisorWeight_mul_of_coprime
    {m n : ℕ} (hmn : m.Coprime n) :
    main4WilsonReciprocalDivisorWeight (m * n) =
      main4WilsonReciprocalDivisorWeight m *
        main4WilsonReciprocalDivisorWeight n := by
  simp only [main4WilsonReciprocalDivisorWeight,
    hmn.card_divisors_mul, Nat.cast_mul, one_div_mul_one_div]

/-- Exact value of `1 / tau` on a prime power. -/
theorem main4WilsonReciprocalDivisorWeight_prime_pow
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    main4WilsonReciprocalDivisorWeight (p ^ k) =
      1 / ((k + 1 : ℕ) : ℝ) := by
  unfold main4WilsonReciprocalDivisorWeight
  rw [← ArithmeticFunction.sigma_zero_apply,
    ArithmeticFunction.sigma_zero_apply_prime_pow hp]

/-- In particular Wilson's weight has value `1/2` at every prime. -/
theorem main4WilsonReciprocalDivisorWeight_prime
    {p : ℕ} (hp : p.Prime) :
    main4WilsonReciprocalDivisorWeight p = 1 / 2 := by
  simpa using main4WilsonReciprocalDivisorWeight_prime_pow hp 1

/-- Wilson's local prime hypothesis `0 <= f(p) <= 1`. -/
theorem main4WilsonReciprocalDivisorWeight_prime_mem_unitInterval
    {p : ℕ} (hp : p.Prime) :
    0 ≤ main4WilsonReciprocalDivisorWeight p ∧
      main4WilsonReciprocalDivisorWeight p ≤ 1 := by
  rw [main4WilsonReciprocalDivisorWeight_prime hp]
  norm_num

/-- Wilson's prime-power monotonicity hypothesis. -/
theorem main4WilsonReciprocalDivisorWeight_prime_pow_le_prime
    {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) :
    main4WilsonReciprocalDivisorWeight (p ^ k) ≤
      main4WilsonReciprocalDivisorWeight p := by
  rw [main4WilsonReciprocalDivisorWeight_prime_pow hp,
    main4WilsonReciprocalDivisorWeight_prime hp]
  apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
  exact_mod_cast (show 2 ≤ k + 1 by omega)

/-- On any finite prime family, Wilson's prime-harmonic sum for `1/tau`
is exactly one half of the ordinary reciprocal-prime sum. -/
theorem sum_main4WilsonReciprocalDivisorWeight_div_primes_eq_half
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    (∑ p ∈ s,
        main4WilsonReciprocalDivisorWeight p / (p : ℝ)) =
      (1 / 2 : ℝ) * ∑ p ∈ s, 1 / (p : ℝ) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [main4WilsonReciprocalDivisorWeight_prime (hs p hp)]
  ring

end

end PellPaper
