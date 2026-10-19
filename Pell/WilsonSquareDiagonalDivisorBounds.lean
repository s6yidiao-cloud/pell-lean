import Pell.TauThreeBounds

/-!
# Divisor bounds for Wilson's square diagonal

This file isolates an elementary arithmetic estimate used on the square
diagonal in Wilson-type moment arguments.  The number of divisors of `n ^ 2`
is bounded pointwise by the ordered three-divisor function `tauThree n`.
Consequently its summatory function inherits the explicit
`N * (1 + log N) ^ 2` bound proved for `tauThree`.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- At a prime power, the divisor count of the square is at most the ordered
three-divisor count.  The left side is written as its local factor `2*k+1`. -/
private theorem two_mul_add_one_le_tauThree_prime_pow
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    2 * k + 1 ≤ tauThree (p ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [tauThree_apply_prime_pow_succ hp]
      omega

/-- The square-divisor function is pointwise bounded by the ordered
three-divisor function, uniformly including `n = 0`. -/
theorem card_divisors_sq_le_tauThree (n : ℕ) :
    (n ^ 2).divisors.card ≤ tauThree n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hnsq : n ^ 2 ≠ 0 := pow_ne_zero 2 hn
  rw [Nat.card_divisors hnsq, Nat.primeFactors_pow n (by norm_num),
    tauThree_isMultiplicative.multiplicative_factorization tauThree hn]
  apply Finset.prod_le_prod
  · intro p hpMem
    exact Nat.zero_le _
  · intro p hpMem
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpMem
    rw [Nat.factorization_pow]
    simpa [nsmul_eq_mul, Nat.mul_comm] using
      two_mul_add_one_le_tauThree_prime_pow hp (n.factorization p)

/-- Natural-number summatory form of the square-diagonal divisor bound. -/
theorem sum_Ioc_card_divisors_sq_le_sum_tauThree (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, (n ^ 2).divisors.card ≤
      ∑ n ∈ Finset.Ioc 0 N, tauThree n := by
  exact Finset.sum_le_sum fun n _hn ↦ card_divisors_sq_le_tauThree n

/-- Explicit real summatory bound for the divisor count on squares. -/
theorem sum_Ioc_card_divisors_sq_cast_le_mul_one_add_log_sq (N : ℕ) :
    ((∑ n ∈ Finset.Ioc 0 N, (n ^ 2).divisors.card : ℕ) : ℝ) ≤
      (N : ℝ) * (1 + Real.log (N : ℝ)) ^ 2 := by
  calc
    ((∑ n ∈ Finset.Ioc 0 N, (n ^ 2).divisors.card : ℕ) : ℝ) ≤
        ((∑ n ∈ Finset.Ioc 0 N, tauThree n : ℕ) : ℝ) := by
      exact_mod_cast sum_Ioc_card_divisors_sq_le_sum_tauThree N
    _ ≤ (N : ℝ) * (1 + Real.log (N : ℝ)) ^ 2 :=
      sum_Ioc_tauThree_cast_le_mul_one_add_log_sq N

/-- Pointwise-cast version of the explicit square-diagonal summatory bound. -/
theorem sum_Ioc_card_divisors_sq_real_le_mul_one_add_log_sq (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, ((n ^ 2).divisors.card : ℝ) ≤
      (N : ℝ) * (1 + Real.log (N : ℝ)) ^ 2 := by
  rw [← Nat.cast_sum]
  exact sum_Ioc_card_divisors_sq_cast_le_mul_one_add_log_sq N

/-! ## A six-divisor majorant for the weighted square diagonal -/

/-- The ordered four-divisor function, introduced only as an intermediate
stage in the six-divisor majorant. -/
private def tauFour : ArithmeticFunction ℕ :=
  ArithmeticFunction.zeta * tauThree

/-- The ordered five-divisor function. -/
private def tauFive : ArithmeticFunction ℕ :=
  ArithmeticFunction.zeta * tauFour

/-- The ordered six-divisor function. -/
def tauSix : ArithmeticFunction ℕ :=
  ArithmeticFunction.zeta * tauFive

private theorem tauThree_apply_prime_pow_choose {p k : ℕ} (hp : p.Prime) :
    tauThree (p ^ k) = (k + 2).choose 2 := by
  rw [tauThree_apply_prime_pow hp]
  simp [Nat.choose_two_right, Nat.mul_comm]

private theorem tauFour_apply_prime_pow {p k : ℕ} (hp : p.Prime) :
    tauFour (p ^ k) = (k + 3).choose 3 := by
  rw [tauFour, ArithmeticFunction.zeta_mul_apply,
    Nat.sum_divisors_prime_pow hp]
  simp_rw [tauThree_apply_prime_pow_choose hp]
  simpa [Nat.add_assoc] using Nat.sum_range_add_choose k 2

private theorem tauFive_apply_prime_pow {p k : ℕ} (hp : p.Prime) :
    tauFive (p ^ k) = (k + 4).choose 4 := by
  rw [tauFive, ArithmeticFunction.zeta_mul_apply,
    Nat.sum_divisors_prime_pow hp]
  simp_rw [tauFour_apply_prime_pow hp]
  simpa [Nat.add_assoc] using Nat.sum_range_add_choose k 3

private theorem tauSix_apply_prime_pow {p k : ℕ} (hp : p.Prime) :
    tauSix (p ^ k) = (k + 5).choose 5 := by
  rw [tauSix, ArithmeticFunction.zeta_mul_apply,
    Nat.sum_divisors_prime_pow hp]
  simp_rw [tauFive_apply_prime_pow hp]
  simpa [Nat.add_assoc] using Nat.sum_range_add_choose k 4

private theorem four_mul_add_five_le_choose_add_five_four (k : ℕ) :
    4 * k + 5 ≤ (k + 5).choose 4 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      have hfour : 4 ≤ (k + 5).choose 3 := by
        have hmono := Nat.choose_le_choose 3 (show 4 ≤ k + 5 by omega)
        norm_num at hmono ⊢
        exact hmono
      rw [show k + 1 + 5 = (k + 5) + 1 by omega,
        Nat.choose_succ_succ]
      norm_num at *
      omega

private theorem square_times_divisor_local_le_choose_add_five (k : ℕ) :
    (2 * k + 1) * (k + 1) ≤ (k + 5).choose 5 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      have hstep := four_mul_add_five_le_choose_add_five_four k
      rw [show k + 1 + 5 = (k + 5) + 1 by omega,
        Nat.choose_succ_succ]
      norm_num at *
      nlinarith

/-- The ordered six-divisor function is multiplicative. -/
theorem tauSix_isMultiplicative : tauSix.IsMultiplicative := by
  unfold tauSix tauFive tauFour
  exact ArithmeticFunction.isMultiplicative_zeta.mul
    (ArithmeticFunction.isMultiplicative_zeta.mul
      (ArithmeticFunction.isMultiplicative_zeta.mul tauThree_isMultiplicative))

/-- The product `tau(n^2) * tau(n)` is bounded pointwise by the ordered
six-divisor function.  This is the weighted square-diagonal majorant. -/
theorem card_divisors_sq_mul_card_divisors_le_tauSix (n : ℕ) :
    (n ^ 2).divisors.card * n.divisors.card ≤ tauSix n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [tauSix, tauFive, tauFour]
  have hnsq : n ^ 2 ≠ 0 := pow_ne_zero 2 hn
  rw [Nat.card_divisors hnsq, Nat.primeFactors_pow n (by norm_num),
    Nat.card_divisors hn,
    tauSix_isMultiplicative.multiplicative_factorization tauSix hn,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod
  · intro p hpMem
    exact Nat.zero_le _
  · intro p hpMem
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpMem
    rw [Nat.factorization_pow]
    simpa [nsmul_eq_mul, Nat.mul_comm, tauSix_apply_prime_pow hp] using
      square_times_divisor_local_le_choose_add_five (n.factorization p)

/-- One elementary Dirichlet-hyperbola step: convolving a nonnegative
arithmetic function with `zeta` raises an explicit logarithmic summatory
bound by one power. -/
private theorem sum_Ioc_zeta_mul_cast_le_one_more_log
    (f : ArithmeticFunction ℕ) (k M : ℕ)
    (hf : ∀ Y : ℕ,
      ((∑ n ∈ Finset.Ioc 0 Y, f n : ℕ) : ℝ) ≤
        (Y : ℝ) * (1 + Real.log (Y : ℝ)) ^ k) :
    ((∑ n ∈ Finset.Ioc 0 M,
        (ArithmeticFunction.zeta * f) n : ℕ) : ℝ) ≤
      (M : ℝ) * (1 + Real.log (M : ℝ)) ^ (k + 1) := by
  rcases eq_or_ne M 0 with rfl | hM
  · simp
  have hMpos : 0 < M := Nat.pos_of_ne_zero hM
  have hsum :
      ∑ n ∈ Finset.Ioc 0 M, (ArithmeticFunction.zeta * f) n =
        ∑ n ∈ Finset.Ioc 0 M,
          ∑ m ∈ Finset.Ioc 0 (M / n), f m := by
    rw [ArithmeticFunction.sum_Ioc_mul_eq_sum_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : n ≠ 0 := ne_of_gt (Finset.mem_Ioc.mp hn).1
    rw [ArithmeticFunction.zeta_apply_ne hn0, one_mul]
  rw [hsum, Nat.cast_sum]
  calc
    ∑ n ∈ Finset.Ioc 0 M,
        (((∑ m ∈ Finset.Ioc 0 (M / n), f m : ℕ) : ℝ)) ≤
        ∑ n ∈ Finset.Ioc 0 M,
          ((M : ℝ) / (n : ℝ)) *
            (1 + Real.log (M : ℝ)) ^ k := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨hnpos, hnM⟩ := Finset.mem_Ioc.mp hn
      have hMnpos : 0 < M / n := Nat.div_pos hnM hnpos
      have hMnle : M / n ≤ M := Nat.div_le_self M n
      have hlogMnM : Real.log ((M / n : ℕ) : ℝ) ≤
          Real.log (M : ℝ) := by
        exact Real.log_le_log (by positivity) (by exact_mod_cast hMnle)
      have hbaseMn : 0 ≤ 1 + Real.log ((M / n : ℕ) : ℝ) := by
        have hMnone : (1 : ℝ) ≤ ((M / n : ℕ) : ℝ) := by
          exact_mod_cast hMnpos
        positivity
      have hbaseM : 0 ≤ 1 + Real.log (M : ℝ) := by
        have hMone : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hMpos
        positivity
      have hpow :
          (1 + Real.log ((M / n : ℕ) : ℝ)) ^ k ≤
            (1 + Real.log (M : ℝ)) ^ k :=
        pow_le_pow_left₀ hbaseMn (add_le_add le_rfl hlogMnM) k
      calc
        (((∑ m ∈ Finset.Ioc 0 (M / n), f m : ℕ) : ℝ)) ≤
            ((M / n : ℕ) : ℝ) *
              (1 + Real.log ((M / n : ℕ) : ℝ)) ^ k := hf (M / n)
        _ ≤ ((M / n : ℕ) : ℝ) *
              (1 + Real.log (M : ℝ)) ^ k :=
          mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)
        _ ≤ ((M : ℝ) / (n : ℝ)) *
              (1 + Real.log (M : ℝ)) ^ k :=
          mul_le_mul_of_nonneg_right Nat.cast_div_le (pow_nonneg hbaseM k)
    _ = (M : ℝ) * (1 + Real.log (M : ℝ)) ^ k *
        (harmonic M : ℝ) := by
      have hfin : Finset.Ioc 0 M = Finset.Icc 1 M := by
        ext n
        simp only [Finset.mem_Ioc, Finset.mem_Icc]
        omega
      rw [hfin, harmonic_eq_sum_Icc]
      simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
        Finset.mul_sum, div_eq_mul_inv]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ ≤ (M : ℝ) * (1 + Real.log (M : ℝ)) ^ k *
        (1 + Real.log (M : ℝ)) := by
      have hbaseM : 0 ≤ 1 + Real.log (M : ℝ) := by
        have hMone : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hMpos
        positivity
      exact mul_le_mul_of_nonneg_left (harmonic_le_one_add_log M)
        (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hbaseM k))
    _ = (M : ℝ) * (1 + Real.log (M : ℝ)) ^ (k + 1) := by
      rw [pow_succ]
      ring

private theorem sum_Ioc_tauFour_cast_le_mul_one_add_log_cube (M : ℕ) :
    ((∑ n ∈ Finset.Ioc 0 M, tauFour n : ℕ) : ℝ) ≤
      (M : ℝ) * (1 + Real.log (M : ℝ)) ^ 3 := by
  simpa [tauFour] using
    sum_Ioc_zeta_mul_cast_le_one_more_log tauThree 2 M
      sum_Ioc_tauThree_cast_le_mul_one_add_log_sq

private theorem sum_Ioc_tauFive_cast_le_mul_one_add_log_fourth (M : ℕ) :
    ((∑ n ∈ Finset.Ioc 0 M, tauFive n : ℕ) : ℝ) ≤
      (M : ℝ) * (1 + Real.log (M : ℝ)) ^ 4 := by
  simpa [tauFive] using
    sum_Ioc_zeta_mul_cast_le_one_more_log tauFour 3 M
      sum_Ioc_tauFour_cast_le_mul_one_add_log_cube

/-- The ordered six-divisor function has the explicit elementary summatory
bound `M * (1 + log M)^5`. -/
theorem sum_Ioc_tauSix_cast_le_mul_one_add_log_fifth (M : ℕ) :
    ((∑ n ∈ Finset.Ioc 0 M, tauSix n : ℕ) : ℝ) ≤
      (M : ℝ) * (1 + Real.log (M : ℝ)) ^ 5 := by
  simpa [tauSix] using
    sum_Ioc_zeta_mul_cast_le_one_more_log tauFive 4 M
      sum_Ioc_tauFive_cast_le_mul_one_add_log_fourth

/-- Explicit weighted square-diagonal estimate of order
`N * (1 + log N)^5`. -/
theorem sum_Ioc_card_divisors_sq_mul_card_divisors_cast_le (N : ℕ) :
    ((∑ n ∈ Finset.Ioc 0 N,
        (n ^ 2).divisors.card * n.divisors.card : ℕ) : ℝ) ≤
      (N : ℝ) * (1 + Real.log (N : ℝ)) ^ 5 := by
  calc
    ((∑ n ∈ Finset.Ioc 0 N,
        (n ^ 2).divisors.card * n.divisors.card : ℕ) : ℝ) ≤
        ((∑ n ∈ Finset.Ioc 0 N, tauSix n : ℕ) : ℝ) := by
      exact_mod_cast Finset.sum_le_sum
        (fun n _hn ↦ card_divisors_sq_mul_card_divisors_le_tauSix n)
    _ ≤ (N : ℝ) * (1 + Real.log (N : ℝ)) ^ 5 :=
      sum_Ioc_tauSix_cast_le_mul_one_add_log_fifth N

/-- Pointwise-cast form of the weighted square-diagonal estimate. -/
theorem sum_Ioc_card_divisors_sq_mul_card_divisors_real_le (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N,
        ((n ^ 2).divisors.card : ℝ) * (n.divisors.card : ℝ) ≤
      (N : ℝ) * (1 + Real.log (N : ℝ)) ^ 5 := by
  simpa only [Nat.cast_sum, Nat.cast_mul] using
    sum_Ioc_card_divisors_sq_mul_card_divisors_cast_le N

end

end PellPaper
