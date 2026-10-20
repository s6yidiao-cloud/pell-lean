import Pell.TauThreeFactorFibre
import Pell.DivisorCountSubpower
import Pell.DivisorSummatoryLogBound
import Mathlib.Data.Nat.Choose.Sum

/-!
# Elementary bounds for the ordered three-divisor function

This file develops unconditional arithmetic facts about the function
`tauThree = zeta * sigma 0` used in the Friedlander--Iwaniec cubic grouping.
In particular, it records multiplicativity and the exact local factor at a
prime power.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- The ordered three-divisor function is multiplicative. -/
theorem tauThree_isMultiplicative : tauThree.IsMultiplicative := by
  unfold tauThree
  exact ArithmeticFunction.isMultiplicative_zeta.mul
    ArithmeticFunction.isMultiplicative_sigma

/-- Exact local factor of the ordered three-divisor function. -/
theorem tauThree_apply_prime_pow {p k : ℕ} (hp : p.Prime) :
    tauThree (p ^ k) = (k + 1) * (k + 2) / 2 := by
  rw [tauThree, ArithmeticFunction.zeta_mul_apply,
    Nat.sum_divisors_prime_pow hp]
  simp_rw [ArithmeticFunction.sigma_zero_apply_prime_pow hp]
  simpa [Nat.choose_two_right, Nat.mul_comm] using
    (Nat.sum_range_add_choose k 1)

/-- Successive local factors differ by the next linear term. -/
theorem tauThree_apply_prime_pow_succ {p : ℕ} (hp : p.Prime) (k : ℕ) :
    tauThree (p ^ (k + 1)) = tauThree (p ^ k) + (k + 2) := by
  rw [tauThree_apply_prime_pow hp, tauThree_apply_prime_pow hp]
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm] using
    (Nat.triangle_succ (k + 2))

/-- The local factor contains at least the `k + 1` elementary placements. -/
theorem add_one_le_tauThree_apply_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    k + 1 ≤ tauThree (p ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show k + 1 + 1 = (k + 1) + 1 by omega,
        tauThree_apply_prime_pow_succ hp]
      omega

/-- Local submultiplicativity at powers of one prime. -/
theorem tauThree_apply_prime_pow_add_le_mul {p : ℕ} (hp : p.Prime)
    (a b : ℕ) :
    tauThree (p ^ (a + b)) ≤
      tauThree (p ^ a) * tauThree (p ^ b) := by
  induction b with
  | zero => simp
  | succ b ih =>
      have hlinear : a + b + 2 ≤ tauThree (p ^ a) * (b + 2) := by
        have hab : a + b + 2 ≤ (a + 1) * (b + 2) := by
          nlinarith
        exact hab.trans (Nat.mul_le_mul_right (b + 2)
          (add_one_le_tauThree_apply_prime_pow hp a))
      rw [show a + (b + 1) = (a + b) + 1 by omega,
        tauThree_apply_prime_pow_succ hp,
        tauThree_apply_prime_pow_succ hp]
      calc
        tauThree (p ^ (a + b)) + (a + b + 2) ≤
            tauThree (p ^ a) * tauThree (p ^ b) +
              tauThree (p ^ a) * (b + 2) := Nat.add_le_add ih hlinear
        _ = tauThree (p ^ a) * (tauThree (p ^ b) + (b + 2)) := by ring

/-- The ordered three-divisor function is submultiplicative without a
coprimality hypothesis.  This is the factorization step that turns the
three-variable `tauThree (m₁*m₂*m₃)` sum in Friedlander--Iwaniec into
three one-variable sums. -/
theorem tauThree_mul_le (m n : ℕ) :
    tauThree (m * n) ≤ tauThree m * tauThree n := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hmn : m * n ≠ 0 := mul_ne_zero hm hn
  have hpowZero : ∀ {p : ℕ}, tauThree (p ^ 0) = 1 := by
    intro p
    simp
  iterate 3 rw [tauThree_isMultiplicative.multiplicative_factorization tauThree
      (by assumption),
    Finsupp.prod_of_support_subset _ _ _ (fun _ _ ↦ hpowZero)
      (s := m.primeFactors ∪ n.primeFactors)]
  · rw [← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod
    · intro p hp
      exact Nat.zero_le _
    · intro p hp
      have hpprime : p.Prime := by
        rcases Finset.mem_union.mp hp with hpm | hpn
        · exact Nat.prime_of_mem_primeFactors hpm
        · exact Nat.prime_of_mem_primeFactors hpn
      rw [Nat.factorization_mul hm hn, Finsupp.add_apply]
      exact tauThree_apply_prime_pow_add_le_mul hpprime _ _
  · exact Finset.subset_union_right
  · exact Finset.subset_union_left
  · simp [Nat.primeFactors_mul hm hn]

/-- Three-factor form of `tauThree_mul_le`, matching the cubic expansion in
the Friedlander--Iwaniec proof. -/
theorem tauThree_mul_mul_le (a b c : ℕ) :
    tauThree (a * b * c) ≤ tauThree a * tauThree b * tauThree c := by
  exact (tauThree_mul_le (a * b) c).trans
    (Nat.mul_le_mul_right (tauThree c) (tauThree_mul_le a b))

/-- A pointwise comparison with the square of the ordinary divisor count.
This is uniform at zero as well as at positive integers. -/
theorem tauThree_le_card_divisors_sq (n : ℕ) :
    tauThree n ≤ n.divisors.card ^ 2 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [tauThree, ArithmeticFunction.zeta_mul_apply]
  simp_rw [ArithmeticFunction.sigma_zero_apply]
  calc
    ∑ d ∈ n.divisors, d.divisors.card ≤
        ∑ _d ∈ n.divisors, n.divisors.card := by
      apply Finset.sum_le_sum
      intro d hd
      exact Finset.card_le_card
        (Nat.divisors_subset_of_dvd hn (Nat.dvd_of_mem_divisors hd))
    _ = n.divisors.card ^ 2 := by
      simp [pow_two]

/-- The summatory ordered three-divisor function has the elementary
Dirichlet-hyperbola bound `M * (1 + log M)^2`, uniformly including `M = 0`.
This is the one-variable logarithmic input in Section 9 of
Friedlander--Iwaniec. -/
theorem sum_Ioc_tauThree_cast_le_mul_one_add_log_sq (M : ℕ) :
    ((∑ n ∈ Finset.Ioc 0 M, tauThree n : ℕ) : ℝ) ≤
      (M : ℝ) * (1 + Real.log (M : ℝ)) ^ 2 := by
  rcases eq_or_ne M 0 with rfl | hM
  · simp
  have hMpos : 0 < M := Nat.pos_of_ne_zero hM
  have hsum :
      ∑ n ∈ Finset.Ioc 0 M, tauThree n =
        ∑ n ∈ Finset.Ioc 0 M,
          ∑ d ∈ Finset.Ioc 0 (M / n), d.divisors.card := by
    rw [tauThree, ArithmeticFunction.sum_Ioc_mul_eq_sum_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : n ≠ 0 := ne_of_gt (Finset.mem_Ioc.mp hn).1
    rw [ArithmeticFunction.zeta_apply_ne hn0, one_mul]
    simp_rw [ArithmeticFunction.sigma_zero_apply]
  rw [hsum, Nat.cast_sum]
  calc
    ∑ n ∈ Finset.Ioc 0 M,
        (((∑ d ∈ Finset.Ioc 0 (M / n), d.divisors.card : ℕ) : ℝ)) ≤
        ∑ n ∈ Finset.Ioc 0 M,
          ((M : ℝ) / (n : ℝ)) * (1 + Real.log (M : ℝ)) := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨hnpos, hnM⟩ := Finset.mem_Ioc.mp hn
      have hMnpos : 0 < M / n := Nat.div_pos hnM hnpos
      have hMnle : M / n ≤ M := Nat.div_le_self M n
      have hlogMnM : Real.log ((M / n : ℕ) : ℝ) ≤
          Real.log (M : ℝ) := by
        exact Real.log_le_log (by positivity) (by exact_mod_cast hMnle)
      have hlogMnonneg : 0 ≤ 1 + Real.log (M : ℝ) := by
        have hMone : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hMpos
        positivity
      calc
        (((∑ d ∈ Finset.Ioc 0 (M / n), d.divisors.card : ℕ) : ℝ)) ≤
            ((M / n : ℕ) : ℝ) *
              (1 + Real.log ((M / n : ℕ) : ℝ)) :=
          sum_Ioc_card_divisors_cast_le_mul_one_add_log (M / n)
        _ ≤ ((M / n : ℕ) : ℝ) * (1 + Real.log (M : ℝ)) :=
          mul_le_mul_of_nonneg_left (add_le_add le_rfl hlogMnM)
            (Nat.cast_nonneg _)
        _ ≤ ((M : ℝ) / (n : ℝ)) * (1 + Real.log (M : ℝ)) :=
          mul_le_mul_of_nonneg_right Nat.cast_div_le hlogMnonneg
    _ = (M : ℝ) * (1 + Real.log (M : ℝ)) * (harmonic M : ℝ) := by
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
    _ ≤ (M : ℝ) * (1 + Real.log (M : ℝ)) ^ 2 := by
      have hlogMnonneg : 0 ≤ 1 + Real.log (M : ℝ) := by
        have hMone : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hMpos
        positivity
      calc
        (M : ℝ) * (1 + Real.log (M : ℝ)) * (harmonic M : ℝ) ≤
            (M : ℝ) * (1 + Real.log (M : ℝ)) *
              (1 + Real.log (M : ℝ)) :=
          mul_le_mul_of_nonneg_left (harmonic_le_one_add_log M)
            (mul_nonneg (Nat.cast_nonneg _) hlogMnonneg)
        _ = (M : ℝ) * (1 + Real.log (M : ℝ)) ^ 2 := by ring

/-- Consequently `tauThree` is bounded by every positive real power, with
the constant chosen before the positive integer. -/
theorem exists_pos_tauThree_le_rpow (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      (tauThree n : ℝ) ≤ C * (n : ℝ) ^ ε := by
  obtain ⟨C, hC, hdiv⟩ :=
    exists_pos_card_divisors_le_rpow (ε / 2) (by positivity)
  refine ⟨C ^ 2, pow_pos hC 2, ?_⟩
  intro n hn
  have htau : (tauThree n : ℝ) ≤ (n.divisors.card : ℝ) ^ 2 := by
    exact_mod_cast tauThree_le_card_divisors_sq n
  calc
    (tauThree n : ℝ) ≤ (n.divisors.card : ℝ) ^ 2 := htau
    _ ≤ (C * (n : ℝ) ^ (ε / 2)) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (hdiv n hn) 2
    _ = C ^ 2 * (n : ℝ) ^ ε := by
      rw [mul_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg n)]
      ring_nf

end

end PellPaper
