import Pell.QuadraticIdealNormLocalUniquePrime
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Prime-power ideal norms with two split primes

Suppose two distinct ideals `P` and `Q` have norm `p`, where `p` is prime,
and exhaust the maximal ideals over `p`.  Every ideal of norm `p^k` then has
the unique shape `P^j * Q^(k-j)`, for `j ≤ k`.  This gives an equivalence
with `Fin (k+1)` and the actual norm-fibre cardinality `k+1`, including `k=0`.

Norm `p` already forces each displayed ideal to be nonzero and maximal.
The local norm, distinctness and exhaustiveness hypotheses remain explicit;
the geometric-sum corollary also retains the character value `χ(p)=1`.
No concrete quadratic splitting or character identification is asserted.
-/

namespace PellPaper

open NumberField

noncomputable section

private theorem isMaximal_of_absNorm_eq_prime
    (K : Type*) [Field K] [NumberField K] (p : ℕ) (hp : Nat.Prime p)
    (P : Ideal (𝓞 K)) (hPnorm : Ideal.absNorm P = p) : P.IsMaximal := by
  have hPprime : P.IsPrime := Ideal.isPrime_of_irreducible_absNorm
    ((Nat.irreducible_iff_nat_prime _).mpr (hPnorm ▸ hp))
  apply hPprime.isMaximal
  intro hP
  have hzero : Ideal.absNorm P = 0 := Ideal.absNorm_eq_zero_iff.mpr hP
  exact hp.ne_zero (hPnorm.symm.trans hzero)

/-- Removing a maximal prime divisor proves the full two-prime power
classification, without an assumed ideal factorization or counting formula. -/
theorem ideal_eq_primePow_mul_primePow_of_absNorm_eq_primePow_of_twoPrimesOver
    (K : Type*) [Field K] [NumberField K] (p k : ℕ) (hp : Nat.Prime p)
    (P Q : Ideal (𝓞 K)) (hPnorm : Ideal.absNorm P = p) (hQnorm : Ideal.absNorm Q = p)
    (hexhaust : ∀ R : Ideal (𝓞 K), R.IsMaximal →
      R.under ℤ = Ideal.span ({(p : ℤ)} : Set ℤ) → R = P ∨ R = Q)
    {I : Ideal (𝓞 K)} (hI : Ideal.absNorm I = p ^ k) :
    ∃ j : ℕ, j ≤ k ∧ I = P ^ j * Q ^ (k - j) := by
  induction k generalizing I with
  | zero =>
      refine ⟨0, le_rfl, ?_⟩
      simpa using Ideal.absNorm_eq_one_iff.mp (by simpa using hI)
  | succ k ih =>
      have hp_dvd : p ∣ Ideal.absNorm I := by
        rw [hI]
        exact dvd_pow_self _ (Nat.succ_ne_zero _)
      obtain ⟨R, hRmax, hRunder, hRdvd⟩ :=
        Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp I hp_dvd
      obtain ⟨J, hIJ⟩ := hRdvd
      have hRPQ : R = P ∨ R = Q := hexhaust R hRmax hRunder
      have hRnorm : Ideal.absNorm R = p := by
        rcases hRPQ with rfl | rfl
        · exact hPnorm
        · exact hQnorm
      have hJnorm : Ideal.absNorm J = p ^ k := by
        apply Nat.eq_of_mul_eq_mul_left hp.pos
        calc
          p * Ideal.absNorm J = Ideal.absNorm (R * J) := by simp [hRnorm]
          _ = Ideal.absNorm I := by rw [hIJ]
          _ = p * p ^ k := by rw [hI, pow_succ]; ac_rfl
      obtain ⟨j, hj, hJ⟩ := ih hJnorm
      rcases hRPQ with rfl | rfl
      · refine ⟨j + 1, by omega, ?_⟩
        have hsub : k + 1 - (j + 1) = k - j := by omega
        rw [hIJ, hJ, hsub, pow_succ]
        simp only [mul_comm, mul_left_comm]
      · refine ⟨j, by omega, ?_⟩
        have hsub : k + 1 - j = (k - j) + 1 := by omega
        rw [hIJ, hJ, hsub, pow_succ]
        simp only [mul_comm, mul_left_comm]

/-- Distinct norm-`p` ideals have unique exponents in any product of their
powers.  Coprimality of their maximal ideals separates the two factors. -/
theorem primePow_mul_primePow_exponents_eq_of_distinct_norm_prime
    (K : Type*) [Field K] [NumberField K] (p : ℕ) (hp : Nat.Prime p)
    (P Q : Ideal (𝓞 K)) (hPnorm : Ideal.absNorm P = p) (hQnorm : Ideal.absNorm Q = p)
    (hPQ : P ≠ Q) {a b c d : ℕ} (h : P ^ a * Q ^ b = P ^ c * Q ^ d) :
    a = c ∧ b = d := by
  have hcoprime : IsCoprime P Q := Ideal.isCoprime_iff_sup_eq.mpr
    ((isMaximal_of_absNorm_eq_prime K p hp P hPnorm).coprime_of_ne
      (isMaximal_of_absNorm_eq_prime K p hp Q hQnorm) hPQ)
  have hPa_dvd_Pc : P ^ a ∣ P ^ c :=
    (show IsCoprime (P ^ a) (Q ^ d) from hcoprime.pow).dvd_of_dvd_mul_right
      ⟨Q ^ b, h.symm⟩
  have hPc_dvd_Pa : P ^ c ∣ P ^ a :=
    (show IsCoprime (P ^ c) (Q ^ b) from hcoprime.pow).dvd_of_dvd_mul_right
      ⟨Q ^ d, h⟩
  have hPpowers : P ^ a = P ^ c := le_antisymm
    (Ideal.dvd_iff_le.mp hPc_dvd_Pa) (Ideal.dvd_iff_le.mp hPa_dvd_Pc)
  have hpowers : p ^ a = p ^ c := by
    simpa only [map_pow, hPnorm] using congrArg Ideal.absNorm hPpowers
  have hac : a = c := Nat.pow_right_injective hp.two_le hpowers
  have hsum : p ^ (a + b) = p ^ (c + d) := by
    simpa only [map_mul, map_pow, hPnorm, hQnorm, ← pow_add] using
      congrArg Ideal.absNorm h
  have habcd : a + b = c + d := Nat.pow_right_injective hp.two_le hsum
  exact ⟨hac, by omega⟩

/-- The exponent is unique within the actual range `0 ≤ j ≤ k`. -/
theorem ideal_existsUnique_primePow_mul_primePow_of_twoPrimesOver
    (K : Type*) [Field K] [NumberField K] (p k : ℕ) (hp : Nat.Prime p)
    (P Q : Ideal (𝓞 K)) (hPnorm : Ideal.absNorm P = p) (hQnorm : Ideal.absNorm Q = p)
    (hPQ : P ≠ Q)
    (hexhaust : ∀ R : Ideal (𝓞 K), R.IsMaximal →
      R.under ℤ = Ideal.span ({(p : ℤ)} : Set ℤ) → R = P ∨ R = Q)
    {I : Ideal (𝓞 K)} (hI : Ideal.absNorm I = p ^ k) :
    ∃! j : Fin (k + 1), I = P ^ (j : ℕ) * Q ^ (k - (j : ℕ)) := by
  obtain ⟨j, hj, hIj⟩ :=
    ideal_eq_primePow_mul_primePow_of_absNorm_eq_primePow_of_twoPrimesOver
      K p k hp P Q hPnorm hQnorm hexhaust hI
  refine ⟨⟨j, by omega⟩, hIj, ?_⟩
  intro l hl
  apply Fin.ext
  exact (primePow_mul_primePow_exponents_eq_of_distinct_norm_prime
    K p hp P Q hPnorm hQnorm hPQ (hl.symm.trans hIj)).1

/-- Enumerate the actual norm-`p^k` fibre by the exponent of the first of
the two primes.  Finiteness follows from this equivalence. -/
noncomputable def finEquivIdealNormFibrePrimePowOfTwoPrimesOver
    (K : Type*) [Field K] [NumberField K] (p k : ℕ) (hp : Nat.Prime p)
    (P Q : Ideal (𝓞 K)) (hPnorm : Ideal.absNorm P = p) (hQnorm : Ideal.absNorm Q = p)
    (hPQ : P ≠ Q)
    (hexhaust : ∀ R : Ideal (𝓞 K), R.IsMaximal →
      R.under ℤ = Ideal.span ({(p : ℤ)} : Set ℤ) → R = P ∨ R = Q) :
    Fin (k + 1) ≃ {I : Ideal (𝓞 K) // Ideal.absNorm I = p ^ k} := by
  let f : Fin (k + 1) → {I : Ideal (𝓞 K) // Ideal.absNorm I = p ^ k} := fun j =>
    ⟨P ^ (j : ℕ) * Q ^ (k - (j : ℕ)), by
      rw [map_mul, map_pow, map_pow, hPnorm, hQnorm, ← pow_add,
        Nat.add_sub_of_le (Nat.le_of_lt_succ j.2)]⟩
  apply Equiv.ofBijective f
  constructor
  · intro j l hjl
    apply Fin.ext
    exact (primePow_mul_primePow_exponents_eq_of_distinct_norm_prime
      K p hp P Q hPnorm hQnorm hPQ (congrArg Subtype.val hjl)).1
  · rintro ⟨I, hI⟩
    obtain ⟨j, hj, _⟩ := ideal_existsUnique_primePow_mul_primePow_of_twoPrimesOver
      K p k hp P Q hPnorm hQnorm hPQ hexhaust hI
    refine ⟨j, ?_⟩
    apply Subtype.ext
    exact hj.symm

/-- There are exactly `k+1` ideals of norm `p^k` under the two-prime local
decomposition hypotheses, including the unit-ideal case `k=0`. -/
theorem card_idealNormFibre_primePow_of_twoPrimesOver_norm_prime
    (K : Type*) [Field K] [NumberField K] (p k : ℕ) (hp : Nat.Prime p)
    (P Q : Ideal (𝓞 K)) (hPnorm : Ideal.absNorm P = p) (hQnorm : Ideal.absNorm Q = p)
    (hPQ : P ≠ Q)
    (hexhaust : ∀ R : Ideal (𝓞 K), R.IsMaximal →
      R.under ℤ = Ideal.span ({(p : ℤ)} : Set ℤ) → R = P ∨ R = Q) :
    Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = p ^ k} = k + 1 := by
  simpa using (Nat.card_congr
    (finEquivIdealNormFibrePrimePowOfTwoPrimesOver K p k hp P Q hPnorm hQnorm hPQ hexhaust)).symm

/-- The split local geometric factor follows from the two-prime local
decomposition and the explicit value `χ(p)=1`. -/
theorem idealNormPrimePowerGeometricSum_of_twoPrimesOver_of_apply_eq_one
    (K : Type*) [Field K] [NumberField K] (p k : ℕ) (hp : Nat.Prime p)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (P Q : Ideal (𝓞 K)) (hPnorm : Ideal.absNorm P = p) (hQnorm : Ideal.absNorm Q = p)
    (hPQ : P ≠ Q)
    (hexhaust : ∀ R : Ideal (𝓞 K), R.IsMaximal →
      R.under ℤ = Ideal.span ({(p : ℤ)} : Set ℤ) → R = P ∨ R = Q)
    (hχ : χ p = 1) :
    (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = p ^ k} : ℂ) =
      ∑ j ∈ Finset.range (k + 1), χ p ^ j := by
  rw [card_idealNormFibre_primePow_of_twoPrimesOver_norm_prime
    K p k hp P Q hPnorm hQnorm hPQ hexhaust]
  simp [hχ]

end

end PellPaper
