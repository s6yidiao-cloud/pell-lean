import Pell.QuadraticIdealNormEulerCoefficient

/-!
# A unique-prime local ideal-norm bridge

This module records the elementary counting consequence of a local
decomposition statement: if every maximal ideal over a rational prime `p` is
one fixed ideal `P`, and `P` has absolute norm `p`, then there is exactly one
integral ideal of each norm `p^k`, namely `P^k`.

It does not establish that uniqueness or norm condition for the concrete
real quadratic fields, and it does not identify the result with a Kronecker
character value.  Those remain the ramified-prime part of the local
prime-power frontier.
-/

namespace PellPaper

open NumberField

noncomputable section

/-- Under a unique-prime-over-`p` hypothesis, every ideal of absolute norm
`p^k` is the indicated power of that prime ideal. -/
theorem ideal_eq_primePow_of_absNorm_eq_primePow_of_uniquePrimeOver
    (K : Type*) [Field K] [NumberField K] (p k : ℕ) (hp : Nat.Prime p)
    (P : Ideal (𝓞 K)) (hPnorm : Ideal.absNorm P = p)
    (hunique : ∀ Q : Ideal (𝓞 K), Q.IsMaximal →
      Q.under ℤ = Ideal.span ({(p : ℤ)} : Set ℤ) → Q = P)
    {I : Ideal (𝓞 K)} (hI : Ideal.absNorm I = p ^ k) :
    I = P ^ k := by
  induction k generalizing I with
  | zero =>
      simpa using (Ideal.absNorm_eq_one_iff.mp (by simpa using hI))
  | succ k ih =>
      have hp_dvd : p ∣ Ideal.absNorm I := by
        rw [hI]
        exact dvd_pow_self _ (Nat.succ_ne_zero _)
      obtain ⟨Q, hQmax, hQunder, hQdvd⟩ :=
        Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp I hp_dvd
      obtain ⟨J, hIJ⟩ := hQdvd
      have hQP : Q = P := hunique Q hQmax hQunder
      subst Q
      have hJ : Ideal.absNorm J = p ^ k := by
        apply Nat.eq_of_mul_eq_mul_left hp.pos
        calc
          p * Ideal.absNorm J = Ideal.absNorm (P * J) := by
            simp [hPnorm]
          _ = Ideal.absNorm I := by rw [hIJ]
          _ = p * p ^ k := by
            rw [hI, pow_succ]
            ac_rfl
      rw [hIJ, ih hJ]
      simp [pow_succ, mul_comm]

/-- The preceding uniqueness result makes the prime-power ideal-norm fibre a
singleton. -/
theorem card_idealNormFibre_primePow_eq_one_of_uniquePrimeOver
    (K : Type*) [Field K] [NumberField K] (p k : ℕ) (hp : Nat.Prime p)
    (P : Ideal (𝓞 K)) (hPnorm : Ideal.absNorm P = p)
    (hunique : ∀ Q : Ideal (𝓞 K), Q.IsMaximal →
      Q.under ℤ = Ideal.span ({(p : ℤ)} : Set ℤ) → Q = P) :
    Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = p ^ k} = 1 := by
  apply Nat.card_eq_one_iff_unique.mpr
  constructor
  · constructor
    rintro ⟨I, hI⟩ ⟨J, hJ⟩
    apply Subtype.ext
    exact (ideal_eq_primePow_of_absNorm_eq_primePow_of_uniquePrimeOver
      K p k hp P hPnorm hunique hI).trans
      (ideal_eq_primePow_of_absNorm_eq_primePow_of_uniquePrimeOver
        K p k hp P hPnorm hunique hJ).symm
  · refine ⟨⟨P ^ k, ?_⟩⟩
    simp [hPnorm]

/-- The ramified local geometric factor follows once the selected character
vanishes at `p`.  The hypotheses here are precisely the local uniqueness and
norm assertions; no concrete quadratic splitting result is supplied. -/
theorem idealNormPrimePowerGeometricSum_of_uniquePrimeOver_of_apply_eq_zero
    (K : Type*) [Field K] [NumberField K] (p k : ℕ) (hp : Nat.Prime p)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (P : Ideal (𝓞 K)) (hPnorm : Ideal.absNorm P = p)
    (hunique : ∀ Q : Ideal (𝓞 K), Q.IsMaximal →
      Q.under ℤ = Ideal.span ({(p : ℤ)} : Set ℤ) → Q = P)
    (hχ : χ p = 0) :
    (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = p ^ k} : ℂ) =
      ∑ j ∈ Finset.range (k + 1), χ p ^ j := by
  rw [card_idealNormFibre_primePow_eq_one_of_uniquePrimeOver K p k hp P hPnorm hunique]
  simp [hχ]

end

end PellPaper
