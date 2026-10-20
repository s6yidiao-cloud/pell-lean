import Pell.QuadraticIdealNormLocalUniquePrime
import Mathlib.Algebra.BigOperators.Fin

/-!
# Ideal-norm fibres at a unique prime of residue degree two

Suppose the only maximal ideal over a rational prime `p` is `P`, and
`absNorm P = p²`.  An ideal of norm `p^k` must be a power `P^j` with `k = 2j`.
Consequently the norm fibre has cardinality one for even `k` and zero for
odd `k`.  If a character takes the value `-1` at `p`, this is its local
geometric sum.

All local uniqueness, norm, and character-value inputs are explicit.  This
module makes no concrete splitting or quadratic-character identification.
-/

namespace PellPaper

open NumberField

noncomputable section

private theorem exists_factor_of_uniquePrimeOver_norm_sq
    (K : Type*) [Field K] [NumberField K] (p k : ℕ) (hp : Nat.Prime p)
    (hk : k ≠ 0) (P : Ideal (𝓞 K)) (hPnorm : Ideal.absNorm P = p ^ 2)
    (hunique : ∀ Q : Ideal (𝓞 K), Q.IsMaximal →
      Q.under ℤ = Ideal.span ({(p : ℤ)} : Set ℤ) → Q = P)
    {I : Ideal (𝓞 K)} (hI : Ideal.absNorm I = p ^ k) :
    ∃ J : Ideal (𝓞 K), I = P * J ∧ p ^ 2 * Ideal.absNorm J = p ^ k := by
  have hp_dvd : p ∣ Ideal.absNorm I := by
    rw [hI]
    exact dvd_pow_self _ hk
  obtain ⟨Q, hQmax, hQunder, hQdvd⟩ :=
    Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp I hp_dvd
  obtain ⟨J, hIJ⟩ := hQdvd
  have hQP : Q = P := hunique Q hQmax hQunder
  subst Q
  refine ⟨J, hIJ, ?_⟩
  calc
    p ^ 2 * Ideal.absNorm J = Ideal.absNorm (P * J) := by simp [hPnorm]
    _ = p ^ k := by rw [← hIJ, hI]

/-- With a unique prime over `p` of norm `p²`, every ideal of norm `p^k`
has the unique possible power shape, with an even exponent `k = 2j`. -/
theorem ideal_eq_primePow_of_absNorm_eq_primePow_of_uniquePrimeOver_norm_sq
    (K : Type*) [Field K] [NumberField K] (p k : ℕ) (hp : Nat.Prime p)
    (P : Ideal (𝓞 K)) (hPnorm : Ideal.absNorm P = p ^ 2)
    (hunique : ∀ Q : Ideal (𝓞 K), Q.IsMaximal →
      Q.under ℤ = Ideal.span ({(p : ℤ)} : Set ℤ) → Q = P)
    {I : Ideal (𝓞 K)} (hI : Ideal.absNorm I = p ^ k) :
    ∃ j : ℕ, k = 2 * j ∧ I = P ^ j := by
  induction k using Nat.twoStepInduction generalizing I with
  | zero =>
      refine ⟨0, rfl, ?_⟩
      simpa using Ideal.absNorm_eq_one_iff.mp (by simpa using hI)
  | one =>
      obtain ⟨J, _, hJ⟩ :=
        exists_factor_of_uniquePrimeOver_norm_sq K p 1 hp (by decide) P hPnorm hunique hI
      have hle : p ^ 2 ≤ p := Nat.le_of_dvd hp.pos ⟨Ideal.absNorm J, by simpa using hJ.symm⟩
      have hp2 := hp.two_le
      nlinarith
  | more k ih _ =>
      obtain ⟨J, hIJ, hJmul⟩ :=
        exists_factor_of_uniquePrimeOver_norm_sq K p (k + 2) hp (by omega)
          P hPnorm hunique hI
      have hJ : Ideal.absNorm J = p ^ k := by
        apply Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2)
        calc
          p ^ 2 * Ideal.absNorm J = p ^ (k + 2) := hJmul
          _ = p ^ 2 * p ^ k := by rw [pow_add]; ac_rfl
      obtain ⟨j, hkj, hJP⟩ := ih hJ
      refine ⟨j + 1, by omega, ?_⟩
      rw [hIJ, hJP, pow_succ]
      ac_rfl

/-- The norm-`p^k` fibre is a singleton for even `k` and empty for odd `k`
under the unique-prime/norm-`p²` assumptions. -/
theorem card_idealNormFibre_primePow_of_uniquePrimeOver_norm_sq
    (K : Type*) [Field K] [NumberField K] (p k : ℕ) (hp : Nat.Prime p)
    (P : Ideal (𝓞 K)) (hPnorm : Ideal.absNorm P = p ^ 2)
    (hunique : ∀ Q : Ideal (𝓞 K), Q.IsMaximal →
      Q.under ℤ = Ideal.span ({(p : ℤ)} : Set ℤ) → Q = P) :
    Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = p ^ k} =
      if Even k then 1 else 0 := by
  classical
  by_cases hk : Even k
  · rw [if_pos hk]
    obtain ⟨j, hkj⟩ := even_iff_exists_two_mul.mp hk
    apply Nat.card_eq_one_iff_unique.mpr
    constructor
    · constructor
      rintro ⟨I, hI⟩ ⟨J, hJ⟩
      apply Subtype.ext
      change I = J
      obtain ⟨i, hki, hIP⟩ :=
        ideal_eq_primePow_of_absNorm_eq_primePow_of_uniquePrimeOver_norm_sq
          K p k hp P hPnorm hunique hI
      obtain ⟨l, hkl, hJP⟩ :=
        ideal_eq_primePow_of_absNorm_eq_primePow_of_uniquePrimeOver_norm_sq
          K p k hp P hPnorm hunique hJ
      have hil : i = l := by omega
      rw [hIP, hJP, hil]
    · refine ⟨⟨P ^ j, ?_⟩⟩
      rw [map_pow, hPnorm, ← pow_mul, hkj]
  · rw [if_neg hk]
    have hempty : IsEmpty {I : Ideal (𝓞 K) // Ideal.absNorm I = p ^ k} := by
      constructor
      rintro ⟨I, hI⟩
      obtain ⟨j, hkj, _⟩ :=
        ideal_eq_primePow_of_absNorm_eq_primePow_of_uniquePrimeOver_norm_sq
          K p k hp P hPnorm hunique hI
      exact hk (even_iff_exists_two_mul.mpr ⟨j, hkj⟩)
    exact Nat.card_eq_zero.mpr (Or.inl hempty)

/-- The inert local geometric factor follows from the unique-prime/norm-`p²`
inputs and the explicit character value `χ(p) = -1`. -/
theorem idealNormPrimePowerGeometricSum_of_uniquePrimeOver_of_apply_eq_neg_one
    (K : Type*) [Field K] [NumberField K] (p k : ℕ) (hp : Nat.Prime p)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (P : Ideal (𝓞 K)) (hPnorm : Ideal.absNorm P = p ^ 2)
    (hunique : ∀ Q : Ideal (𝓞 K), Q.IsMaximal →
      Q.under ℤ = Ideal.span ({(p : ℤ)} : Set ℤ) → Q = P)
    (hχ : χ p = -1) :
    (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = p ^ k} : ℂ) =
      ∑ j ∈ Finset.range (k + 1), χ p ^ j := by
  rw [card_idealNormFibre_primePow_of_uniquePrimeOver_norm_sq K p k hp P hPnorm hunique,
    hχ, ← Fin.sum_univ_eq_sum_range, Fin.sum_neg_one_pow]
  simp only [Nat.even_add_one, ite_not]
  split_ifs <;> simp

end

end PellPaper
