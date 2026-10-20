import Pell.QuadraticIdealNormMultiplicativity

/-!
# Coprime ideal-norm fibre factor allocation

For coprime positive natural numbers, an integral ideal of norm `m * n`
admits a factorization into ideals of norms `m` and `n`.  The proof uses the
decomposition-monoid factor allocation for ideals, followed by a natural-number
coprimality argument.  The norm-zero endpoint is handled separately: a
coprime pair containing zero has the other factor equal to one.

This module is intentionally isolated pending independent review.
-/

namespace PellPaper

open NumberField

noncomputable section

/-- Coprime ideal-norm fibre multiplication is surjective.  In the positive
case, first allocate a divisor of the principal ideal `(m*n)` between `(m)`
and `(n)`, then use the coprimality of `m` and `n` to identify the two norms.
The cases with a zero norm are exactly `(0, 1)` and `(1, 0)`. -/
theorem idealNormFibreMul_surjective
    (K : Type*) [Field K] [NumberField K]
    {m n : ℕ} (hmn : m.Coprime n) :
    Function.Surjective (idealNormFibreMul K m n) := by
  rintro ⟨L, hL⟩
  rcases eq_or_ne m 0 with rfl | hm
  · have hn : n = 1 := (n.coprime_zero_left).mp hmn
    subst n
    have hL_bot : L = ⊥ := Ideal.absNorm_eq_zero_iff.mp (by simpa using hL)
    subst L
    refine ⟨⟨⟨⊥, by simp⟩, ⟨⊤, by simp⟩⟩, ?_⟩
    apply Subtype.ext
    simp [idealNormFibreMul]
  rcases eq_or_ne n 0 with rfl | hn
  · have hm_one : m = 1 := (m.coprime_zero_right).mp hmn
    subst m
    have hL_bot : L = ⊥ := Ideal.absNorm_eq_zero_iff.mp (by simpa using hL)
    subst L
    refine ⟨⟨⟨⊤, by simp⟩, ⟨⊥, by simp⟩⟩, ?_⟩
    apply Subtype.ext
    simp [idealNormFibreMul]
  have hL_dvd : L ∣ Ideal.span ({((m * n : ℕ) : 𝓞 K)} : Set (𝓞 K)) :=
    Ideal.dvd_iff_le.mpr (by simpa [hL] using Ideal.span_singleton_absNorm_le L)
  have hL_dvd_mul : L ∣
      Ideal.span ({(m : 𝓞 K)} : Set (𝓞 K)) *
        Ideal.span ({(n : 𝓞 K)} : Set (𝓞 K)) := by
    simpa [Ideal.span_singleton_mul_span_singleton] using hL_dvd
  obtain ⟨I, J, hI_dvd, hJ_dvd, hIJ⟩ := exists_dvd_and_dvd_of_dvd_mul hL_dvd_mul
  have hnorm_prod : Ideal.absNorm I * Ideal.absNorm J = m * n := by
    calc
      Ideal.absNorm I * Ideal.absNorm J = Ideal.absNorm (I * J) := by simp
      _ = Ideal.absNorm L := by rw [hIJ]
      _ = m * n := hL
  have hI_norm_dvd : Ideal.absNorm I ∣ m ^ Module.finrank ℤ (𝓞 K) := by
    calc
      Ideal.absNorm I ∣ Ideal.absNorm (Ideal.span ({(m : 𝓞 K)} : Set (𝓞 K))) :=
        Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp hI_dvd)
      _ = m ^ Module.finrank ℤ (𝓞 K) := Ideal.absNorm_span_natCast m
  have hJ_norm_dvd : Ideal.absNorm J ∣ n ^ Module.finrank ℤ (𝓞 K) := by
    calc
      Ideal.absNorm J ∣ Ideal.absNorm (Ideal.span ({(n : 𝓞 K)} : Set (𝓞 K))) :=
        Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp hJ_dvd)
      _ = n ^ Module.finrank ℤ (𝓞 K) := Ideal.absNorm_span_natCast n
  have hI_coprime_n : (Ideal.absNorm I).Coprime n :=
    (hmn.pow_left _).of_dvd_left hI_norm_dvd
  have hJ_coprime_m : (Ideal.absNorm J).Coprime m :=
    (hmn.symm.pow_left _).of_dvd_left hJ_norm_dvd
  have hI_dvd_mn : Ideal.absNorm I ∣ m * n := ⟨Ideal.absNorm J, hnorm_prod.symm⟩
  have hJ_dvd_mn : Ideal.absNorm J ∣ m * n := by
    rw [← hnorm_prod]
    exact dvd_mul_left _ _
  have hI_dvd_m : Ideal.absNorm I ∣ m :=
    hI_coprime_n.dvd_of_dvd_mul_right hI_dvd_mn
  have hJ_dvd_n : Ideal.absNorm J ∣ n := by
    apply hJ_coprime_m.dvd_of_dvd_mul_left
    simpa [mul_comm] using hJ_dvd_mn
  have hm_dvd_I : m ∣ Ideal.absNorm I := by
    apply (hmn.of_dvd_right hJ_dvd_n).dvd_of_dvd_mul_right
    rw [hnorm_prod]
    exact dvd_mul_right _ _
  have hn_dvd_J : n ∣ Ideal.absNorm J := by
    apply (hmn.symm.of_dvd_right hI_dvd_m).dvd_of_dvd_mul_left
    rw [hnorm_prod]
    exact dvd_mul_left _ _
  have hI_norm : Ideal.absNorm I = m := Nat.dvd_antisymm hI_dvd_m hm_dvd_I
  have hJ_norm : Ideal.absNorm J = n := Nat.dvd_antisymm hJ_dvd_n hn_dvd_J
  refine ⟨⟨⟨I, hI_norm⟩, ⟨J, hJ_norm⟩⟩, ?_⟩
  apply Subtype.ext
  exact hIJ.symm

/-- The multiplication map on coprime ideal-norm fibres is an equivalence. -/
noncomputable def idealNormFibreMulEquiv
    (K : Type*) [Field K] [NumberField K]
    {m n : ℕ} (hmn : m.Coprime n) :
    {I : Ideal (𝓞 K) // Ideal.absNorm I = m} ×
        {J : Ideal (𝓞 K) // Ideal.absNorm J = n} ≃
      {L : Ideal (𝓞 K) // Ideal.absNorm L = m * n} :=
  Equiv.ofBijective (idealNormFibreMul K m n)
    ⟨idealNormFibreMul_injective K hmn, idealNormFibreMul_surjective K hmn⟩

/-- The raw ideal-norm coefficient is multiplicative at coprime inputs,
including the zero/unit endpoint cases. -/
theorem card_idealNormFibre_mul_eq
    (K : Type*) [Field K] [NumberField K]
    {m n : ℕ} (hmn : m.Coprime n) :
    Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = m} *
        Nat.card {J : Ideal (𝓞 K) // Ideal.absNorm J = n} =
      Nat.card {L : Ideal (𝓞 K) // Ideal.absNorm L = m * n} := by
  rw [← Nat.card_prod]
  exact Nat.card_congr (idealNormFibreMulEquiv K hmn)

/-- The zero-normalized ideal-norm coefficient is a multiplicative arithmetic
function.  Its special normalization at zero is compatible with the only
coprime zero cases, namely `(0,1)` and `(1,0)`. -/
theorem idealNormCoefficient_isMultiplicative
    (K : Type*) [Field K] [NumberField K] :
    (idealNormCoefficient K).IsMultiplicative := by
  refine ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr ⟨idealNormCoefficient_one K, ?_⟩
  intro m n hm hn hmn
  rw [idealNormCoefficient_apply_of_ne_zero K (Nat.mul_ne_zero hm hn),
    idealNormCoefficient_apply_of_ne_zero K hm,
    idealNormCoefficient_apply_of_ne_zero K hn]
  exact_mod_cast (card_idealNormFibre_mul_eq K hmn).symm

end

end PellPaper
