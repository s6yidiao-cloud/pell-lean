import Pell.QuadraticIdealNormEulerCoefficient

/-!
# Coprime ideal-norm fibre multiplication

An isolated investigation of the missing multiplicativity input for the
zero-normalized ideal-norm coefficient.  This file is deliberately not yet
imported by the project root.
-/

namespace PellPaper

open NumberField

noncomputable section

/-- Ideals in coprime norm fibres are coprime.  The proof uses the fact that
an ideal contains its absolute norm, so it divides the corresponding principal
ideal. -/
theorem idealNormFibre_isCoprime
    (K : Type*) [Field K] [NumberField K]
    {m n : ℕ} (hmn : m.Coprime n)
    {I J : Ideal (𝓞 K)}
    (hI : Ideal.absNorm I = m) (hJ : Ideal.absNorm J = n) :
    IsCoprime I J := by
  have hI_dvd : I ∣ Ideal.span ({(m : 𝓞 K)} : Set (𝓞 K)) :=
    Ideal.dvd_iff_le.mpr (by simpa [hI] using Ideal.span_singleton_absNorm_le I)
  have hJ_dvd : J ∣ Ideal.span ({(n : 𝓞 K)} : Set (𝓞 K)) :=
    Ideal.dvd_iff_le.mpr (by simpa [hJ] using Ideal.span_singleton_absNorm_le J)
  apply IsCoprime.mono hI_dvd hJ_dvd
  rw [Ideal.isCoprime_span_singleton_iff]
  exact hmn.cast

/-- Multiplication sends a pair of fixed ideal-norm fibres to the product
norm fibre.  This definition includes the norm-zero fibres, rather than
silently discarding them. -/
def idealNormFibreMul
    (K : Type*) [Field K] [NumberField K] (m n : ℕ) :
    {I : Ideal (𝓞 K) // Ideal.absNorm I = m} ×
        {J : Ideal (𝓞 K) // Ideal.absNorm J = n} →
      {L : Ideal (𝓞 K) // Ideal.absNorm L = m * n} := fun IJ ↦
  ⟨IJ.1.1 * IJ.2.1, by
    simp only [map_mul, IJ.1.2, IJ.2.2]⟩

/-- On coprime norm fibres, ideal multiplication is injective.  This is the
nontrivial half of the desired coefficient multiplicativity: the remaining
surjectivity is the ideal-factor allocation step. -/
theorem idealNormFibreMul_injective
    (K : Type*) [Field K] [NumberField K]
    {m n : ℕ} (hmn : m.Coprime n) :
    Function.Injective (idealNormFibreMul K m n) := by
  rintro ⟨⟨I, hI⟩, ⟨J, hJ⟩⟩ ⟨⟨I', hI'⟩, ⟨J', hJ'⟩⟩ h
  have hmul : I * J = I' * J' := congrArg Subtype.val h
  change I * J = I' * J' at hmul
  rcases eq_or_ne m 0 with rfl | hm
  · have hn : n = 1 := (n.coprime_zero_left).mp hmn
    have hI_bot : I = ⊥ := Ideal.absNorm_eq_zero_iff.mp hI
    have hI'_bot : I' = ⊥ := Ideal.absNorm_eq_zero_iff.mp hI'
    have hJ_top : J = ⊤ := Ideal.absNorm_eq_one_iff.mp (hJ.trans hn)
    have hJ'_top : J' = ⊤ := Ideal.absNorm_eq_one_iff.mp (hJ'.trans hn)
    subst I
    subst I'
    subst J
    subst J'
    rfl
  have hIJ' : IsCoprime I J' := idealNormFibre_isCoprime K hmn hI hJ'
  have hI'J : IsCoprime I' J := idealNormFibre_isCoprime K hmn hI' hJ
  have hI_dvd : I ∣ I' := hIJ'.dvd_of_dvd_mul_right ⟨J, hmul.symm⟩
  have hI'_dvd : I' ∣ I := hI'J.dvd_of_dvd_mul_right ⟨J', hmul⟩
  have hII' : I = I' := by
    apply le_antisymm
    · exact Ideal.dvd_iff_le.mp hI'_dvd
    · exact Ideal.dvd_iff_le.mp hI_dvd
  subst I'
  have hJJ' : J = J' := by
    apply mul_left_cancel₀
    · intro hI_bot
      apply hm
      calc
        m = Ideal.absNorm I := hI.symm
        _ = 0 := Ideal.absNorm_eq_zero_iff.mpr hI_bot
    · exact hmul
  subst J'
  rfl

/-- The coprime-fibre product map gives the precise lower bound on raw ideal
norm coefficients.  It remains valid in the endpoint cases forced by
`m.Coprime n`, including a zero factor paired with one. -/
theorem card_idealNormFibre_mul_le
    (K : Type*) [Field K] [NumberField K]
    {m n : ℕ} (hmn : m.Coprime n) :
    Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = m} *
        Nat.card {J : Ideal (𝓞 K) // Ideal.absNorm J = n} ≤
      Nat.card {L : Ideal (𝓞 K) // Ideal.absNorm L = m * n} := by
  let hfinite : Finite {L : Ideal (𝓞 K) // Ideal.absNorm L = m * n} :=
    Fintype.finite (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) (m * n)).fintype
  rw [← Nat.card_prod]
  exact @Nat.card_le_card_of_injective _ _ hfinite (idealNormFibreMul K m n)
    (idealNormFibreMul_injective K hmn)

end

end PellPaper
