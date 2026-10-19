import Pell.QuadraticIdealNormRamifiedUniquePrime
import Pell.QuadraticIdealNormLocalUniquePrime
import Pell.QuadraticKroneckerCharacterQuadraticity

/-!
# The concrete ramified prime-power coefficient

For a prime `p` dividing a positive fundamental discriminant `D`, there is
exactly one integral ideal of norm `p^k` in the attached quadratic field.
The selected character vanishes at `p` because it is a nonunit modulo `D`.
Together these give the ramified branch of the local geometric-sum identity,
without a supplied splitting, uniqueness, norm, or character-value hypothesis.

The split and inert branches, conductor identification, and global analytic
identities are outside the scope of this module.
-/

namespace PellPaper

noncomputable section

local instance rationalQuadraticAlgebra_ramifiedPrimePower_numberField_instance (d : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot d)] :
    NumberField (rationalQuadraticAlgebra d) :=
  rationalQuadraticAlgebra_numberField d

/-- Every Dirichlet character vanishes on a prime dividing its level. -/
theorem dirichletCharacter_apply_prime_eq_zero_of_dvd_level
    {R : Type*} [CommMonoidWithZero R] {D p : ℕ}
    (χ : DirichletCharacter R D) (hp : Nat.Prime p) (hpD : p ∣ D) :
    χ p = 0 := by
  apply MulChar.map_nonunit
  rw [ZMod.isUnit_iff_coprime, hp.coprime_iff_not_dvd]
  exact not_not.mpr hpD

/-- The actual prime-power ideal-norm fibre is a singleton in the ramified case. -/
theorem rationalQuadraticAlgebra_card_idealNormFibre_primePow_eq_one_of_prime_dvd_discriminant
    (D p k : ℕ) (hD : PositiveFundamentalDiscriminant D)
    (hp : Nat.Prime p) (hpD : p ∣ D) :
    let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
      ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
    Nat.card {I : Ideal (NumberField.RingOfIntegers
      (rationalQuadraticAlgebra (D : ℤ))) // Ideal.absNorm I = p ^ k} = 1 := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  let _ : Fact (Nat.Prime p) := ⟨hp⟩
  obtain ⟨P, hPnorm, hunique⟩ :=
    rationalQuadraticAlgebra_exists_uniquePrimeOver_of_prime_dvd_positiveFundamentalDiscriminant
      D p hD hp hpD
  exact card_idealNormFibre_primePow_eq_one_of_uniquePrimeOver
    (rationalQuadraticAlgebra (D : ℤ)) p k hp P hPnorm hunique

/-- The ramified local geometric-sum identity for the selected complex
character and the actual ideals of the quadratic field. -/
theorem rationalQuadraticAlgebra_idealNormPrimePowerGeometricSum_of_prime_dvd_discriminant
    (D p k : ℕ) (hD : PositiveFundamentalDiscriminant D)
    (hp : Nat.Prime p) (hpD : p ∣ D) :
    let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
      ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
    (Nat.card {I : Ideal (NumberField.RingOfIntegers
      (rationalQuadraticAlgebra (D : ℤ))) // Ideal.absNorm I = p ^ k} : ℂ) =
      ∑ j ∈ Finset.range (k + 1),
        kroneckerCharacterAtPositiveFundamentalDiscriminantC D hD p ^ j := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  dsimp only
  rw [rationalQuadraticAlgebra_card_idealNormFibre_primePow_eq_one_of_prime_dvd_discriminant
    D p k hD hp hpD]
  simp [dirichletCharacter_apply_prime_eq_zero_of_dvd_level
    (kroneckerCharacterAtPositiveFundamentalDiscriminantC D hD) hp hpD]

end

end PellPaper
