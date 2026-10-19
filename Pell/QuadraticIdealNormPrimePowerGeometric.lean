import Pell.QuadraticKroneckerCharacterOddPrimeSplitting
import Pell.QuadraticKroneckerCharacterAtTwo
import Pell.QuadraticIdealNormUnramifiedDichotomy
import Pell.QuadraticIdealNormLocalInert
import Pell.QuadraticIdealNormLocalSplit
import Pell.QuadraticIdealNormRamifiedPrimePower

/-!
# Actual prime-power ideal-norm coefficients for the selected character

For every positive fundamental discriminant `D`, rational prime `p`, and
exponent `k`, the actual norm-`p^k` ideal fibre has cardinality equal to the
geometric sum of the selected complex character at `p`.  The ramified case
uses the proved unique-prime count.  In the unramified cases, the genuine
prime-ideal dichotomy supplies the local ideals, and existence or absence
of a norm-`p` ideal determines the character value, including at `p = 2`.

There are no supplied splitting, local counting, or character-value
hypotheses.  The theorem includes `k = 0`.  It does not assert primitivity,
a conductor formula, an all-integer Kronecker identification, or a
class-number formula.
-/

namespace PellPaper

noncomputable section

local instance rationalQuadraticAlgebra_primePowerGeometric_numberField_instance (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    NumberField (rationalQuadraticAlgebra D) :=
  rationalQuadraticAlgebra_numberField D

private theorem selectedCharacter_unramified_prime_values_iff_ideal_exists
    (D p : ℕ) (hD : PositiveFundamentalDiscriminant D)
    (hp : Nat.Prime p) (hpD : ¬ p ∣ D) :
    let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
      ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
    (kroneckerCharacterAtPositiveFundamentalDiscriminantC D hD p = 1 ↔
      ∃ I : Ideal (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))),
        Ideal.absNorm I = p) ∧
    (kroneckerCharacterAtPositiveFundamentalDiscriminantC D hD p = -1 ↔
      ¬ ∃ I : Ideal (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))),
        Ideal.absNorm I = p) := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  dsimp only
  by_cases hp2 : p = 2
  · subst p
    have hodd : Odd D := Nat.not_even_iff_odd.mp (fun heven => hpD heven.two_dvd)
    exact ⟨kroneckerCharacterC_eq_one_iff_exists_ideal_absNorm_eq_two D hD hodd,
      kroneckerCharacterC_eq_neg_one_iff_not_exists_ideal_absNorm_eq_two D hD hodd⟩
  · exact ⟨kroneckerCharacterC_eq_one_iff_exists_ideal_absNorm_eq_odd_prime
      D p hD hp hp2 hpD,
      kroneckerCharacterC_eq_neg_one_iff_not_exists_ideal_absNorm_eq_odd_prime
        D p hD hp hp2 hpD⟩

/-- The complete local geometric-sum identity for the actual quadratic
field and its selected complex character, at every rational prime and every
nonnegative exponent.  All local arithmetic inputs are proved internally. -/
theorem rationalQuadraticAlgebra_idealNormPrimePowerGeometricSum
    (D p k : ℕ) (hD : PositiveFundamentalDiscriminant D) (hp : Nat.Prime p) :
    let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
      ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
    (Nat.card {I : Ideal (NumberField.RingOfIntegers
      (rationalQuadraticAlgebra (D : ℤ))) // Ideal.absNorm I = p ^ k} : ℂ) =
      ∑ j ∈ Finset.range (k + 1),
        kroneckerCharacterAtPositiveFundamentalDiscriminantC D hD p ^ j := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  let _ : Fact (Nat.Prime p) := ⟨hp⟩
  let _ : NeZero D := ⟨by have := hD.1; omega⟩
  dsimp only
  by_cases hpD : p ∣ D
  · exact rationalQuadraticAlgebra_idealNormPrimePowerGeometricSum_of_prime_dvd_discriminant
      D p k hD hp hpD
  · have hvalues := selectedCharacter_unramified_prime_values_iff_ideal_exists D p hD hp hpD
    dsimp only at hvalues
    have hcases := rationalQuadraticAlgebra_unramified_primeIdeal_norm_dichotomy D p hD hp hpD
    dsimp only at hcases
    rcases hcases with ⟨P, _, _, hPnorm, hunique⟩ |
      ⟨P, Q, hPQ, _, _, _, _, hPnorm, hQnorm, hexhaust⟩
    · have hnone : ¬ ∃ I : Ideal (NumberField.RingOfIntegers
          (rationalQuadraticAlgebra (D : ℤ))), Ideal.absNorm I = p := by
        rintro ⟨I, hI⟩
        obtain ⟨j, hj, _⟩ :=
          ideal_eq_primePow_of_absNorm_eq_primePow_of_uniquePrimeOver_norm_sq
            (rationalQuadraticAlgebra (D : ℤ)) p 1 hp P hPnorm hunique
              (by simpa using hI)
        omega
      exact idealNormPrimePowerGeometricSum_of_uniquePrimeOver_of_apply_eq_neg_one
        (rationalQuadraticAlgebra (D : ℤ)) p k hp
        (kroneckerCharacterAtPositiveFundamentalDiscriminantC D hD)
        P hPnorm hunique (hvalues.2.mpr hnone)
    · exact idealNormPrimePowerGeometricSum_of_twoPrimesOver_of_apply_eq_one
        (rationalQuadraticAlgebra (D : ℤ)) p k hp
        (kroneckerCharacterAtPositiveFundamentalDiscriminantC D hD)
        P Q hPnorm hQnorm hPQ hexhaust (hvalues.1.mpr ⟨P, hPnorm⟩)

end

end PellPaper
