import Pell.QuadraticKroneckerCharacterOddValues
import Pell.QuadraticIdealNormResidueSquare

/-!
# The selected character detects norm-prime ideals at odd unramified primes

This module connects the selected complex character to actual ideals:
at an odd prime not dividing the positive fundamental discriminant,
`chi(p)=1` is equivalent to the existence of an ideal of norm `p`, and
`chi(p)=-1` is equivalent to its nonexistence. The prime-two case and
higher-prime-power counts are separate.
-/

namespace PellPaper

open NumberTheorySymbols

noncomputable section

local instance rationalQuadraticAlgebra_oddPrimeCharacter_numberField_instance (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    NumberField (rationalQuadraticAlgebra D) :=
  rationalQuadraticAlgebra_numberField D

private theorem isSquare_intCast_iff_exists_sq_mod (D : ℤ) (p : ℕ) :
    IsSquare (D : ZMod p) ↔ ∃ r : ℤ, r ^ 2 ≡ D [ZMOD (p : ℤ)] := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨r, hr⟩ := ZMod.intCast_surjective x
    refine ⟨r, (ZMod.intCast_eq_intCast_iff (r ^ 2) D p).mp ?_⟩
    simpa only [Int.cast_pow, pow_two, Int.cast_mul, hr] using hx.symm
  · rintro ⟨r, hr⟩
    refine ⟨(r : ZMod p), ?_⟩
    have h := (ZMod.intCast_eq_intCast_iff (r ^ 2) D p).mpr hr
    simpa only [Int.cast_pow, pow_two, Int.cast_mul] using h.symm

private theorem selectedCharacter_oddPrime_eq_legendre
    (D p : ℕ) (hD : PositiveFundamentalDiscriminant D)
    (hp : Nat.Prime p) (hp2 : p ≠ 2) (hpD : ¬ p ∣ D) :
    let _ : Fact (Nat.Prime p) := ⟨hp⟩
    kroneckerCharacterAtPositiveFundamentalDiscriminant D hD p = legendreSym p (D : ℤ) := by
  let _ : Fact (Nat.Prime p) := ⟨hp⟩
  rw [kroneckerCharacterAtPositiveFundamentalDiscriminant_apply_eq_jacobi_of_odd_coprime
    D p hD (hp.odd_of_ne_two hp2) (hp.coprime_iff_not_dvd.mpr hpD)]
  exact (jacobiSym.legendreSym.to_jacobiSym p (D : ℤ)).symm

/-- The selected complex character is one precisely when an actual norm-p
ideal exists, at an odd prime away from the discriminant. -/
theorem kroneckerCharacterC_eq_one_iff_exists_ideal_absNorm_eq_odd_prime
    (D p : ℕ) (hD : PositiveFundamentalDiscriminant D)
    (hp : Nat.Prime p) (hp2 : p ≠ 2) (hpD : ¬ p ∣ D) :
    let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
      ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
    kroneckerCharacterAtPositiveFundamentalDiscriminantC D hD p = 1 ↔
      ∃ I : Ideal (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))),
        Ideal.absNorm I = p := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  let _ : Fact (Nat.Prime p) := ⟨hp⟩
  dsimp only
  have hnonzero : ((D : ℤ) : ZMod p) ≠ 0 := by
    simpa using (show (D : ZMod p) ≠ 0 from
      fun h => hpD ((ZMod.natCast_eq_zero_iff D p).mp h))
  have hcast : kroneckerCharacterAtPositiveFundamentalDiscriminantC D hD p =
      (legendreSym p (D : ℤ) : ℂ) := by
    simp [kroneckerCharacterAtPositiveFundamentalDiscriminantC,
      selectedCharacter_oddPrime_eq_legendre D p hD hp hp2 hpD]
  rw [hcast]
  have hcastone : (legendreSym p (D : ℤ) : ℂ) = 1 ↔ legendreSym p (D : ℤ) = 1 := by
    exact_mod_cast (Iff.rfl : legendreSym p (D : ℤ) = 1 ↔ legendreSym p (D : ℤ) = 1)
  rw [hcastone, legendreSym.eq_one_iff p hnonzero,
    isSquare_intCast_iff_exists_sq_mod]
  exact (rationalQuadraticAlgebra_exists_ideal_absNorm_eq_prime_iff_sq_mod
    D p hD hp hp2 hpD).symm

/-- The selected complex character is minus one precisely when the actual
norm-p ideal fibre is empty, at an odd prime away from the discriminant. -/
theorem kroneckerCharacterC_eq_neg_one_iff_not_exists_ideal_absNorm_eq_odd_prime
    (D p : ℕ) (hD : PositiveFundamentalDiscriminant D)
    (hp : Nat.Prime p) (hp2 : p ≠ 2) (hpD : ¬ p ∣ D) :
    let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
      ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
    kroneckerCharacterAtPositiveFundamentalDiscriminantC D hD p = -1 ↔
      ¬ ∃ I : Ideal (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))),
        Ideal.absNorm I = p := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  let _ : Fact (Nat.Prime p) := ⟨hp⟩
  dsimp only
  have hcast : kroneckerCharacterAtPositiveFundamentalDiscriminantC D hD p =
      (legendreSym p (D : ℤ) : ℂ) := by
    simp [kroneckerCharacterAtPositiveFundamentalDiscriminantC,
      selectedCharacter_oddPrime_eq_legendre D p hD hp hp2 hpD]
  rw [hcast]
  have hcastneg : (legendreSym p (D : ℤ) : ℂ) = -1 ↔ legendreSym p (D : ℤ) = -1 := by
    exact_mod_cast (Iff.rfl : legendreSym p (D : ℤ) = -1 ↔ legendreSym p (D : ℤ) = -1)
  rw [hcastneg, legendreSym.eq_neg_one_iff p, isSquare_intCast_iff_exists_sq_mod]
  exact not_congr (rationalQuadraticAlgebra_exists_ideal_absNorm_eq_prime_iff_sq_mod
    D p hD hp hp2 hpD).symm

end
end PellPaper
