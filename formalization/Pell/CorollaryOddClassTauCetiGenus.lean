import Pell.CorollaryOddClassOrdinaryGenus
import Pell.QuadraticAlgebraFieldDiscriminantEquality
import TauCeti.NumberTheory.Multiquadratic.Quadratic.TwoRank
import TauCeti.NumberTheory.NumberField.ClassGroupElementaryTwoQuotient

/-!
# TauCeti genus theory for the ordinary real-quadratic class number

This module adapts TauCeti's complete quadratic genus theory to the concrete
quadratic field already used by the Pell project.  Pell's proved field
discriminant equality identifies the ramified rational primes with the prime
factors of the positive fundamental discriminant.  TauCeti then gives the
ordinary class-group two-rank lower bound, and its elementary-two-quotient
theorem converts that bound into divisibility of the actual Mathlib class
number.

The loss of two in the exponent is the uniform real-quadratic wide-class
bound.  It is exactly the input packaged by
`OrdinaryClassNumberGenusDivisibility` and costs only an absolute factor four
in the downstream odd-class estimate.
-/

namespace PellPaper

noncomputable section

open scoped ArithmeticFunction.omega NumberField

/-- TauCeti's quadratic genus theory supplies the ordinary class-number
divisibility family required by the odd-class-number pipeline. -/
theorem ordinaryClassNumberGenusDivisibility_tauceti_proved :
    OrdinaryClassNumberGenusDivisibility := by
  intro D hD
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  let _ : NumberField (rationalQuadraticAlgebra (D : ℤ)) :=
    rationalQuadraticAlgebra_numberField (D : ℤ)
  have hdisc :
      NumberField.discr (rationalQuadraticAlgebra (D : ℤ)) = (D : ℤ) := by
    change rationalQuadraticAlgebraFieldDiscriminantAtPositiveFundamentalDiscriminant D hD =
      (D : ℤ)
    exact rationalQuadraticAlgebraFieldDiscriminantAtPositiveFundamentalDiscriminant_eq D hD
  have hD0 : D ≠ 0 := (positive_of_positiveFundamentalDiscriminant hD).ne'
  have hram :
      NumberField.ramifiedPrimes (rationalQuadraticAlgebra (D : ℤ)) =
        (D.primeFactors : Set ℕ) := by
    ext p
    constructor
    · intro hp
      have hpprime := NumberField.prime_of_mem_ramifiedPrimes hp
      have hpdivz :=
        (NumberField.mem_ramifiedPrimes_iff_dvd_discr hpprime).mp hp
      rw [hdisc] at hpdivz
      exact Finset.mem_coe.mpr (Nat.mem_primeFactors.mpr
        ⟨hpprime, Int.natCast_dvd_natCast.mp hpdivz, hD0⟩)
    · intro hp
      have hpfin := Nat.mem_primeFactors.mp (Finset.mem_coe.mp hp)
      apply (NumberField.mem_ramifiedPrimes_iff_dvd_discr hpfin.1).mpr
      rw [hdisc]
      exact Int.natCast_dvd_natCast.mpr hpfin.2.1
  have hncard :
      (NumberField.ramifiedPrimes (rationalQuadraticAlgebra (D : ℤ))).ncard = ω D := by
    rw [hram, Set.ncard_coe_finset, ArithmeticFunction.cardDistinctFactors_apply]
    exact List.card_toFinset D.primeFactorsList
  have hrank :
      ω D - 2 ≤
        TauCeti.ClassGroup.twoRank
          (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))) := by
    rw [← hncard]
    exact TauCeti.Multiquadratic.ncard_ramifiedPrimes_sub_two_le_twoRank
      (rationalQuadraticAlgebra_finrank_eq_two (D : ℤ))
  have hpow :
      2 ^ (ω D - 2) ∣
        2 ^ TauCeti.ClassGroup.twoRank
          (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))) :=
    Nat.pow_dvd_pow 2 hrank
  unfold rationalQuadraticAlgebraClassNumberAtPositiveFundamentalDiscriminant
  unfold rationalQuadraticAlgebraClassNumber
  exact hpow.trans
    (NumberField.two_pow_classGroupTwoRank_dvd_classNumber
      (rationalQuadraticAlgebra (D : ℤ)))

/-- The proved TauCeti divisibility supplies the constant-four pointwise
genus interface consumed by the remaining odd-class-number argument. -/
theorem oddClassGenusPointwiseBound_four_tauceti_proved :
    OddClassGenusPointwiseBound 4 :=
  oddClassGenusPointwiseBound_four_of_ordinaryClassNumberGenusDivisibility
    ordinaryClassNumberGenusDivisibility_tauceti_proved

end

end PellPaper
