import Pell.QuadraticIdealNormDivisorBound

/-!
# Transport of fixed ideal-norm fibres across number-field equivalences

A rational algebra equivalence restricts to an equivalence of rings of
integers.  Mapping ideals through this ring equivalence preserves the
cardinality of the quotient ring, hence the absolute ideal norm.  It therefore
induces an equivalence on every fixed-norm ideal fibre.

This supplies the invariant transport needed in the manuscript when a
quadratic form has discriminant `w*s^2` but the ideal count is most naturally
proved at the positive fundamental index of the squarefree radicand `w`.
No representation or unit-orbit assertion is made here.
-/

namespace PellPaper

open NumberField

noncomputable section

local instance rationalQuadraticAlgebra_idealNormTransport_numberField_instance (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    NumberField (rationalQuadraticAlgebra D) :=
  rationalQuadraticAlgebra_numberField D

/-- The ring-of-integers equivalence induced by a rational algebra
equivalence of number fields. -/
noncomputable def ringOfIntegersRingEquivOfAlgEquiv
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    (e : K ≃ₐ[ℚ] L) :
    NumberField.RingOfIntegers K ≃+* NumberField.RingOfIntegers L :=
  NumberField.RingOfIntegers.mapRingEquiv e.toRingEquiv

/-- Mapping an integral ideal across a number-field equivalence preserves its
absolute norm. -/
theorem absNorm_map_ringOfIntegersRingEquivOfAlgEquiv
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    (e : K ≃ₐ[ℚ] L) (I : Ideal (NumberField.RingOfIntegers K)) :
    Ideal.absNorm
        (I.map (ringOfIntegersRingEquivOfAlgEquiv K L e)) =
      Ideal.absNorm I := by
  simp only [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr
    (Ideal.quotientEquiv I
      (I.map (ringOfIntegersRingEquivOfAlgEquiv K L e))
      (ringOfIntegersRingEquivOfAlgEquiv K L e) rfl).symm.toEquiv

/-- A number-field equivalence induces an equivalence between the integral
ideal fibres of any fixed absolute norm. -/
noncomputable def idealNormFibreEquivOfAlgEquiv
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    (e : K ≃ₐ[ℚ] L) (n : ℕ) :
    {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = n} ≃
      {J : Ideal (NumberField.RingOfIntegers L) // Ideal.absNorm J = n} :=
  Equiv.subtypeEquiv
    ((ringOfIntegersRingEquivOfAlgEquiv K L e).idealComapOrderIso.symm.toEquiv)
    (fun I => by
      change Ideal.absNorm I = n ↔
        Ideal.absNorm (I.map (ringOfIntegersRingEquivOfAlgEquiv K L e)) = n
      rw [absNorm_map_ringOfIntegersRingEquivOfAlgEquiv K L e I])

/-- Fixed absolute-norm ideal fibres have equal cardinality across a rational
algebra equivalence. -/
theorem card_idealNormFibre_eq_of_algEquiv
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    (e : K ≃ₐ[ℚ] L) (n : ℕ) :
    Nat.card {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = n} =
      Nat.card {J : Ideal (NumberField.RingOfIntegers L) // Ideal.absNorm J = n} :=
  Nat.card_congr (idealNormFibreEquivOfAlgEquiv K L e n)

/-- Transporting to a positive fundamental quadratic presentation transfers
the sharp divisor bound for fixed-norm ideal fibres. -/
theorem card_idealNormFibre_le_card_divisors_of_quadraticFundamental_algEquiv
    (K : Type*) [Field K] [NumberField K]
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ))]
    (e : K ≃ₐ[ℚ] rationalQuadraticAlgebra (D : ℤ))
    (n : ℕ) (hn : n ≠ 0) :
    Nat.card {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = n} ≤
      n.divisors.card := by
  calc
    Nat.card {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = n} =
        Nat.card {J : Ideal (NumberField.RingOfIntegers
          (rationalQuadraticAlgebra (D : ℤ))) // Ideal.absNorm J = n} :=
      card_idealNormFibre_eq_of_algEquiv K (rationalQuadraticAlgebra (D : ℤ)) e n
    _ ≤ n.divisors.card := by
      simpa only using
        rationalQuadraticAlgebra_card_idealNormFibre_le_card_divisors D hD n hn

end
end PellPaper
