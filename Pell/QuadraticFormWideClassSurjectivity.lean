import Pell.QuadraticIdealNormalizedNormClassRepresentative
import Pell.QuadraticFormWideClassFibreCard

/-!
# Surjectivity and the lower class-number comparison

Every actual wide ideal class has a nonzero integral ideal representative.
The normalized norm-form construction realizes that representative by a
primitive form, so the literal proper-form quotient maps surjectively onto
the actual wide class group. Together with the proved finite fibres, this
gives the full comparison h(D) <= H(D) <= 2*h(D).

This is discriminant-indexed; classification of all real quadratic fields
by these concrete representatives and analytic average bounds are separate.
-/

namespace PellPaper
namespace IntegralBinaryQuadraticForm

noncomputable section

local instance rationalQuadraticAlgebra_wideClassSurjectivity_numberField_instance (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    NumberField (rationalQuadraticAlgebra D) :=
  rationalQuadraticAlgebra_numberField D

/-- Every actual wide ideal class is the image of a proper form class. -/
theorem properFormClassWideClassMap_surjective
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) :
    Function.Surjective (properFormClassWideClassMapAtPositiveFundamentalDiscriminant D hD) := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  intro c
  obtain ⟨I, hI⟩ := ClassGroup.mk0_surjective c
  have hI0 : I.1 ≠ ⊥ := by
    simpa using (mem_nonZeroDivisors_iff_ne_zero.mp I.2)
  obtain ⟨Q, hQ⟩ := exists_formAssociatedIdealClass_eq_of_nonzeroIdeal D hD I.1 hI0
  refine ⟨PrimitiveBinaryQuadraticForms.toProperFormClass Q, ?_⟩
  change formAssociatedIdealClassAtPositiveFundamentalDiscriminant D hD Q = c
  rw [hQ]
  exact hI

/-- The ordinary ideal class number is at most the genuine proper-form
class count; the domain is proved finite before cardinality comparison. -/
theorem classNumber_le_properFormClass_card
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) :
    rationalQuadraticAlgebraClassNumberAtPositiveFundamentalDiscriminant D hD ≤
      Nat.card (ProperFormClass (D : ℤ)) := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  let _ := finite_properFormClass_of_positiveFundamentalDiscriminant D hD
  have hcard := Nat.card_le_card_of_surjective
    (properFormClassWideClassMapAtPositiveFundamentalDiscriminant D hD)
    (properFormClassWideClassMap_surjective D hD)
  simpa only [rationalQuadraticAlgebraClassNumberAtPositiveFundamentalDiscriminant,
    rationalQuadraticAlgebraClassNumber, NumberField.classNumber,
    Nat.card_eq_fintype_card] using hcard

/-- The genuine finite proper-form class count is positive. -/
theorem properFormClass_card_pos_of_positiveFundamentalDiscriminant
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) :
    0 < Nat.card (ProperFormClass (D : ℤ)) :=
  lt_of_lt_of_le (rationalQuadraticAlgebraClassNumberAtPositiveFundamentalDiscriminant_pos D hD)
    (classNumber_le_properFormClass_card D hD)

end
end IntegralBinaryQuadraticForm
end PellPaper
