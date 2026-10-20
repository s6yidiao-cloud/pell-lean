import Pell.RealQuadraticFieldIsomorphismClasses
import Pell.RealQuadraticNumberFieldFundamentalPresentation

/-!
# Positive fundamental discriminants classify actual real quadratic fields

The map uses actual quadratic fields, and the target is the quotient of
actual fields by rational algebra equivalence. Surjectivity uses the proved
presentation theorem; injectivity uses invariance of the actual field
discriminant. No field-class counting assumption is supplied.
-/

namespace PellPaper

noncomputable section

local instance fundamentalFieldClass_numberField (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    NumberField (rationalQuadraticAlgebra D) := rationalQuadraticAlgebra_numberField D

/-- The actual real quadratic field associated to a positive fundamental index. -/
def fundamentalRealQuadraticField
    (D : {D : ℕ // PositiveFundamentalDiscriminant D}) : RealQuadraticField := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D.val : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant D.property⟩
  exact RealQuadraticField.of (rationalQuadraticAlgebra (D.val : ℤ))
    (QuadraticAlgebra.finrank_eq_two _ _)
    ⟨(rationalQuadraticAlgebraRealEmbedding (D.val : ℤ) (by positivity)).toRingHom⟩

/-- Send the index to the ordinary, unmarked isomorphism class of its field. -/
def positiveFundamentalToRealQuadraticFieldClass
    (D : {D : ℕ // PositiveFundamentalDiscriminant D}) : RealQuadraticFieldClass :=
  (fundamentalRealQuadraticField D).toClass

theorem positiveFundamentalToRealQuadraticFieldClass_injective :
    Function.Injective positiveFundamentalToRealQuadraticFieldClass := by
  intro D E h
  obtain ⟨e⟩ := (realQuadraticField_toClass_eq_iff
    (fundamentalRealQuadraticField D) (fundamentalRealQuadraticField E)).mp h
  apply Subtype.ext
  exact positiveFundamentalDiscriminant_eq_of_quadraticAlgebra_algEquiv
    D.val E.val D.property E.property e

theorem positiveFundamentalToRealQuadraticFieldClass_surjective :
    Function.Surjective positiveFundamentalToRealQuadraticFieldClass := by
  intro c
  induction c using Quotient.inductionOn with
  | _ K =>
    obtain ⟨σ⟩ := K.has_real_embedding
    obtain ⟨D, hD, ⟨e⟩⟩ :=
      exists_realQuadraticNumberField_positiveFundamental_presentation K K.degree_two σ
    refine ⟨⟨D, hD⟩, ?_⟩
    exact (realQuadraticField_toClass_eq_iff
      (fundamentalRealQuadraticField ⟨D, hD⟩) K).mpr ⟨e.symm⟩

/-- A proved bijection, not a definition of field classes as discriminants. -/
def positiveFundamentalFieldClassEquiv :
    {D : ℕ // PositiveFundamentalDiscriminant D} ≃ RealQuadraticFieldClass :=
  Equiv.ofBijective positiveFundamentalToRealQuadraticFieldClass
    ⟨positiveFundamentalToRealQuadraticFieldClass_injective,
      positiveFundamentalToRealQuadraticFieldClass_surjective⟩

theorem realQuadraticFieldClassDiscriminant_positiveFundamental
    (D : {D : ℕ // PositiveFundamentalDiscriminant D}) :
    realQuadraticFieldClassDiscriminant (positiveFundamentalToRealQuadraticFieldClass D) =
      (D.val : ℤ) := by
  change NumberField.discr (fundamentalRealQuadraticField D) = (D.val : ℤ)
  exact numberField_discr_eq_of_quadraticFundamentalPresentation
    (fundamentalRealQuadraticField D) D.val D.property AlgEquiv.refl

theorem realQuadraticFieldClassNumber_positiveFundamental
    (D : {D : ℕ // PositiveFundamentalDiscriminant D}) :
    realQuadraticFieldClassNumber (positiveFundamentalToRealQuadraticFieldClass D) =
      rationalQuadraticAlgebraClassNumberAtPositiveFundamentalDiscriminant D.val D.property := by
  change NumberField.classNumber (fundamentalRealQuadraticField D) = _
  exact numberField_classNumber_eq_of_quadraticFundamentalPresentation
    (fundamentalRealQuadraticField D) D.val D.property AlgEquiv.refl

end
end PellPaper
