import Pell.QuadraticFormIdealClassMap

/-!
# The other sign choice with the same attached ideal

The form `[a,b,c]` and its partner `[-a,b,-c]` attach to the same actual
ideal. This is the sign convention for a possible two-element fibre of the
wide-class map. No assertion that all fibres have at most two elements, or
that these two forms are properly inequivalent, is made here.
-/

namespace PellPaper
namespace IntegralBinaryQuadraticForm

/-- Reverse the leading and trailing signs while preserving the middle coefficient. -/
def wideClassPartner (Q : IntegralBinaryQuadraticForm) : IntegralBinaryQuadraticForm :=
  ⟨-Q.a, Q.b, -Q.c⟩

@[simp]
theorem wideClassPartner_involutive (Q : IntegralBinaryQuadraticForm) :
    Q.wideClassPartner.wideClassPartner = Q := by
  ext <;> simp [wideClassPartner]

@[simp]
theorem discriminant_wideClassPartner (Q : IntegralBinaryQuadraticForm) :
    Q.wideClassPartner.discriminant = Q.discriminant := by
  simp [wideClassPartner, discriminant]

@[simp]
theorem primitive_wideClassPartner_iff (Q : IntegralBinaryQuadraticForm) :
    Q.wideClassPartner.Primitive ↔ Q.Primitive := by
  simp only [Primitive, wideClassPartner, dvd_neg]

theorem eval_wideClassPartner (Q : IntegralBinaryQuadraticForm) (x y : ℤ) :
    Q.wideClassPartner.eval x y = -Q.eval x (-y) := by
  simp only [wideClassPartner, eval]
  ring

/-- The partner stays in the primitive fixed-discriminant family. -/
def wideClassPartnerAt {D : ℤ} (Q : PrimitiveBinaryQuadraticForms D) :
    PrimitiveBinaryQuadraticForms D :=
  ⟨Q.1.wideClassPartner, (primitive_wideClassPartner_iff Q.1).mpr Q.2.1,
    (discriminant_wideClassPartner Q.1).trans Q.2.2⟩

noncomputable section

local instance rationalQuadraticAlgebra_wideClassPartner_numberField_instance (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    NumberField (rationalQuadraticAlgebra D) :=
  rationalQuadraticAlgebra_numberField D

/-- The partner has literally the same attached ideal, before taking ideal classes. -/
theorem formAssociatedIdeal_wideClassPartner_eq (D : ℤ)
    (Q : IntegralBinaryQuadraticForm) (hQ : Q.discriminant = D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    formAssociatedIdeal D Q.wideClassPartner
        ((discriminant_wideClassPartner Q).trans hQ) =
      formAssociatedIdeal D Q hQ := by
  have hgen : formIdealGenerator D Q.wideClassPartner
      ((discriminant_wideClassPartner Q).trans hQ) = formIdealGenerator D Q hQ := rfl
  simp only [formAssociatedIdeal]
  rw [hgen]
  simp only [wideClassPartner, Int.cast_neg, Ideal.span_insert_neg]

end
end IntegralBinaryQuadraticForm
end PellPaper
