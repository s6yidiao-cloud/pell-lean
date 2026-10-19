import Pell.QuadraticFieldInvariantTransport

/-!
# Actual isomorphism classes of real quadratic number fields

A bundled field has rational degree two and admits a real embedding. The
embedding is not marked data in the equivalence relation: two objects are
equivalent exactly when their fields are rational-algebra-equivalent.

Carriers here live in Type; the separate presentation theorem for fields
in arbitrary universes supplies small representatives. This module neither
assumes a discriminant classification nor defines a class-average model.
-/

namespace PellPaper

noncomputable section

/-- An actual degree-two number field which admits a real embedding. -/
structure RealQuadraticField where
  carrier : Type
  [field : Field carrier]
  [numberField : NumberField carrier]
  degree_two : Module.finrank ℚ carrier = 2
  has_real_embedding : Nonempty (carrier →+* ℝ)

attribute [instance] RealQuadraticField.field RealQuadraticField.numberField

instance : CoeSort RealQuadraticField Type := ⟨RealQuadraticField.carrier⟩

/-- Bundle an actual real quadratic field without choosing a marked embedding. -/
def RealQuadraticField.of (K : Type) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (hreal : Nonempty (K →+* ℝ)) : RealQuadraticField :=
  { carrier := K, degree_two := hK, has_real_embedding := hreal }

/-- Ordinary rational field isomorphism; embeddings and integral bases are
not part of the equivalence data. -/
def realQuadraticFieldSetoid : Setoid RealQuadraticField where
  r K L := Nonempty (K ≃ₐ[ℚ] L)
  iseqv :=
    { refl := fun _K => ⟨AlgEquiv.refl⟩
      symm := fun ⟨e⟩ => ⟨e.symm⟩
      trans := fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩ }

/-- Actual real quadratic number fields up to rational field isomorphism. -/
def RealQuadraticFieldClass := Quotient realQuadraticFieldSetoid

/-- The isomorphism class of a bundled actual real quadratic field. -/
def RealQuadraticField.toClass (K : RealQuadraticField) : RealQuadraticFieldClass :=
  Quotient.mk realQuadraticFieldSetoid K

/-- Class equality means an actual rational algebra equivalence. -/
theorem realQuadraticField_toClass_eq_iff (K L : RealQuadraticField) :
    K.toClass = L.toClass ↔ Nonempty (K ≃ₐ[ℚ] L) := Quotient.eq

/-- The actual integer field discriminant, well-defined on isomorphism classes. -/
def realQuadraticFieldClassDiscriminant : RealQuadraticFieldClass → ℤ :=
  Quotient.lift (fun K : RealQuadraticField => NumberField.discr K) (by
    intro K L h
    obtain ⟨e⟩ := h
    exact NumberField.discr_eq_discr_of_algEquiv K e)

/-- The actual ordinary ideal class number, well-defined on field classes. -/
def realQuadraticFieldClassNumber : RealQuadraticFieldClass → ℕ :=
  Quotient.lift (fun K : RealQuadraticField => NumberField.classNumber K) (by
    intro K L h
    obtain ⟨e⟩ := h
    exact numberFieldClassNumber_eq_of_algEquiv K L e)

theorem realQuadraticFieldClassDiscriminant_toClass (K : RealQuadraticField) :
    realQuadraticFieldClassDiscriminant K.toClass = NumberField.discr K := rfl

theorem realQuadraticFieldClassNumber_toClass (K : RealQuadraticField) :
    realQuadraticFieldClassNumber K.toClass = NumberField.classNumber K := rfl

end
end PellPaper
