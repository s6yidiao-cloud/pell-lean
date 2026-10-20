import Pell.QuadraticAlgebraFieldDiscriminantEquality
import Pell.QuadraticAlgebraClassNumber

/-!
# Class-number and discriminant transport for actual field presentations

An actual rational algebra equivalence transports rings of integers and
their class groups, so the ordinary class number is invariant. A positive
fundamental presentation identifies the field discriminant with its index,
which also proves uniqueness of that index.

These statements do not supply the existence of a fundamental presentation
or define a sum over all real quadratic fields; those are separate steps.
-/

namespace PellPaper

noncomputable section

local instance quadraticFieldInvariantTransport_numberField (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    NumberField (rationalQuadraticAlgebra D) := rationalQuadraticAlgebra_numberField D

/-- An actual rational algebra equivalence preserves the ordinary ideal
class number, via its induced ring-of-integers and class-group equivalences. -/
theorem numberFieldClassNumber_eq_of_algEquiv
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    (e : K ≃ₐ[ℚ] L) : NumberField.classNumber K = NumberField.classNumber L := by
  let f : NumberField.RingOfIntegers K ≃+* NumberField.RingOfIntegers L :=
    (e.restrictScalars ℤ).mapIntegralClosure.toRingEquiv
  exact Fintype.card_congr (ClassGroup.mulEquiv f).toEquiv

/-- A fundamental quadratic presentation identifies the actual field
discriminant with the chosen positive fundamental index. -/
theorem numberField_discr_eq_of_quadraticFundamentalPresentation
    (K : Type*) [Field K] [NumberField K]
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D)
    (e : K ≃ₐ[ℚ] rationalQuadraticAlgebra (D : ℤ)) :
    NumberField.discr K = (D : ℤ) := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  calc
    NumberField.discr K = NumberField.discr (rationalQuadraticAlgebra (D : ℤ)) :=
      NumberField.discr_eq_discr_of_algEquiv K e
    _ = (D : ℤ) := rationalQuadraticAlgebraFieldDiscriminantAtPositiveFundamentalDiscriminant_eq D hD

/-- The actual ordinary class number in any fundamental presentation is
the one used by the genuine discriminant-indexed model. -/
theorem numberField_classNumber_eq_of_quadraticFundamentalPresentation
    (K : Type*) [Field K] [NumberField K]
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D)
    (e : K ≃ₐ[ℚ] rationalQuadraticAlgebra (D : ℤ)) :
    NumberField.classNumber K =
      rationalQuadraticAlgebraClassNumberAtPositiveFundamentalDiscriminant D hD := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  exact numberFieldClassNumber_eq_of_algEquiv K (rationalQuadraticAlgebra (D : ℤ)) e

/-- Two positive fundamental presentations of the same actual number
field have the same index, by invariance of its actual field discriminant. -/
theorem positiveFundamentalIndex_unique_for_numberField
    (K : Type*) [Field K] [NumberField K]
    (D E : ℕ) (hD : PositiveFundamentalDiscriminant D) (hE : PositiveFundamentalDiscriminant E)
    (eD : K ≃ₐ[ℚ] rationalQuadraticAlgebra (D : ℤ))
    (eE : K ≃ₐ[ℚ] rationalQuadraticAlgebra (E : ℤ)) : D = E := by
  have h := (numberField_discr_eq_of_quadraticFundamentalPresentation K D hD eD).symm.trans
    (numberField_discr_eq_of_quadraticFundamentalPresentation K E hE eE)
  exact_mod_cast h

/-- Equivalent concrete fields at positive fundamental indices have equal
indices; this is injectivity of the actual field parametrization. -/
theorem positiveFundamentalDiscriminant_eq_of_quadraticAlgebra_algEquiv
    (D E : ℕ) (hD : PositiveFundamentalDiscriminant D) (hE : PositiveFundamentalDiscriminant E)
    (e : rationalQuadraticAlgebra (D : ℤ) ≃ₐ[ℚ] rationalQuadraticAlgebra (E : ℤ)) : D = E := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  exact positiveFundamentalIndex_unique_for_numberField (rationalQuadraticAlgebra (D : ℤ))
    D E hD hE (AlgEquiv.refl) e

end
end PellPaper
