import Pell.QuadraticFormIdealAttachment
import Mathlib.RingTheory.ClassGroup.Basic

/-!
# Nonzero form ideals as actual ideal classes

This module makes only the first literal map in the form--ideal dictionary.
For a primitive form at a positive fundamental discriminant, its attached
nonzero integral ideal determines an element of Mathlib's actual ideal class
group of the concrete quadratic algebra's ring of integers.

The compatibility result is deliberately conditional on an explicit equality
of scaled integral ideals.  It does not use proper transformations, does not
assert that the map descends to `ProperFormClass`, and does not identify the
form quotient with the ideal class group.
-/

namespace PellPaper

namespace IntegralBinaryQuadraticForm

noncomputable section

local instance rationalQuadraticAlgebra_formIdealClass_numberField_instance (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    NumberField (rationalQuadraticAlgebra D) :=
  rationalQuadraticAlgebra_numberField D

/-- Send a nonzero integral ideal of a Dedekind domain to its Mathlib ideal
class.  The nonzero hypothesis is exactly the prerequisite of `ClassGroup.mk0`. -/
noncomputable def idealClassOfNonzeroIdeal
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    (I : Ideal R) (hI : I ≠ ⊥) : ClassGroup R :=
  ClassGroup.mk0 ⟨I, mem_nonZeroDivisors_of_ne_zero (by simpa using hI)⟩

/-- An equality after multiplying two nonzero integral ideals by nonzero
principal factors gives equality of their ideal classes.  This is a direct
specialization of Mathlib's `ClassGroup.mk0_eq_mk0_iff`. -/
theorem idealClassOfNonzeroIdeal_eq_of_principalScale
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    (I J : Ideal R) (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (x y : R) (hx : x ≠ 0) (hy : y ≠ 0)
    (hscale : Ideal.span {x} * I = Ideal.span {y} * J) :
    idealClassOfNonzeroIdeal I hI = idealClassOfNonzeroIdeal J hJ := by
  unfold idealClassOfNonzeroIdeal
  exact ClassGroup.mk0_eq_mk0_iff.mpr ⟨x, y, hx, hy, hscale⟩

/-- The actual ideal-class representative attached to a form whose leading
coefficient is nonzero. -/
noncomputable def formAssociatedIdealClass
    (D : ℤ) (Q : IntegralBinaryQuadraticForm) (hQ : Q.discriminant = D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] (ha : Q.a ≠ 0) :
    ClassGroup (NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) :=
  idealClassOfNonzeroIdeal (formAssociatedIdeal D Q hQ)
    (formAssociatedIdeal_ne_bot_of_a_ne_zero D Q hQ ha)

/-- The attached ideals of two forms have the same actual ideal class whenever
an explicit nonzero principal scaling equality between them is supplied.
No proper-transform compatibility is asserted here. -/
theorem formAssociatedIdealClass_eq_of_principalScale
    (D : ℤ) (Q R : IntegralBinaryQuadraticForm)
    (hQ : Q.discriminant = D) (hR : R.discriminant = D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)]
    (haQ : Q.a ≠ 0) (haR : R.a ≠ 0)
    (x y : NumberField.RingOfIntegers (rationalQuadraticAlgebra D))
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hscale : Ideal.span {x} * formAssociatedIdeal D Q hQ =
      Ideal.span {y} * formAssociatedIdeal D R hR) :
    formAssociatedIdealClass D Q hQ haQ =
      formAssociatedIdealClass D R hR haR := by
  exact idealClassOfNonzeroIdeal_eq_of_principalScale
    (formAssociatedIdeal D Q hQ) (formAssociatedIdeal D R hR)
    (formAssociatedIdeal_ne_bot_of_a_ne_zero D Q hQ haQ)
    (formAssociatedIdeal_ne_bot_of_a_ne_zero D R hR haR)
    x y hx hy hscale

/-- A primitive form at a positive fundamental discriminant has a canonical
image in the actual ideal class group of the associated concrete quadratic
algebra.  This is a map on forms, not on proper-form classes. -/
noncomputable def formAssociatedIdealClassAtPositiveFundamentalDiscriminant
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D)
    (Q : PrimitiveBinaryQuadraticForms (D : ℤ)) :
    let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
      ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
    ClassGroup (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))) := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  exact formAssociatedIdealClass (D : ℤ) Q.1 Q.2.2
    (leadingCoefficient_ne_zero_of_positiveFundamentalDiscriminant D hD Q)

end

end IntegralBinaryQuadraticForm

end PellPaper
