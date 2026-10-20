import Pell.QuadraticFormIdealBasis

/-!
# Integer lattice equivalence from actual wide ideal-class equality

Equality in the actual ideal class group supplies nonzero integral scalars
`x,y` with `(x) I = (y) J`.  Multiplication by a nonzero scalar identifies an
ideal with its scaled ideal.  Composing these identifications produces a
linear equivalence `e : I ≃ₗ[ℤ] J` satisfying `y * e(z) = x * z`.

In particular, equal wide classes of two primitive form ideals provide this
equivalence with no assumed lattice equality, basis determinant, or principal
scalar in the fraction field.  This module does not yet identify the proper
form classes in a fibre.
-/

namespace PellPaper
namespace IntegralBinaryQuadraticForm

noncomputable section

private def idealPrincipalScaleLinearMap {A : Type*} [CommRing A]
    (I : Ideal A) (x : A) : I →ₗ[A] (Ideal.span {x} * I) where
  toFun z := ⟨x * z.1, Ideal.mem_span_singleton_mul.mpr ⟨z.1, z.2, rfl⟩⟩
  map_add' z w := by
    apply Subtype.ext
    exact mul_add x z.1 w.1
  map_smul' a z := by
    apply Subtype.ext
    change x * (a * z.1) = a * (x * z.1)
    ring

/-- Multiplication by a nonzero scalar identifies an integral ideal with its
principal multiple as modules over the original domain. -/
def idealPrincipalScaleLinearEquiv {A : Type*} [CommRing A] [IsDomain A]
    (I : Ideal A) (x : A) (hx : x ≠ 0) : I ≃ₗ[A] (Ideal.span {x} * I) :=
  LinearEquiv.ofBijective (idealPrincipalScaleLinearMap I x) (by
    constructor
    · intro z w hzw
      apply Subtype.ext
      exact mul_left_cancel₀ hx (congrArg Subtype.val hzw)
    · intro z
      obtain ⟨w, hw, hxw⟩ := Ideal.mem_span_singleton_mul.mp z.2
      exact ⟨⟨w, hw⟩, Subtype.ext hxw⟩)

@[simp]
theorem coe_idealPrincipalScaleLinearEquiv {A : Type*} [CommRing A] [IsDomain A]
    (I : Ideal A) (x : A) (hx : x ≠ 0) (z : I) :
    (idealPrincipalScaleLinearEquiv I x hx z : A) = x * z.1 := rfl

/-- An actual principal scaling equality gives a compatible linear
equivalence of the original integral ideals. -/
theorem exists_idealLinearEquiv_of_principalScale
    {A : Type*} [CommRing A] [IsDomain A]
    (I J : Ideal A) (x y : A) (hx : x ≠ 0) (hy : y ≠ 0)
    (hscale : Ideal.span {x} * I = Ideal.span {y} * J) :
    ∃ e : I ≃ₗ[A] J, ∀ z : I, y * (e z : A) = x * z.1 := by
  let ex := idealPrincipalScaleLinearEquiv I x hx
  let ey := idealPrincipalScaleLinearEquiv J y hy
  let ec := LinearEquiv.ofEq (Ideal.span {x} * I) (Ideal.span {y} * J) hscale
  refine ⟨(ex.trans ec).trans ey.symm, ?_⟩
  intro z
  change y * (ey.symm (ec (ex z)) : A) = x * z.1
  calc
    y * (ey.symm (ec (ex z)) : A) = (ey (ey.symm (ec (ex z))) : A) := rfl
    _ = (ec (ex z) : A) := congrArg Subtype.val (ey.apply_symm_apply _)
    _ = x * z.1 := rfl

/-- Equality in the actual ideal class group yields nonzero integral scalars
and a compatible module equivalence of the two integral ideals. -/
theorem exists_principalScaleLinearEquiv_of_idealClass_eq
    {A : Type*} [CommRing A] [IsDedekindDomain A]
    (I J : Ideal A) (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (hclass : idealClassOfNonzeroIdeal I hI = idealClassOfNonzeroIdeal J hJ) :
    ∃ x y : A, x ≠ 0 ∧ y ≠ 0 ∧
      ∃ e : I ≃ₗ[A] J, ∀ z : I, y * (e z : A) = x * z.1 := by
  unfold idealClassOfNonzeroIdeal at hclass
  obtain ⟨x, y, hx, hy, hscale⟩ := ClassGroup.mk0_eq_mk0_iff.mp hclass
  exact ⟨x, y, hx, hy, exists_idealLinearEquiv_of_principalScale I J x y hx hy hscale⟩

local instance rationalQuadraticAlgebra_wideClassScalingEquiv_numberField_instance (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    NumberField (rationalQuadraticAlgebra D) :=
  rationalQuadraticAlgebra_numberField D

/-- The canonical attached wide-class equality of primitive forms at a
positive fundamental discriminant yields an integer linear equivalence of
their actual ideals, compatible with two nonzero integral scaling factors. -/
theorem exists_formAssociatedIdeal_integerLinearEquiv_of_wideClass_eq
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D)
    (Q R : PrimitiveBinaryQuadraticForms (D : ℤ))
    (hclass : formAssociatedIdealClassAtPositiveFundamentalDiscriminant D hD Q =
      formAssociatedIdealClassAtPositiveFundamentalDiscriminant D hD R) :
    let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
      ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
    ∃ x y : NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ)),
      x ≠ 0 ∧ y ≠ 0 ∧
      ∃ e : formAssociatedIdeal (D : ℤ) Q.1 Q.2.2 ≃ₗ[ℤ]
          formAssociatedIdeal (D : ℤ) R.1 R.2.2,
        ∀ z : formAssociatedIdeal (D : ℤ) Q.1 Q.2.2,
          y * (e z : NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))) =
            x * z.1 := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  dsimp only
  have hQnonzero := formAssociatedIdeal_ne_bot_of_a_ne_zero (D : ℤ) Q.1 Q.2.2
    (leadingCoefficient_ne_zero_of_positiveFundamentalDiscriminant D hD Q)
  have hRnonzero := formAssociatedIdeal_ne_bot_of_a_ne_zero (D : ℤ) R.1 R.2.2
    (leadingCoefficient_ne_zero_of_positiveFundamentalDiscriminant D hD R)
  have hclass' : idealClassOfNonzeroIdeal (formAssociatedIdeal (D : ℤ) Q.1 Q.2.2) hQnonzero =
      idealClassOfNonzeroIdeal (formAssociatedIdeal (D : ℤ) R.1 R.2.2) hRnonzero := hclass
  obtain ⟨x, y, hx, hy, e, he⟩ := exists_principalScaleLinearEquiv_of_idealClass_eq
    _ _ hQnonzero hRnonzero hclass'
  exact ⟨x, y, hx, hy, e.restrictScalars ℤ, he⟩

end
end IntegralBinaryQuadraticForm
end PellPaper
