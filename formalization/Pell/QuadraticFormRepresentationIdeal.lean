import Pell.QuadraticFormIdealVectorNorm

/-!
# Integral ideals attached to representations by a primitive quadratic form

For an integral binary quadratic form `Q = [a,b,c]`, the vector
`beta = a*x - theta*y` belongs to the maximal-order ideal `I_Q` and has
algebra norm `a * Q(x,y)`.  This file divides the principal ideal `(beta)` by
`I_Q` inside the Dedekind domain of integers.  If `Q(x,y)=m`, the resulting
integral ideal has absolute norm `|m|`.

Thus the extension-to-the-maximal-order and norm-preservation step in
the manuscript is obtained directly from the already constructed
maximal-order ideal.  No ideal-count, unit-orbit, height-window, or analytic
estimate is asserted here.
-/

namespace PellPaper
namespace IntegralBinaryQuadraticForm

noncomputable section

local instance rationalQuadraticAlgebra_representationIdeal_numberField_instance (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    NumberField (rationalQuadraticAlgebra D) :=
  rationalQuadraticAlgebra_numberField D

private theorem formAssociatedIdeal_dvd_span_formIdealVector
    (D : ℤ) (Q : IntegralBinaryQuadraticForm) (hQ : Q.discriminant = D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] (x y : ℤ) :
    formAssociatedIdeal D Q hQ ∣ Ideal.span {formIdealVector D Q hQ x y} := by
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact formIdealVector_mem D Q hQ x y

/-- The integral quotient ideal `J` determined by `(beta) = I_Q * J`, where
`beta = a*x - theta*y` is the form-ideal vector at `(x,y)`. -/
noncomputable def formRepresentationQuotientIdeal
    (D : ℤ) (Q : IntegralBinaryQuadraticForm) (hQ : Q.discriminant = D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] (x y : ℤ) :
    Ideal (NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) :=
  Classical.choose (formAssociatedIdeal_dvd_span_formIdealVector D Q hQ x y)

/-- The defining integral ideal factorization for a representation vector. -/
theorem formAssociatedIdeal_mul_formRepresentationQuotientIdeal
    (D : ℤ) (Q : IntegralBinaryQuadraticForm) (hQ : Q.discriminant = D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] (x y : ℤ) :
    formAssociatedIdeal D Q hQ * formRepresentationQuotientIdeal D Q hQ x y =
      Ideal.span {formIdealVector D Q hQ x y} := by
  exact (Classical.choose_spec
    (formAssociatedIdeal_dvd_span_formIdealVector D Q hQ x y)).symm

/-- If `Q(x,y)=m` and `Q` is primitive, the quotient ideal has absolute norm
exactly `|m|`.  The only nondegeneracy input is `a != 0`, which follows from
a nonsquare discriminant in the intended application. -/
theorem absNorm_formRepresentationQuotientIdeal_eq_natAbs
    (D : ℤ) (Q : IntegralBinaryQuadraticForm) (hQ : Q.discriminant = D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)]
    (hprim : Q.Primitive) (ha : Q.a ≠ 0) (x y m : ℤ)
    (hm : Q.eval x y = m) :
    Ideal.absNorm (formRepresentationQuotientIdeal D Q hQ x y) = m.natAbs := by
  have hnorm := congrArg Ideal.absNorm
    (formAssociatedIdeal_mul_formRepresentationQuotientIdeal D Q hQ x y)
  rw [map_mul, absNorm_formAssociatedIdeal_eq_natAbs D Q hQ hprim,
    Ideal.absNorm_span_singleton, algebraNorm_formIdealVector D Q hQ x y, hm,
    Int.natAbs_mul] at hnorm
  exact Nat.mul_left_cancel (Int.natAbs_pos.mpr ha) hnorm

/-- Representations assigned the same quotient ideal generate the same
principal ideal in the maximal order. -/
theorem span_formIdealVector_eq_of_formRepresentationQuotientIdeal_eq
    (D : ℤ) (Q : IntegralBinaryQuadraticForm) (hQ : Q.discriminant = D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)]
    {x₁ y₁ x₂ y₂ : ℤ}
    (hJ : formRepresentationQuotientIdeal D Q hQ x₁ y₁ =
      formRepresentationQuotientIdeal D Q hQ x₂ y₂) :
    Ideal.span {formIdealVector D Q hQ x₁ y₁} =
      Ideal.span {formIdealVector D Q hQ x₂ y₂} := by
  rw [← formAssociatedIdeal_mul_formRepresentationQuotientIdeal D Q hQ x₁ y₁,
    ← formAssociatedIdeal_mul_formRepresentationQuotientIdeal D Q hQ x₂ y₂,
    hJ]

/-- Two representation vectors in one quotient-ideal fibre differ by a unit
of the maximal order. -/
theorem associated_formIdealVector_of_formRepresentationQuotientIdeal_eq
    (D : ℤ) (Q : IntegralBinaryQuadraticForm) (hQ : Q.discriminant = D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)]
    {x₁ y₁ x₂ y₂ : ℤ}
    (hJ : formRepresentationQuotientIdeal D Q hQ x₁ y₁ =
      formRepresentationQuotientIdeal D Q hQ x₂ y₂) :
    Associated (formIdealVector D Q hQ x₁ y₁)
      (formIdealVector D Q hQ x₂ y₂) := by
  rw [← Ideal.span_singleton_eq_span_singleton]
  exact span_formIdealVector_eq_of_formRepresentationQuotientIdeal_eq D Q hQ hJ

end
end IntegralBinaryQuadraticForm
end PellPaper
