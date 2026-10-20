import Pell.QuadraticFormIdealAttachment

/-!
# Proper changes of variables and attached ideals

This isolated candidate records the concrete principal scaling relation behind
the classical form--ideal dictionary.  It deliberately stays at the level of
integral ideals: the relation says that the ideals attached to a form and to a
proper transform become equal after multiplication by explicit principal
integral ideals.  Passing this relation to a class group still requires the
nonzero/invertibility facts for the attached ideals and factors.
-/

namespace PellPaper

open scoped MatrixGroups

namespace IntegralBinaryQuadraticForm

noncomputable section

local instance rationalQuadraticAlgebra_formIdealTransform_numberField_instance (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    NumberField (rationalQuadraticAlgebra D) :=
  rationalQuadraticAlgebra_numberField D

/-- The integral factor by which the form ideal changes under the proper
substitution `g`.  In classical notation it is
`a g₀₀ + b g₁₀ + g₁₀ (-b + √D)/2`. -/
def formProperTransformFactor (D : ℤ) (Q : IntegralBinaryQuadraticForm)
    (hQ : Q.discriminant = D) (g : SL(2, ℤ))
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    NumberField.RingOfIntegers (rationalQuadraticAlgebra D) :=
  ((Q.a * g 0 0 + Q.b * g 1 0 : ℤ) :
    NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) +
    (g 1 0 : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) *
      formIdealGenerator D Q hQ

/-- The conjugate companion of `formProperTransformFactor`, written without
using a field automorphism so that it remains an algebraic integer. -/
def formProperTransformCompanionFactor (D : ℤ) (Q : IntegralBinaryQuadraticForm)
    (hQ : Q.discriminant = D) (g : SL(2, ℤ))
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    NumberField.RingOfIntegers (rationalQuadraticAlgebra D) :=
  (Q.a * g 0 0 : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) -
    (g 1 0 : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) *
      formIdealGenerator D Q hQ

/-- The element of the original form ideal multiplying the transform factor
to give the scaled transformed quadratic generator. -/
def formProperTransformSecondGenerator (D : ℤ) (Q : IntegralBinaryQuadraticForm)
    (hQ : Q.discriminant = D) (g : SL(2, ℤ))
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    NumberField.RingOfIntegers (rationalQuadraticAlgebra D) :=
  (g 1 1 : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) *
      formIdealGenerator D Q hQ -
    (Q.a * g 0 1 : NumberField.RingOfIntegers (rationalQuadraticAlgebra D))

@[simp]
theorem coe_formProperTransformFactor (D : ℤ) (Q : IntegralBinaryQuadraticForm)
    (hQ : Q.discriminant = D) (g : SL(2, ℤ))
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    ((formProperTransformFactor D Q hQ g :
      NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) :
        rationalQuadraticAlgebra D) =
      ((Q.a * g 0 0 + Q.b * g 1 0 : ℤ) : rationalQuadraticAlgebra D) +
        (g 1 0 : rationalQuadraticAlgebra D) *
          ((formIdealGenerator D Q hQ :
            NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) :
              rationalQuadraticAlgebra D) := rfl

@[simp]
theorem coe_formProperTransformCompanionFactor (D : ℤ)
    (Q : IntegralBinaryQuadraticForm) (hQ : Q.discriminant = D) (g : SL(2, ℤ))
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    ((formProperTransformCompanionFactor D Q hQ g :
      NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) :
        rationalQuadraticAlgebra D) =
      (Q.a * g 0 0 : rationalQuadraticAlgebra D) -
        (g 1 0 : rationalQuadraticAlgebra D) *
          ((formIdealGenerator D Q hQ :
            NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) :
              rationalQuadraticAlgebra D) := rfl

@[simp]
theorem coe_formProperTransformSecondGenerator (D : ℤ)
    (Q : IntegralBinaryQuadraticForm) (hQ : Q.discriminant = D) (g : SL(2, ℤ))
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    ((formProperTransformSecondGenerator D Q hQ g :
      NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) :
        rationalQuadraticAlgebra D) =
      (g 1 1 : rationalQuadraticAlgebra D) *
        ((formIdealGenerator D Q hQ :
          NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) :
            rationalQuadraticAlgebra D) -
      (Q.a * g 0 1 : rationalQuadraticAlgebra D) := rfl

private theorem formIdealGenerator_quadratic_relation (D : ℤ)
    (Q : IntegralBinaryQuadraticForm) (hQ : Q.discriminant = D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    ((formIdealGenerator D Q hQ :
      NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) :
        rationalQuadraticAlgebra D) ^ 2 +
      (Q.b : rationalQuadraticAlgebra D) *
        ((formIdealGenerator D Q hQ :
          NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) :
            rationalQuadraticAlgebra D) +
      (Q.a * Q.c : rationalQuadraticAlgebra D) = 0 := by
  rw [coe_formIdealGenerator]
  have hω : (QuadraticAlgebra.omega : rationalQuadraticAlgebra D) ^ 2 =
      (algebraMap ℤ (rationalQuadraticAlgebra D)) D := by
    simpa only [Mathlib.Tactic.Algebra.Int.cast_eq_algebraMap] using
      (show (QuadraticAlgebra.omega : rationalQuadraticAlgebra D) ^ 2 =
        (D : rationalQuadraticAlgebra D) by
          simpa [pow_two] using rationalQuadraticAlgebra_omega_sq D)
  have hQ' := congrArg (algebraMap ℤ (rationalQuadraticAlgebra D)) hQ
  simp only [discriminant, map_sub, map_pow, map_mul, map_ofNat] at hQ'
  calc
    ((-((algebraMap ℤ (rationalQuadraticAlgebra D)) Q.b) +
        QuadraticAlgebra.omega) / 2) ^ 2 +
        (Q.b : rationalQuadraticAlgebra D) *
          ((-((algebraMap ℤ (rationalQuadraticAlgebra D)) Q.b) +
            QuadraticAlgebra.omega) / 2) +
        (Q.a * Q.c : rationalQuadraticAlgebra D) =
        ((QuadraticAlgebra.omega : rationalQuadraticAlgebra D) ^ 2 -
          ((algebraMap ℤ (rationalQuadraticAlgebra D)) Q.b) ^ 2 +
          4 * ((algebraMap ℤ (rationalQuadraticAlgebra D)) Q.a) *
            ((algebraMap ℤ (rationalQuadraticAlgebra D)) Q.c)) / 4 := by
          simp only [Mathlib.Tactic.Algebra.Int.cast_eq_algebraMap]
          ring
    _ = 0 := by
      rw [hω, ← hQ']
      simp

/-- The norm identity for the two explicit factors associated to the first
column of a proper substitution. -/
theorem leadingCoefficient_mul_properTransformLeadingCoefficient_eq_factor_mul_companion
    (D : ℤ) (Q : IntegralBinaryQuadraticForm) (hQ : Q.discriminant = D)
    (g : SL(2, ℤ)) [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    (Q.a : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) *
      ((Q.properTransform g).a :
        NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) =
      formProperTransformFactor D Q hQ g *
        formProperTransformCompanionFactor D Q hQ g := by
  apply Subtype.ext
  change (Q.a : rationalQuadraticAlgebra D) *
      ((Q.properTransform g).a : rationalQuadraticAlgebra D) =
    ((formProperTransformFactor D Q hQ g :
      NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) :
        rationalQuadraticAlgebra D) *
      ((formProperTransformCompanionFactor D Q hQ g :
        NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) :
          rationalQuadraticAlgebra D)
  simp only [coe_formProperTransformFactor,
    coe_formProperTransformCompanionFactor,
    Mathlib.Tactic.Algebra.Int.cast_eq_algebraMap, map_add, map_mul, map_pow,
    properTransform]
  have htheta := formIdealGenerator_quadratic_relation D Q hQ
  linear_combination (g 1 0 : rationalQuadraticAlgebra D) ^ 2 * htheta

/-- The scaled quadratic generator of the transformed form is the transform
factor times an explicit element of the original form ideal. -/
theorem leadingCoefficient_mul_properTransformGenerator_eq_factor_mul_secondGenerator
    (D : ℤ) (Q : IntegralBinaryQuadraticForm) (hQ : Q.discriminant = D)
    (g : SL(2, ℤ)) [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    (Q.a : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) *
      formIdealGenerator D (Q.properTransform g)
        ((discriminant_properTransform Q g).trans hQ) =
      formProperTransformFactor D Q hQ g *
        formProperTransformSecondGenerator D Q hQ g := by
  apply Subtype.ext
  change (Q.a : rationalQuadraticAlgebra D) *
      ((formIdealGenerator D (Q.properTransform g)
        ((discriminant_properTransform Q g).trans hQ) :
          NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) :
            rationalQuadraticAlgebra D) =
    ((formProperTransformFactor D Q hQ g :
      NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) :
        rationalQuadraticAlgebra D) *
      ((formProperTransformSecondGenerator D Q hQ g :
        NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) :
          rationalQuadraticAlgebra D)
  simp only [coe_formIdealGenerator, coe_formProperTransformFactor,
    coe_formProperTransformSecondGenerator,
    Mathlib.Tactic.Algebra.Int.cast_eq_algebraMap, map_add, map_mul, map_ofNat,
    properTransform]
  have htheta := formIdealGenerator_quadratic_relation D Q hQ
  rw [coe_formIdealGenerator] at htheta
  simp only [Mathlib.Tactic.Algebra.Int.cast_eq_algebraMap] at htheta
  have hg := g.property
  rw [Matrix.det_fin_two] at hg
  have hg' := congrArg (algebraMap ℤ (rationalQuadraticAlgebra D)) hg
  simp only [map_sub, map_mul, map_one] at hg'
  have hgzero :
      (g 0 0 : rationalQuadraticAlgebra D) *
          (g 1 1 : rationalQuadraticAlgebra D) -
        (g 0 1 : rationalQuadraticAlgebra D) *
          (g 1 0 : rationalQuadraticAlgebra D) - 1 = 0 := by
    linear_combination hg'
  linear_combination
    -(g 1 0 : rationalQuadraticAlgebra D) *
      (g 1 1 : rationalQuadraticAlgebra D) * htheta -
    (Q.a : rationalQuadraticAlgebra D) *
      (((-((algebraMap ℤ (rationalQuadraticAlgebra D)) Q.b) +
        QuadraticAlgebra.omega) / 2) +
        (Q.b : rationalQuadraticAlgebra D) / 2) * hgzero

/-- The scaled transform factor belongs to the ideal attached to the
transformed form, with an explicit two-generator expression. -/
theorem leadingCoefficient_mul_factor_eq_transformedLeadingCombination
    (D : ℤ) (Q : IntegralBinaryQuadraticForm) (hQ : Q.discriminant = D)
    (g : SL(2, ℤ)) [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    (Q.a : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) *
      formProperTransformFactor D Q hQ g =
      (g 1 1 : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) *
        ((Q.a : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) *
          ((Q.properTransform g).a :
            NumberField.RingOfIntegers (rationalQuadraticAlgebra D))) +
      (g 1 0 : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) *
        ((Q.a : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) *
          formIdealGenerator D (Q.properTransform g)
            ((discriminant_properTransform Q g).trans hQ)) := by
  apply Subtype.ext
  change (Q.a : rationalQuadraticAlgebra D) *
      ((formProperTransformFactor D Q hQ g :
        NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) :
          rationalQuadraticAlgebra D) =
    (g 1 1 : rationalQuadraticAlgebra D) *
      ((Q.a : rationalQuadraticAlgebra D) *
        ((Q.properTransform g).a : rationalQuadraticAlgebra D)) +
    (g 1 0 : rationalQuadraticAlgebra D) *
      ((Q.a : rationalQuadraticAlgebra D) *
        ((formIdealGenerator D (Q.properTransform g)
          ((discriminant_properTransform Q g).trans hQ) :
            NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) :
              rationalQuadraticAlgebra D))
  simp only [coe_formIdealGenerator, coe_formProperTransformFactor,
    Mathlib.Tactic.Algebra.Int.cast_eq_algebraMap, map_add, map_mul, map_pow, map_ofNat,
    properTransform]
  have hg := g.property
  rw [Matrix.det_fin_two] at hg
  have hg' := congrArg (algebraMap ℤ (rationalQuadraticAlgebra D)) hg
  simp only [map_sub, map_mul, map_one] at hg'
  have hgzero :
      (g 0 0 : rationalQuadraticAlgebra D) *
          (g 1 1 : rationalQuadraticAlgebra D) -
        (g 0 1 : rationalQuadraticAlgebra D) *
          (g 1 0 : rationalQuadraticAlgebra D) - 1 = 0 := by
    linear_combination hg'
  linear_combination
    -(Q.a : rationalQuadraticAlgebra D) *
      ((Q.a : rationalQuadraticAlgebra D) *
          (g 0 0 : rationalQuadraticAlgebra D) +
        (Q.b : rationalQuadraticAlgebra D) *
          (g 1 0 : rationalQuadraticAlgebra D) / 2) * hgzero

/-- The product of the transform factor with the original quadratic
generator is a scaled element of the transformed form ideal. -/
theorem factor_mul_formIdealGenerator_eq_leadingCoefficient_mul_transformedCombination
    (D : ℤ) (Q : IntegralBinaryQuadraticForm) (hQ : Q.discriminant = D)
    (g : SL(2, ℤ)) [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    formProperTransformFactor D Q hQ g * formIdealGenerator D Q hQ =
      (Q.a : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) *
        ((g 0 0 : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) *
          formIdealGenerator D (Q.properTransform g)
            ((discriminant_properTransform Q g).trans hQ) +
        (g 0 1 : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) *
          ((Q.properTransform g).a :
            NumberField.RingOfIntegers (rationalQuadraticAlgebra D))) := by
  apply Subtype.ext
  change ((formProperTransformFactor D Q hQ g :
      NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) :
        rationalQuadraticAlgebra D) *
      ((formIdealGenerator D Q hQ :
        NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) :
          rationalQuadraticAlgebra D) =
    (Q.a : rationalQuadraticAlgebra D) *
      ((g 0 0 : rationalQuadraticAlgebra D) *
        ((formIdealGenerator D (Q.properTransform g)
          ((discriminant_properTransform Q g).trans hQ) :
            NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) :
              rationalQuadraticAlgebra D) +
      (g 0 1 : rationalQuadraticAlgebra D) *
        ((Q.properTransform g).a : rationalQuadraticAlgebra D))
  simp only [coe_formIdealGenerator, coe_formProperTransformFactor,
    Mathlib.Tactic.Algebra.Int.cast_eq_algebraMap, map_add, map_mul, map_pow, map_ofNat,
    properTransform]
  have htheta := formIdealGenerator_quadratic_relation D Q hQ
  rw [coe_formIdealGenerator] at htheta
  simp only [Mathlib.Tactic.Algebra.Int.cast_eq_algebraMap] at htheta
  have hg := g.property
  rw [Matrix.det_fin_two] at hg
  have hg' := congrArg (algebraMap ℤ (rationalQuadraticAlgebra D)) hg
  simp only [map_sub, map_mul, map_one] at hg'
  have hgzero :
      (g 0 0 : rationalQuadraticAlgebra D) *
          (g 1 1 : rationalQuadraticAlgebra D) -
        (g 0 1 : rationalQuadraticAlgebra D) *
          (g 1 0 : rationalQuadraticAlgebra D) - 1 = 0 := by
    linear_combination hg'
  linear_combination
    (g 1 0 : rationalQuadraticAlgebra D) * htheta +
    (Q.a : rationalQuadraticAlgebra D) *
      ((Q.b : rationalQuadraticAlgebra D) *
          (g 0 0 : rationalQuadraticAlgebra D) / 2 +
        (Q.c : rationalQuadraticAlgebra D) *
          (g 1 0 : rationalQuadraticAlgebra D)) * hgzero

/-- The companion factor is an explicit element of the original form ideal. -/
theorem formProperTransformCompanionFactor_mem_formAssociatedIdeal
    (D : ℤ) (Q : IntegralBinaryQuadraticForm) (hQ : Q.discriminant = D)
    (g : SL(2, ℤ)) [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    formProperTransformCompanionFactor D Q hQ g ∈
      formAssociatedIdeal D Q hQ := by
  rw [formAssociatedIdeal]
  apply Ideal.mem_span_pair.mpr
  refine ⟨(g 0 0 : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)),
    -(g 1 0 : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)), ?_⟩
  simp only [formProperTransformCompanionFactor]
  ring

/-- The second factor appearing in the scaled generator relation is an
explicit element of the original form ideal. -/
theorem formProperTransformSecondGenerator_mem_formAssociatedIdeal
    (D : ℤ) (Q : IntegralBinaryQuadraticForm) (hQ : Q.discriminant = D)
    (g : SL(2, ℤ)) [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    formProperTransformSecondGenerator D Q hQ g ∈
      formAssociatedIdeal D Q hQ := by
  rw [formAssociatedIdeal]
  apply Ideal.mem_span_pair.mpr
  refine ⟨-(g 0 1 : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)),
    (g 1 1 : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)), ?_⟩
  simp only [formProperTransformSecondGenerator]
  ring

/-- A proper change of variables preserves the attached ideal up to the
displayed principal scaling relation:
`(a) I(Q ∘ g) = (a g₀₀ + b g₁₀ + g₁₀ θ) I(Q)`.

This is an equality of actual integral ideals.  It is the concrete relation
needed later to compare their fractional-ideal or ideal-class images; this
theorem itself does not yet construct that quotient-level map. -/
theorem formAssociatedIdeal_principalScale_properTransform_eq
    (D : ℤ) (Q : IntegralBinaryQuadraticForm) (hQ : Q.discriminant = D)
    (g : SL(2, ℤ)) [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    Ideal.span {(Q.a : NumberField.RingOfIntegers (rationalQuadraticAlgebra D))} *
      formAssociatedIdeal D (Q.properTransform g)
        ((discriminant_properTransform Q g).trans hQ) =
      Ideal.span {formProperTransformFactor D Q hQ g} *
        formAssociatedIdeal D Q hQ := by
  apply (Ideal.span_singleton_mul_eq_span_singleton_mul
    (formAssociatedIdeal D (Q.properTransform g)
      ((discriminant_properTransform Q g).trans hQ))
    (formAssociatedIdeal D Q hQ)).mpr
  constructor
  · intro z hz
    rw [formAssociatedIdeal] at hz
    rcases Ideal.mem_span_pair.mp hz with ⟨x, y, hxy⟩
    refine ⟨x * formProperTransformCompanionFactor D Q hQ g +
      y * formProperTransformSecondGenerator D Q hQ g, ?_, ?_⟩
    · apply Ideal.add_mem
      · exact (formAssociatedIdeal D Q hQ).mul_mem_left _
          (formProperTransformCompanionFactor_mem_formAssociatedIdeal D Q hQ g)
      · exact (formAssociatedIdeal D Q hQ).mul_mem_left _
          (formProperTransformSecondGenerator_mem_formAssociatedIdeal D Q hQ g)
    · calc
        (Q.a : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) * z =
            (Q.a : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) *
              (x * ((Q.properTransform g).a :
                NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) +
              y * formIdealGenerator D (Q.properTransform g)
                ((discriminant_properTransform Q g).trans hQ)) := by rw [hxy]
        _ = x * ((Q.a : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) *
              ((Q.properTransform g).a :
                NumberField.RingOfIntegers (rationalQuadraticAlgebra D))) +
            y * ((Q.a : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) *
              formIdealGenerator D (Q.properTransform g)
                ((discriminant_properTransform Q g).trans hQ)) := by ring
        _ = x * (formProperTransformFactor D Q hQ g *
              formProperTransformCompanionFactor D Q hQ g) +
            y * (formProperTransformFactor D Q hQ g *
              formProperTransformSecondGenerator D Q hQ g) := by
              rw [leadingCoefficient_mul_properTransformLeadingCoefficient_eq_factor_mul_companion,
                leadingCoefficient_mul_properTransformGenerator_eq_factor_mul_secondGenerator]
        _ = formProperTransformFactor D Q hQ g *
            (x * formProperTransformCompanionFactor D Q hQ g +
              y * formProperTransformSecondGenerator D Q hQ g) := by ring
  · intro z hz
    rw [formAssociatedIdeal] at hz
    rcases Ideal.mem_span_pair.mp hz with ⟨x, y, hxy⟩
    let z' : NumberField.RingOfIntegers (rationalQuadraticAlgebra D) :=
      x * ((g 1 1 : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) *
        ((Q.properTransform g).a :
          NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) +
        (g 1 0 : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) *
          formIdealGenerator D (Q.properTransform g)
            ((discriminant_properTransform Q g).trans hQ)) +
      y * ((g 0 0 : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) *
        formIdealGenerator D (Q.properTransform g)
          ((discriminant_properTransform Q g).trans hQ) +
        (g 0 1 : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) *
          ((Q.properTransform g).a :
            NumberField.RingOfIntegers (rationalQuadraticAlgebra D)))
    refine ⟨z', ?_, ?_⟩
    · rw [formAssociatedIdeal]
      apply Ideal.mem_span_pair.mpr
      refine ⟨x * (g 1 1 : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) +
        y * (g 0 1 : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)),
        x * (g 1 0 : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) +
          y * (g 0 0 : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)), ?_⟩
      dsimp only [z']
      ring
    · calc
        (Q.a : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) * z' =
            x * ((g 1 1 : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) *
                ((Q.a : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) *
                  ((Q.properTransform g).a :
                    NumberField.RingOfIntegers (rationalQuadraticAlgebra D))) +
              (g 1 0 : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) *
                ((Q.a : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) *
                  formIdealGenerator D (Q.properTransform g)
                    ((discriminant_properTransform Q g).trans hQ))) +
            y * ((Q.a : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) *
              ((g 0 0 : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) *
                formIdealGenerator D (Q.properTransform g)
                  ((discriminant_properTransform Q g).trans hQ) +
              (g 0 1 : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) *
                ((Q.properTransform g).a :
                  NumberField.RingOfIntegers (rationalQuadraticAlgebra D)))) := by
              dsimp only [z']
              ring
        _ = x * ((Q.a : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) *
              formProperTransformFactor D Q hQ g) +
            y * (formProperTransformFactor D Q hQ g * formIdealGenerator D Q hQ) := by
              rw [← leadingCoefficient_mul_factor_eq_transformedLeadingCombination,
                ← factor_mul_formIdealGenerator_eq_leadingCoefficient_mul_transformedCombination]
        _ = formProperTransformFactor D Q hQ g *
            (x * (Q.a : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) +
              y * formIdealGenerator D Q hQ) := by ring
        _ = formProperTransformFactor D Q hQ g * z := by rw [hxy]

end

end IntegralBinaryQuadraticForm

end PellPaper
