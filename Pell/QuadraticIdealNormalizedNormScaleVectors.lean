import Pell.QuadraticIdealNormalizedNormForm

/-!
# Integral scaling of the oriented ideal-basis vectors

For a negatively oriented actual ideal basis, multiplication by the
quadratic conjugate of its first vector takes the two vectors to the ideal
norm times `a, -theta` for the integral normalized norm form.
-/

namespace PellPaper
namespace IntegralBinaryQuadraticForm

noncomputable section

local instance rationalQuadraticAlgebra_normalizedNormScaleVectors_numberField_instance (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    NumberField (rationalQuadraticAlgebra D) :=
  rationalQuadraticAlgebra_numberField D

private theorem algebraNorm_cast_eq_coordinates (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)]
    (z : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) :
    ((Algebra.norm ℤ z : ℤ) : ℚ) =
      (z : rationalQuadraticAlgebra D).re * (z : rationalQuadraticAlgebra D).re -
        (D : ℚ) * (z : rationalQuadraticAlgebra D).im *
          (z : rationalQuadraticAlgebra D).im := by
  change (algebraMap ℤ ℚ) (Algebra.norm ℤ z) = _
  rw [← Algebra.intNorm_eq_norm ℤ
    (NumberField.RingOfIntegers (rationalQuadraticAlgebra D))]
  rw [Algebra.algebraMap_intNorm (A := ℤ) (K := ℚ)
    (L := rationalQuadraticAlgebra D)
    (B := NumberField.RingOfIntegers (rationalQuadraticAlgebra D))]
  exact rationalQuadraticAlgebra_norm_apply D (z : rationalQuadraticAlgebra D)

private theorem normCross_cast_eq_twice_real (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)]
    (x y : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) :
    ((Algebra.norm ℤ (x + y) - Algebra.norm ℤ x - Algebra.norm ℤ y : ℤ) : ℚ) =
      2 * ((x : rationalQuadraticAlgebra D).re * (y : rationalQuadraticAlgebra D).re -
        (D : ℚ) * (x : rationalQuadraticAlgebra D).im *
          (y : rationalQuadraticAlgebra D).im) := by
  simp only [Int.cast_sub, algebraNorm_cast_eq_coordinates]
  simp
  ring

/-- The two literal integral vector identities supplied by negative
orientation, with exactly the sign convention of the attached ideal basis. -/
theorem quadraticIdealNormalizedNormForm_scale_vectors (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)]
    (I : Ideal (NumberField.RingOfIntegers (rationalQuadraticAlgebra D)))
    (bI : Module.Basis (Fin 2) ℤ I)
    (hQ : (quadraticIdealNormalizedNormForm D I bI).discriminant = D)
    (hneg : 2 * (((bI 0).1 : rationalQuadraticAlgebra D).re *
      ((bI 1).1 : rationalQuadraticAlgebra D).im -
        ((bI 0).1 : rationalQuadraticAlgebra D).im *
          ((bI 1).1 : rationalQuadraticAlgebra D).re) = -(I.absNorm : ℚ)) :
    ringOfIntegersQuadraticConjugation D (bI 0).1 * (bI 0).1 =
      (I.absNorm : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) *
        (quadraticIdealNormalizedNormForm D I bI).a ∧
    ringOfIntegersQuadraticConjugation D (bI 0).1 * (bI 1).1 =
      (I.absNorm : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) *
        (-formIdealGenerator D (quadraticIdealNormalizedNormForm D I bI) hQ) := by
  let Q := quadraticIdealNormalizedNormForm D I bI
  have ha := quadraticIdealNormalizedNormForm_eval D I bI 1 0
  have hc := quadraticIdealNormalizedNormForm_eval D I bI 0 1
  have hb := quadraticIdealNormalizedNormForm_eval D I bI 1 1
  change (I.absNorm : ℤ) * Q.eval 1 0 = _ at ha
  change (I.absNorm : ℤ) * Q.eval 0 1 = _ at hc
  change (I.absNorm : ℤ) * Q.eval 1 1 = _ at hb
  simp only [eval, one_pow, zero_pow (by decide : 2 ≠ 0), Int.cast_zero, Int.cast_one,
    mul_one, mul_zero, add_zero, zero_add] at ha hc hb
  have hcross : (I.absNorm : ℤ) * Q.b =
      Algebra.norm ℤ ((bI 0).1 + (bI 1).1) -
        Algebra.norm ℤ (bI 0).1 - Algebra.norm ℤ (bI 1).1 := by
    linear_combination hb - ha - hc
  have haq := congrArg (fun n : ℤ => (n : ℚ)) ha
  simp only [Int.cast_mul, Int.cast_natCast, algebraNorm_cast_eq_coordinates] at haq
  have hbq := congrArg (fun n : ℤ => (n : ℚ)) hcross
  rw [normCross_cast_eq_twice_real] at hbq
  simp only [Int.cast_mul, Int.cast_natCast] at hbq
  constructor
  · apply Subtype.ext
    change star ((bI 0).1 : rationalQuadraticAlgebra D) *
      ((bI 0).1 : rationalQuadraticAlgebra D) =
        (I.absNorm : rationalQuadraticAlgebra D) * (Q.a : rationalQuadraticAlgebra D)
    ext <;> simp
    · nlinarith [haq]
    · ring
  · apply Subtype.ext
    change star ((bI 0).1 : rationalQuadraticAlgebra D) *
      ((bI 1).1 : rationalQuadraticAlgebra D) =
        (I.absNorm : rationalQuadraticAlgebra D) *
          -(formIdealGenerator D Q hQ : rationalQuadraticAlgebra D)
    rw [formIdealGenerator_coe_coordinates]
    ext <;> simp
    · nlinarith [hbq]
    · nlinarith [hneg]

end
end IntegralBinaryQuadraticForm
end PellPaper
