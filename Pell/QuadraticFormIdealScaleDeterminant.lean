import Pell.QuadraticFormIdealVectorNorm
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Determinant and signed norm for a scaled form-ideal coordinate matrix

The literal vector scaling relation `y * B_R(Mv) = x * B_Q(v)` determines
the matrix determinant: `N(y) * a_R * det M = N(x) * a_Q`.  Comparing norms
then gives `R(Mv) = det M * Q(v)` when `y` and `a_R` are nonzero.
The determinant relation is proved from rational coordinates, not assumed.
-/

namespace PellPaper
namespace IntegralBinaryQuadraticForm

noncomputable section

local instance rationalQuadraticAlgebra_scaleDeterminant_numberField_instance (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    NumberField (rationalQuadraticAlgebra D) :=
  rationalQuadraticAlgebra_numberField D

private def quadraticCoordinateWedge (D : ℤ) (z w : rationalQuadraticAlgebra D) : ℚ :=
  z.re * w.im - z.im * w.re

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

private theorem quadraticCoordinateWedge_mul_integral (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)]
    (z : NumberField.RingOfIntegers (rationalQuadraticAlgebra D))
    (u v : rationalQuadraticAlgebra D) :
    quadraticCoordinateWedge D ((z : rationalQuadraticAlgebra D) * u)
        ((z : rationalQuadraticAlgebra D) * v) =
      ((Algebra.norm ℤ z : ℤ) : ℚ) * quadraticCoordinateWedge D u v := by
  rw [algebraNorm_cast_eq_coordinates]
  simp [quadraticCoordinateWedge]
  ring

private theorem quadraticCoordinateWedge_formIdealVectors (D : ℤ)
    (Q : IntegralBinaryQuadraticForm) (hQ : Q.discriminant = D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] (u v s t : ℤ) :
    quadraticCoordinateWedge D (formIdealVector D Q hQ u v : rationalQuadraticAlgebra D)
      (formIdealVector D Q hQ s t : rationalQuadraticAlgebra D) =
      -(Q.a : ℚ) / 2 * ((u : ℚ) * t - (v : ℚ) * s) := by
  rw [coe_formIdealVector, coe_formIdealVector]
  simp [quadraticCoordinateWedge]
  ring

/-- The signed scalar norms and leading coefficients determine the matrix
determinant from the literal ideal-vector scaling relation. -/
theorem algebraNorm_scalars_mul_leadingCoefficient_det_of_vector_scale
    (D : ℤ) (Q R : IntegralBinaryQuadraticForm)
    (hQ : Q.discriminant = D) (hR : R.discriminant = D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)]
    (x y : NumberField.RingOfIntegers (rationalQuadraticAlgebra D))
    (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hscale : ∀ v : Fin 2 → ℤ,
      y * formIdealVector D R hR (M.mulVec v 0) (M.mulVec v 1) =
        x * formIdealVector D Q hQ (v 0) (v 1)) :
    Algebra.norm ℤ y * R.a * M.det = Algebra.norm ℤ x * Q.a := by
  have h0 := congrArg
    (fun z : NumberField.RingOfIntegers (rationalQuadraticAlgebra D) =>
      (z : rationalQuadraticAlgebra D)) (hscale ![1, 0])
  have h1 := congrArg
    (fun z : NumberField.RingOfIntegers (rationalQuadraticAlgebra D) =>
      (z : rationalQuadraticAlgebra D)) (hscale ![0, 1])
  norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  have hw := congrArg₂ (quadraticCoordinateWedge D) h0 h1
  rw [quadraticCoordinateWedge_mul_integral, quadraticCoordinateWedge_mul_integral,
    quadraticCoordinateWedge_formIdealVectors, quadraticCoordinateWedge_formIdealVectors] at hw
  norm_num at hw
  apply (IsFractionRing.injective ℤ ℚ)
  change ((Algebra.norm ℤ y * R.a * M.det : ℤ) : ℚ) =
    ((Algebra.norm ℤ x * Q.a : ℤ) : ℚ)
  rw [Matrix.det_fin_two]
  push_cast
  linear_combination -2 * hw

/-- Under nonzero target scalar and leading coefficient, the matrix acts on
the form values by multiplication with its signed integer determinant. -/
theorem eval_transform_eq_det_mul_of_vector_scale
    (D : ℤ) (Q R : IntegralBinaryQuadraticForm)
    (hQ : Q.discriminant = D) (hR : R.discriminant = D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)]
    (x y : NumberField.RingOfIntegers (rationalQuadraticAlgebra D))
    (hy : y ≠ 0) (haR : R.a ≠ 0) (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hscale : ∀ v : Fin 2 → ℤ,
      y * formIdealVector D R hR (M.mulVec v 0) (M.mulVec v 1) =
        x * formIdealVector D Q hQ (v 0) (v 1)) :
    ∀ v : Fin 2 → ℤ, R.eval (M.mulVec v 0) (M.mulVec v 1) =
      M.det * Q.eval (v 0) (v 1) := by
  have hdet := algebraNorm_scalars_mul_leadingCoefficient_det_of_vector_scale
    D Q R hQ hR x y M hscale
  intro v
  have hnorm := congrArg (Algebra.norm ℤ) (hscale v)
  simp only [map_mul, algebraNorm_formIdealVector] at hnorm
  apply mul_left_cancel₀ (mul_ne_zero (Algebra.norm_ne_zero_iff.mpr hy) haR)
  calc
    (Algebra.norm ℤ y * R.a) * R.eval (M.mulVec v 0) (M.mulVec v 1) =
        (Algebra.norm ℤ x * Q.a) * Q.eval (v 0) (v 1) := by
      simpa only [mul_assoc] using hnorm
    _ = ((Algebra.norm ℤ y * R.a) * M.det) * Q.eval (v 0) (v 1) := by rw [hdet]
    _ = (Algebra.norm ℤ y * R.a) * (M.det * Q.eval (v 0) (v 1)) := by ring

end
end IntegralBinaryQuadraticForm
end PellPaper
