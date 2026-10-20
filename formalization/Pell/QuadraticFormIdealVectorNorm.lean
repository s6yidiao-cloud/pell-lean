import Pell.QuadraticFormIdealNormEquality

/-!
# The norm form on attached-ideal vectors

The integral vector `a*x - theta*y` lies in the ideal attached to `[a,b,c]`.
Its signed algebra norm is exactly `a * Q(x,y)`. This fixes the sign
convention needed for comparing ideal bases. It does not assert that these
vectors exhaust the ideal or construct a class correspondence.
-/

namespace PellPaper
namespace IntegralBinaryQuadraticForm

noncomputable section

local instance rationalQuadraticAlgebra_formVector_numberField_instance (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    NumberField (rationalQuadraticAlgebra D) :=
  rationalQuadraticAlgebra_numberField D

/-- The integer-coordinate vector in the attached ideal, with basis sign `-theta`. -/
def formIdealVector (D : ℤ) (Q : IntegralBinaryQuadraticForm)
    (hQ : Q.discriminant = D) [Fact (rationalQuadraticAlgebraNoRationalRoot D)]
    (x y : ℤ) : NumberField.RingOfIntegers (rationalQuadraticAlgebra D) :=
  Q.a * x - formIdealGenerator D Q hQ * y

theorem formIdealVector_mem (D : ℤ) (Q : IntegralBinaryQuadraticForm)
    (hQ : Q.discriminant = D) [Fact (rationalQuadraticAlgebraNoRationalRoot D)]
    (x y : ℤ) : formIdealVector D Q hQ x y ∈ formAssociatedIdeal D Q hQ := by
  apply Ideal.sub_mem
  · exact Ideal.mul_mem_right _ _ (leadingCoefficient_mem_formAssociatedIdeal D Q hQ)
  · exact Ideal.mul_mem_right _ _ (formIdealGenerator_mem_formAssociatedIdeal D Q hQ)

/-- Coordinates of the vector with respect to `1, sqrt(D)` over the rationals. -/
theorem coe_formIdealVector (D : ℤ) (Q : IntegralBinaryQuadraticForm)
    (hQ : Q.discriminant = D) [Fact (rationalQuadraticAlgebraNoRationalRoot D)]
    (x y : ℤ) :
    (formIdealVector D Q hQ x y : rationalQuadraticAlgebra D) =
      ⟨(Q.a : ℚ) * x + Q.b * y / 2, -(y : ℚ) / 2⟩ := by
  change (Q.a : rationalQuadraticAlgebra D) * x -
    (formIdealGenerator D Q hQ : rationalQuadraticAlgebra D) * y = _
  rw [formIdealGenerator_coe_coordinates]
  ext <;> simp <;> ring

/-- Signed integral norm of an arbitrary integer vector in the attached ideal. -/
theorem algebraNorm_formIdealVector (D : ℤ) (Q : IntegralBinaryQuadraticForm)
    (hQ : Q.discriminant = D) [Fact (rationalQuadraticAlgebraNoRationalRoot D)]
    (x y : ℤ) :
    Algebra.norm ℤ (formIdealVector D Q hQ x y) = Q.a * Q.eval x y := by
  apply (IsFractionRing.injective ℤ ℚ)
  rw [← Algebra.intNorm_eq_norm ℤ
    (NumberField.RingOfIntegers (rationalQuadraticAlgebra D))]
  rw [Algebra.algebraMap_intNorm (A := ℤ) (K := ℚ)
    (L := rationalQuadraticAlgebra D)
    (B := NumberField.RingOfIntegers (rationalQuadraticAlgebra D))]
  change Algebra.norm ℚ (formIdealVector D Q hQ x y : rationalQuadraticAlgebra D) = _
  rw [coe_formIdealVector]
  calc
    _ = ((Q.a : ℚ) * x + Q.b * y / 2) * ((Q.a : ℚ) * x + Q.b * y / 2) -
        (D : ℚ) * (-(y : ℚ) / 2) * (-(y : ℚ) / 2) := by
      convert rationalQuadraticAlgebra_norm_apply D
        (⟨(Q.a : ℚ) * x + Q.b * y / 2, -(y : ℚ) / 2⟩ :
          rationalQuadraticAlgebra D) using 1
      ring_nf
      rfl
    _ = _ := by
      have hdisc : (Q.b : ℚ) ^ 2 - 4 * Q.a * Q.c = D := by
        exact_mod_cast hQ
      rw [← hdisc]
      simp only [eval, map_mul, map_add, map_pow]
      change ((Q.a : ℚ) * x + Q.b * y / 2) * ((Q.a : ℚ) * x + Q.b * y / 2) -
          ((Q.b : ℚ) ^ 2 - 4 * Q.a * Q.c) * (-(y : ℚ) / 2) * (-(y : ℚ) / 2) =
        (Q.a : ℚ) * (Q.a * (x : ℚ) ^ 2 + Q.b * x * y + Q.c * (y : ℚ) ^ 2)
      ring

end
end IntegralBinaryQuadraticForm
end PellPaper
