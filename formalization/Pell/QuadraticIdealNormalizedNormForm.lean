import Pell.QuadraticFormIdealVectorNorm
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# An integral normalized norm form on an actual ideal basis

Every nonzero ideal in the actual ring of integers of the concrete quadratic
field has an integer basis indexed by `Fin 2`.  Dividing the signed norms of
the basis vectors and their cross coefficient by the ideal's absolute norm
gives an integral binary quadratic form.  Its evaluation is the norm of the
corresponding ideal vector divided by the ideal norm.

This slice does not yet assert its discriminant, primitivity, or a wide-class
identity.  All divisions and coefficients below are in the integers.
-/

namespace PellPaper
namespace IntegralBinaryQuadraticForm

noncomputable section

local instance rationalQuadraticAlgebra_normalizedNormForm_numberField_instance (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    NumberField (rationalQuadraticAlgebra D) :=
  rationalQuadraticAlgebra_numberField D

/-- An actual ordered integer basis of an arbitrary nonzero integral ideal. -/
noncomputable def quadraticIdealIntegerBasis (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)]
    (I : Ideal (NumberField.RingOfIntegers (rationalQuadraticAlgebra D)))
    (hI : I ≠ ⊥) : Module.Basis (Fin 2) ℤ I := by
  apply Module.finBasisOfFinrankEq ℤ I
  have h := Ideal.finrank_eq_finrank
    (NumberField.RingOfIntegers.basis (rationalQuadraticAlgebra D)) I hI
  change Module.finrank ℤ I = _ at h
  rw [h, NumberField.RingOfIntegers.rank, rationalQuadraticAlgebra_finrank_eq_two]

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

/-- The signed norm is a homogeneous quadratic polynomial in two integer
coordinates, with cross coefficient obtained from the norm of the sum. -/
theorem algebraNorm_integer_linearCombination (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)]
    (x y : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) (u v : ℤ) :
    Algebra.norm ℤ (x * u + y * v) =
      Algebra.norm ℤ x * u ^ 2 +
        (Algebra.norm ℤ (x + y) - Algebra.norm ℤ x - Algebra.norm ℤ y) * u * v +
        Algebra.norm ℤ y * v ^ 2 := by
  apply (IsFractionRing.injective ℤ ℚ)
  change ((Algebra.norm ℤ (x * u + y * v) : ℤ) : ℚ) =
    ((Algebra.norm ℤ x * u ^ 2 +
      (Algebra.norm ℤ (x + y) - Algebra.norm ℤ x - Algebra.norm ℤ y) * u * v +
      Algebra.norm ℤ y * v ^ 2 : ℤ) : ℚ)
  simp only [Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_pow]
  simp only [algebraNorm_cast_eq_coordinates]
  change (((x : rationalQuadraticAlgebra D) * u + y * v).re *
      ((x : rationalQuadraticAlgebra D) * u + y * v).re -
      (D : ℚ) * ((x : rationalQuadraticAlgebra D) * u + y * v).im *
      ((x : rationalQuadraticAlgebra D) * u + y * v).im) = _
  simp
  ring

/-- The integral normalized norm form for a specified actual ideal basis. -/
noncomputable def quadraticIdealNormalizedNormForm (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)]
    (I : Ideal (NumberField.RingOfIntegers (rationalQuadraticAlgebra D)))
    (bI : Module.Basis (Fin 2) ℤ I) : IntegralBinaryQuadraticForm where
  a := Algebra.norm ℤ (bI 0).1 / (I.absNorm : ℤ)
  b := (Algebra.norm ℤ ((bI 0).1 + (bI 1).1) -
    Algebra.norm ℤ (bI 0).1 - Algebra.norm ℤ (bI 1).1) / (I.absNorm : ℤ)
  c := Algebra.norm ℤ (bI 1).1 / (I.absNorm : ℤ)

/-- Exact evaluation identity for the integral normalized norm form; no
index, norm-divisibility, or quadratic-polynomial premise is assumed. -/
theorem quadraticIdealNormalizedNormForm_eval (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)]
    (I : Ideal (NumberField.RingOfIntegers (rationalQuadraticAlgebra D)))
    (bI : Module.Basis (Fin 2) ℤ I) (u v : ℤ) :
    (I.absNorm : ℤ) * (quadraticIdealNormalizedNormForm D I bI).eval u v =
      Algebra.norm ℤ ((bI 0).1 * u + (bI 1).1 * v) := by
  have hx := Ideal.absNorm_dvd_norm_of_mem (bI 0).2
  have hy := Ideal.absNorm_dvd_norm_of_mem (bI 1).2
  have hxy := Ideal.absNorm_dvd_norm_of_mem (I.add_mem (bI 0).2 (bI 1).2)
  have hb := dvd_sub (dvd_sub hxy hx) hy
  rw [algebraNorm_integer_linearCombination]
  simp only [eval, quadraticIdealNormalizedNormForm]
  calc
    _ = ((I.absNorm : ℤ) * (Algebra.norm ℤ (bI 0).1 / I.absNorm)) * u ^ 2 +
        ((I.absNorm : ℤ) * ((Algebra.norm ℤ ((bI 0).1 + (bI 1).1) -
          Algebra.norm ℤ (bI 0).1 - Algebra.norm ℤ (bI 1).1) / I.absNorm)) * u * v +
        ((I.absNorm : ℤ) * (Algebra.norm ℤ (bI 1).1 / I.absNorm)) * v ^ 2 := by ring
    _ = _ := by
      rw [Int.mul_ediv_cancel' hx, Int.mul_ediv_cancel' hb, Int.mul_ediv_cancel' hy]

/-- The requested construction for every nonzero actual integral ideal:
an ordered integer basis and an integral form with the normalized norm law. -/
theorem exists_quadraticIdealIntegerBasis_normalizedNormForm (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)]
    (I : Ideal (NumberField.RingOfIntegers (rationalQuadraticAlgebra D)))
    (hI : I ≠ ⊥) :
    ∃ (bI : Module.Basis (Fin 2) ℤ I) (Q : IntegralBinaryQuadraticForm),
      ∀ u v : ℤ, (I.absNorm : ℤ) * Q.eval u v =
        Algebra.norm ℤ ((bI 0).1 * u + (bI 1).1 * v) := by
  let bI := quadraticIdealIntegerBasis D I hI
  exact ⟨bI, quadraticIdealNormalizedNormForm D I bI,
    quadraticIdealNormalizedNormForm_eval D I bI⟩

end
end IntegralBinaryQuadraticForm
end PellPaper
