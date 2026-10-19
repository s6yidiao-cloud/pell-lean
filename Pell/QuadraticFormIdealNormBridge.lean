import Pell.QuadraticFormIdealAttachment
import Pell.QuadraticOrderPellUnitRank
import Pell.QuadraticIdealNormEulerCoefficient
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict

/-!
# Norm constraints for a form-attached ideal

For a form `Q = [a,b,c]` of discriminant `D`, this module calculates the
algebra norm of the integral generator `(-b + sqrt(D)) / 2` used in
`formAssociatedIdeal`.  The resulting element-norm divisibilities give the
two one-sided bounds
`absNorm (formAssociatedIdeal D Q hQ) ∣ |a*c|` and
`absNorm (formAssociatedIdeal D Q hQ) ∣ |a|^2`.

No primitivity/gcd compression, reverse divisibility, or norm equality is
claimed in this module. `QuadraticFormIdealNormEquality` proves the equality
`absNorm (formAssociatedIdeal D Q hQ) = |a|` for primitive forms using a
conjugate-ideal product and integer Bézout.
-/

namespace PellPaper

namespace IntegralBinaryQuadraticForm

noncomputable section

local instance rationalQuadraticAlgebra_formIdealNorm_numberField_instance (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    NumberField (rationalQuadraticAlgebra D) :=
  rationalQuadraticAlgebra_numberField D

/-- The integral form generator has the displayed half-integral rational coordinates. -/
theorem formIdealGenerator_coe_coordinates (D : ℤ)
    (Q : IntegralBinaryQuadraticForm) (hQ : Q.discriminant = D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    ((formIdealGenerator D Q hQ :
      NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) :
      rationalQuadraticAlgebra D) = ⟨-(Q.b : ℚ) / 2, 1 / 2⟩ := by
  rw [coe_formIdealGenerator]
  have htwo_re : ((2 : rationalQuadraticAlgebra D).re) = (2 : ℚ) := by
    change (2 : ℚ) = 2
    norm_num
  have htwo_im : ((2 : rationalQuadraticAlgebra D).im) = (0 : ℚ) := by
    change (0 : ℚ) = 0
    norm_num
  field_simp
  ext
  · simp [QuadraticAlgebra.omega, htwo_re, htwo_im]
    ring
  · simp [QuadraticAlgebra.omega, htwo_re, htwo_im]

/-- The integral generator attached to `[a,b,c]` has signed algebra norm
`a * c`. -/
theorem algebraNorm_formIdealGenerator (D : ℤ)
    (Q : IntegralBinaryQuadraticForm) (hQ : Q.discriminant = D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    Algebra.norm ℤ (formIdealGenerator D Q hQ) = Q.a * Q.c := by
  apply (IsFractionRing.injective ℤ ℚ)
  rw [← Algebra.intNorm_eq_norm ℤ
    (NumberField.RingOfIntegers (rationalQuadraticAlgebra D))]
  rw [Algebra.algebraMap_intNorm (A := ℤ) (K := ℚ)
    (L := rationalQuadraticAlgebra D)
    (B := NumberField.RingOfIntegers (rationalQuadraticAlgebra D))]
  calc
    Algebra.norm ℚ ((algebraMap
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra D))
      (rationalQuadraticAlgebra D)) (formIdealGenerator D Q hQ)) =
      Algebra.norm ℚ (⟨-(Q.b : ℚ) / 2, 1 / 2⟩ :
        rationalQuadraticAlgebra D) := by
      congr 1
      exact formIdealGenerator_coe_coordinates D Q hQ
    _ = ((-(Q.b : ℚ)) / 2) * ((-(Q.b : ℚ)) / 2) -
      (D : ℚ) * (1 / 2) * (1 / 2) := by
      convert rationalQuadraticAlgebra_norm_apply D
        (⟨-(Q.b : ℚ) / 2, 1 / 2⟩ : rationalQuadraticAlgebra D) using 1
      ring_nf
      rfl
    _ = (algebraMap ℤ ℚ) (Q.a * Q.c) := by
      have hQq : (Q.b : ℚ) ^ 2 - 4 * (Q.a : ℚ) * (Q.c : ℚ) = (D : ℚ) := by
        norm_cast
      rw [← hQq]
      push_cast
      ring_nf
      rfl

private theorem ringOfIntegers_finrank_eq_two (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    Module.finrank ℤ (NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) = 2 := by
  rw [NumberField.RingOfIntegers.rank]
  exact rationalQuadraticAlgebra_finrank_eq_two D

private theorem algebraNorm_leadingCoefficient (D : ℤ)
    (Q : IntegralBinaryQuadraticForm)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    Algebra.norm ℤ (Q.a : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) =
      Q.a ^ 2 := by
  rw [show (Q.a : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) =
      algebraMap ℤ (NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) Q.a by rfl,
    Algebra.norm_algebraMap, ringOfIntegers_finrank_eq_two]

/-- The attached ideal norm divides the absolute norm of its quadratic
generator. -/
theorem absNorm_formAssociatedIdeal_dvd_generatorNorm (D : ℤ)
    (Q : IntegralBinaryQuadraticForm) (hQ : Q.discriminant = D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    Ideal.absNorm (formAssociatedIdeal D Q hQ) ∣ (Q.a * Q.c).natAbs := by
  simpa [algebraNorm_formIdealGenerator] using
    (Int.natAbs_dvd_natAbs.mpr
      (Ideal.absNorm_dvd_norm_of_mem
        (formIdealGenerator_mem_formAssociatedIdeal D Q hQ)))

/-- The attached ideal norm also divides the square of the absolute leading
coefficient. -/
theorem absNorm_formAssociatedIdeal_dvd_leadingCoefficient_sq (D : ℤ)
    (Q : IntegralBinaryQuadraticForm) (hQ : Q.discriminant = D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    Ideal.absNorm (formAssociatedIdeal D Q hQ) ∣ Q.a.natAbs ^ 2 := by
  simpa [algebraNorm_leadingCoefficient, Int.natAbs_pow] using
    (Int.natAbs_dvd_natAbs.mpr
      (Ideal.absNorm_dvd_norm_of_mem
        (leadingCoefficient_mem_formAssociatedIdeal D Q hQ)))

end

end IntegralBinaryQuadraticForm

end PellPaper
