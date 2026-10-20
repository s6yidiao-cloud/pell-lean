import Pell.QuadraticIdealNormalizedNormForm
import Pell.QuadraticAlgebraFieldDiscriminantEquality

/-!
# The discriminant of the normalized norm form

The discriminant of an actual integer ideal basis is the square of the
ideal norm times the field discriminant.  The normalized norm form therefore
has exactly the field discriminant, and hence discriminant `D` when `D` is
positive fundamental.  No basis-index or discriminant premise is assumed.
-/

namespace PellPaper
namespace IntegralBinaryQuadraticForm

noncomputable section

local instance rationalQuadraticAlgebra_normalizedNormDiscriminant_numberField_instance (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    NumberField (rationalQuadraticAlgebra D) :=
  rationalQuadraticAlgebra_numberField D

/-- The discriminant-index formula for an actual integral ideal basis. -/
theorem quadraticIdealIntegerBasis_discriminant (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)]
    (I : Ideal (NumberField.RingOfIntegers (rationalQuadraticAlgebra D)))
    (bI : Module.Basis (Fin 2) ℤ I) :
    Algebra.discr ℤ (fun i => (bI i).1) =
      (I.absNorm : ℤ) ^ 2 * NumberField.discr (rationalQuadraticAlgebra D) := by
  let b := Module.finBasisOfFinrankEq ℤ
    (NumberField.RingOfIntegers (rationalQuadraticAlgebra D))
    (by rw [NumberField.RingOfIntegers.rank, rationalQuadraticAlgebra_finrank_eq_two D])
  have hdisc := Algebra.discr_of_matrix_vecMul b (b.toMatrix (fun i => (bI i).1))
  rw [Module.Basis.toMatrix_map_vecMul, NumberField.discr_eq_discr] at hdisc
  have hnorm := Ideal.natAbs_det_basis_change b I bI
  rw [Module.Basis.det_apply] at hnorm
  have hsq : (b.toMatrix (fun i => (bI i).1)).det ^ 2 = (I.absNorm : ℤ) ^ 2 := by
    rw [← hnorm, Int.natCast_natAbs, sq_abs]
    rfl
  exact hdisc.trans (by rw [hsq])

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

private theorem algebraTrace_cast_eq_coordinates (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)]
    (z : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) :
    ((Algebra.trace ℤ _ z : ℤ) : ℚ) = 2 * (z : rationalQuadraticAlgebra D).re := by
  change (algebraMap ℤ ℚ) (Algebra.trace ℤ _ z) = _
  rw [← Algebra.intTrace_eq_trace ℤ
    (NumberField.RingOfIntegers (rationalQuadraticAlgebra D))]
  rw [Algebra.algebraMap_intTrace (A := ℤ) (K := ℚ)
    (L := rationalQuadraticAlgebra D)
    (B := NumberField.RingOfIntegers (rationalQuadraticAlgebra D))]
  exact rationalQuadraticAlgebra_trace_apply D (z : rationalQuadraticAlgebra D)

private theorem algebraNorm_cross_discriminant (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)]
    (x y : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) :
    (Algebra.norm ℤ (x + y) - Algebra.norm ℤ x - Algebra.norm ℤ y) ^ 2 -
      4 * Algebra.norm ℤ x * Algebra.norm ℤ y = Algebra.discr ℤ ![x, y] := by
  rw [Algebra.discr_def, Matrix.det_fin_two]
  change _ = Algebra.trace ℤ _ (x * x) * Algebra.trace ℤ _ (y * y) -
    Algebra.trace ℤ _ (x * y) * Algebra.trace ℤ _ (y * x)
  apply (Int.cast_injective (α := ℚ))
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_ofNat,
    algebraNorm_cast_eq_coordinates, algebraTrace_cast_eq_coordinates]
  change _ = 2 * ((x : rationalQuadraticAlgebra D) * x).re *
      (2 * ((y : rationalQuadraticAlgebra D) * y).re) -
    2 * ((x : rationalQuadraticAlgebra D) * y).re *
      (2 * ((y : rationalQuadraticAlgebra D) * x).re)
  simp
  ring

/-- The normalized norm form has the actual number-field discriminant. -/
theorem quadraticIdealNormalizedNormForm_discriminant (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)]
    (I : Ideal (NumberField.RingOfIntegers (rationalQuadraticAlgebra D)))
    (hI : I ≠ ⊥) (bI : Module.Basis (Fin 2) ℤ I) :
    (quadraticIdealNormalizedNormForm D I bI).discriminant =
      NumberField.discr (rationalQuadraticAlgebra D) := by
  let Q := quadraticIdealNormalizedNormForm D I bI
  have ha := quadraticIdealNormalizedNormForm_eval D I bI 1 0
  have hc := quadraticIdealNormalizedNormForm_eval D I bI 0 1
  have hb := quadraticIdealNormalizedNormForm_eval D I bI 1 1
  change (I.absNorm : ℤ) * Q.eval 1 0 = _ at ha
  change (I.absNorm : ℤ) * Q.eval 0 1 = _ at hc
  change (I.absNorm : ℤ) * Q.eval 1 1 = _ at hb
  simp only [eval, one_pow, zero_pow (by decide : 2 ≠ 0), Int.cast_zero, Int.cast_one,
    mul_one, mul_zero,
    add_zero, zero_add] at ha hc hb
  have hcross : (I.absNorm : ℤ) * Q.b =
      Algebra.norm ℤ ((bI 0).1 + (bI 1).1) -
        Algebra.norm ℤ (bI 0).1 - Algebra.norm ℤ (bI 1).1 := by
    linear_combination hb - ha - hc
  have hdisc := algebraNorm_cross_discriminant D (bI 0).1 (bI 1).1
  have hvec : ![(bI 0).1, (bI 1).1] = fun i => (bI i).1 := by
    funext i
    fin_cases i <;> rfl
  rw [hvec, quadraticIdealIntegerBasis_discriminant] at hdisc
  rw [← hcross, ← ha, ← hc] at hdisc
  have hnorm : (I.absNorm : ℤ) ≠ 0 := by
    exact_mod_cast (mt Ideal.absNorm_eq_zero_iff.mp hI)
  apply mul_left_cancel₀ (pow_ne_zero 2 hnorm)
  change (I.absNorm : ℤ) ^ 2 * Q.discriminant = _
  calc
    _ = ((I.absNorm : ℤ) * Q.b) ^ 2 -
      4 * ((I.absNorm : ℤ) * Q.a) * ((I.absNorm : ℤ) * Q.c) := by
        simp only [discriminant]
        ring
    _ = _ := hdisc

/-- At a positive fundamental discriminant the constructed form's literal
discriminant is exactly the prescribed integer `D`. -/
theorem quadraticIdealNormalizedNormForm_discriminant_of_positiveFundamental
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) :
    let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
      ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
    ∀ (I : Ideal (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))))
      (_hI : I ≠ ⊥) (bI : Module.Basis (Fin 2) ℤ I),
      (quadraticIdealNormalizedNormForm (D : ℤ) I bI).discriminant = (D : ℤ) := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  dsimp only
  intro I hI bI
  rw [quadraticIdealNormalizedNormForm_discriminant (D : ℤ) I hI bI]
  exact rationalQuadraticAlgebraFieldDiscriminantAtPositiveFundamentalDiscriminant_eq D hD

end
end IntegralBinaryQuadraticForm
end PellPaper
