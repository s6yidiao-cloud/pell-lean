import Pell.QuadraticFormProperEquivalence
import Pell.QuadraticOrderPellTraceNorm

/-!
# A direct ideal attached to a primitive quadratic form

For a form `Q = [a,b,c]` of discriminant `D`, the classical ideal--form
dictionary begins with the integral element `(-b + √D) / 2`.  This module
constructs that element in the actual ring of integers of the project's
concrete quadratic algebra, and attaches the two-generated ideal
`(a, (-b + √D) / 2)`.

The module intentionally stops before quotienting by proper equivalence:
properly equivalent forms are expected to give ideals in the same ideal
class, not literally equal ideals.  No finiteness, ideal-class comparison,
or class-number statement is made here.
-/

namespace PellPaper

namespace IntegralBinaryQuadraticForm

noncomputable section

local instance rationalQuadraticAlgebra_formIdeal_numberField_instance (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    NumberField (rationalQuadraticAlgebra D) :=
  rationalQuadraticAlgebra_numberField D

private theorem formIdealGenerator_isIntegral (D : ℤ)
    (Q : IntegralBinaryQuadraticForm) (hQ : Q.discriminant = D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    IsIntegral ℤ
      ((-((algebraMap ℤ (rationalQuadraticAlgebra D)) Q.b) +
        QuadraticAlgebra.omega) / 2) := by
  refine ⟨Polynomial.X ^ 2 + (Polynomial.C Q.b * Polynomial.X +
      Polynomial.C (Q.a * Q.c)), ?_, ?_⟩
  · apply Polynomial.monic_X_pow_add
    apply lt_of_le_of_lt (Polynomial.degree_add_le _ _)
    apply max_lt
    · exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_le _) (by norm_num)
    · exact lt_of_le_of_lt Polynomial.degree_C_le (by norm_num)
  · rw [Polynomial.eval₂_add, Polynomial.eval₂_X_pow,
      Polynomial.eval₂_add, Polynomial.eval₂_mul,
      Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_C]
    have hω : (QuadraticAlgebra.omega : rationalQuadraticAlgebra D) ^ 2 =
        (algebraMap ℤ (rationalQuadraticAlgebra D)) D := by
      simpa only [Mathlib.Tactic.Algebra.Int.cast_eq_algebraMap] using
        (show (QuadraticAlgebra.omega : rationalQuadraticAlgebra D) ^ 2 =
          (D : rationalQuadraticAlgebra D) by
            simpa [pow_two] using rationalQuadraticAlgebra_omega_sq D)
    have hQ' := congrArg (algebraMap ℤ (rationalQuadraticAlgebra D)) hQ
    simp only [discriminant, map_sub, map_pow, map_mul, map_ofNat] at hQ'
    calc
      _ = ((QuadraticAlgebra.omega : rationalQuadraticAlgebra D) ^ 2 -
          ((algebraMap ℤ (rationalQuadraticAlgebra D)) Q.b) ^ 2 +
          4 * ((algebraMap ℤ (rationalQuadraticAlgebra D)) Q.a) *
            ((algebraMap ℤ (rationalQuadraticAlgebra D)) Q.c)) / 4 := by
            simp only [map_mul]
            ring
      _ = 0 := by rw [hω, ← hQ']; simp

/-- The classical integral generator `(-b + √D) / 2` attached to a form of
discriminant `D`.  Its integrality is proved from the form discriminant
identity, rather than assumed from a description of the maximal order. -/
def formIdealGenerator (D : ℤ) (Q : IntegralBinaryQuadraticForm)
    (hQ : Q.discriminant = D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    NumberField.RingOfIntegers (rationalQuadraticAlgebra D) :=
  ⟨(-((algebraMap ℤ (rationalQuadraticAlgebra D)) Q.b) +
    QuadraticAlgebra.omega) / 2, by
    exact formIdealGenerator_isIntegral D Q hQ⟩

/-- Coercing the attached ring-of-integers generator into the field gives the
displayed classical expression. -/
@[simp]
theorem coe_formIdealGenerator (D : ℤ) (Q : IntegralBinaryQuadraticForm)
    (hQ : Q.discriminant = D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    ((formIdealGenerator D Q hQ :
      NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) :
        rationalQuadraticAlgebra D) =
      (-((algebraMap ℤ (rationalQuadraticAlgebra D)) Q.b) +
        QuadraticAlgebra.omega) / 2 := rfl

/-- The integral ideal classically attached to a form of discriminant `D`:
the ideal generated in the maximal order by `a` and `(-b + √D) / 2`.

This is an actual ideal of the actual ring of integers.  The definition alone
does not say that it descends to proper-form classes; proper changes of
variables generally change this ideal by a principal factor rather than by
literal equality. -/
def formAssociatedIdeal (D : ℤ) (Q : IntegralBinaryQuadraticForm)
    (hQ : Q.discriminant = D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    Ideal (NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) :=
  Ideal.span {(Q.a : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)),
    formIdealGenerator D Q hQ}

/-- The leading coefficient lies in its attached ideal. -/
theorem leadingCoefficient_mem_formAssociatedIdeal (D : ℤ)
    (Q : IntegralBinaryQuadraticForm) (hQ : Q.discriminant = D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    (Q.a : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) ∈
      formAssociatedIdeal D Q hQ := by
  exact Ideal.subset_span (by simp)

/-- The quadratic generator lies in its attached ideal. -/
theorem formIdealGenerator_mem_formAssociatedIdeal (D : ℤ)
    (Q : IntegralBinaryQuadraticForm) (hQ : Q.discriminant = D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    formIdealGenerator D Q hQ ∈ formAssociatedIdeal D Q hQ := by
  exact Ideal.subset_span (by simp)

/-- If the leading coefficient is nonzero, the attached ideal is nonzero.
This is the basic nondegeneracy fact needed before passing an integral ideal
to a fractional ideal or an ideal-class construction. -/
theorem formAssociatedIdeal_ne_bot_of_a_ne_zero (D : ℤ)
    (Q : IntegralBinaryQuadraticForm) (hQ : Q.discriminant = D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] (ha : Q.a ≠ 0) :
    formAssociatedIdeal D Q hQ ≠ ⊥ := by
  intro hbot
  have hmem := leadingCoefficient_mem_formAssociatedIdeal D Q hQ
  rw [hbot] at hmem
  have hzero : (Q.a : NumberField.RingOfIntegers (rationalQuadraticAlgebra D)) = 0 := by
    simpa using hmem
  have hzero' := congrArg
    (fun z : NumberField.RingOfIntegers (rationalQuadraticAlgebra D) =>
      (z : rationalQuadraticAlgebra D)) hzero
  apply ha
  exact_mod_cast hzero'

/-- A form with leading coefficient one attaches to the unit ideal.  In
particular, this covers the displayed principal forms in the two fundamental
discriminant branches. -/
theorem formAssociatedIdeal_eq_top_of_a_eq_one (D : ℤ)
    (Q : IntegralBinaryQuadraticForm) (hQ : Q.discriminant = D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] (ha : Q.a = 1) :
    formAssociatedIdeal D Q hQ = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  simpa [ha] using leadingCoefficient_mem_formAssociatedIdeal D Q hQ

/-- At a positive fundamental discriminant, every primitive form has nonzero
leading coefficient.  Thus its attached ideal is automatically nonzero; this
uses only that a positive fundamental discriminant is not an integer square. -/
theorem leadingCoefficient_ne_zero_of_positiveFundamentalDiscriminant
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D)
    (Q : PrimitiveBinaryQuadraticForms (D : ℤ)) : Q.1.a ≠ 0 := by
  intro ha
  apply int_not_isSquare_of_positiveFundamentalDiscriminant hD
  have hdisc : Q.1.b ^ 2 = (D : ℤ) := by
    calc
      Q.1.b ^ 2 = Q.1.discriminant := by simp [discriminant, ha]
      _ = (D : ℤ) := Q.2.2
  refine ⟨Q.1.b, ?_⟩
  simpa [pow_two] using hdisc.symm


end

end IntegralBinaryQuadraticForm

end PellPaper
