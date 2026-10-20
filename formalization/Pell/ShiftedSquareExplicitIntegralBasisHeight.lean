import Pell.ShiftedSquareNormalizedExplicitCoordinates
import Pell.ShiftedSquareFieldDiscriminantBound
import Pell.ShiftedSquareSurfaceCoefficientHeight
import Mathlib.Tactic

/-!
# Discriminant and height of a displayed shifted-square integral basis

This isolated candidate computes the discriminant of any integral basis
`1, omega` satisfying `omega^2 = t*omega + c`.  It then converts the existing
field-discriminant estimate into a uniform bound for `c` and hence for the
six surface coefficients.
-/

namespace PellPaper

noncomputable section

local instance shiftedSquareExplicitIntegralBasisHeight_numberField (a : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

/-- The displayed basis relation computes its integral discriminant. -/
theorem shiftedSquareExplicitIntegralBasis_discr
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (b : Module.Basis (Fin 2) ℤ
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))))
    (omega : NumberField.RingOfIntegers
      (rationalQuadraticAlgebra (-a))) (t c : ℤ)
    (hb0 : b 0 = 1) (hb1 : b 1 = omega)
    (homega : omega ^ 2 =
      (t : NumberField.RingOfIntegers
        (rationalQuadraticAlgebra (-a))) * omega + c) :
    Algebra.discr ℤ b = t ^ 2 + 4 * c := by
  have hone : shiftedSquareIntegralBasisElement b ![1, 0] = 1 := by
    rw [shiftedSquareIntegralBasisElement_eq_explicit b omega hb0 hb1]
    norm_num
  have hom : shiftedSquareIntegralBasisElement b ![0, 1] = omega := by
    rw [shiftedSquareIntegralBasisElement_eq_explicit b omega hb0 hb1]
    norm_num
  have homSq : shiftedSquareIntegralBasisElement b ![c, t] = omega ^ 2 := by
    rw [shiftedSquareIntegralBasisElement_eq_explicit b omega hb0 hb1,
      homega]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have htraceOne :
      Algebra.trace ℤ
          (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))) 1 = 2 := by
    rw [← hone, Algebra.trace_eq_matrix_trace b,
      shiftedSquareExplicitBasis_leftMulMatrix b omega t c hb0 hb1 homega]
    simp [Matrix.trace, Fin.sum_univ_succ]
  have htraceOmega :
      Algebra.trace ℤ
          (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))) omega = t := by
    rw [← hom, Algebra.trace_eq_matrix_trace b,
      shiftedSquareExplicitBasis_leftMulMatrix b omega t c hb0 hb1 homega]
    simp [Matrix.trace, Fin.sum_univ_succ]
  have htraceOmegaSq :
      Algebra.trace ℤ
          (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))) (omega ^ 2) =
        2 * c + t ^ 2 := by
    rw [← homSq, Algebra.trace_eq_matrix_trace b,
      shiftedSquareExplicitBasis_leftMulMatrix b omega t c hb0 hb1 homega]
    simp [Matrix.trace, Fin.sum_univ_succ]
    ring
  rw [Algebra.discr_def, Matrix.det_fin_two]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, hb0, hb1,
    one_mul, mul_one, htraceOne, htraceOmega]
  rw [← pow_two omega, htraceOmegaSq]
  ring

/-- Because the displayed basis is an integral basis, the preceding formula
is the number-field discriminant itself. -/
theorem shiftedSquareExplicitIntegralBasis_fieldDiscr
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (b : Module.Basis (Fin 2) ℤ
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))))
    (omega : NumberField.RingOfIntegers
      (rationalQuadraticAlgebra (-a))) (t c : ℤ)
    (hb0 : b 0 = 1) (hb1 : b 1 = omega)
    (homega : omega ^ 2 =
      (t : NumberField.RingOfIntegers
        (rationalQuadraticAlgebra (-a))) * omega + c) :
    NumberField.discr (rationalQuadraticAlgebra (-a)) = t ^ 2 + 4 * c := by
  calc
    NumberField.discr (rationalQuadraticAlgebra (-a)) =
        Algebra.discr ℤ b :=
      (NumberField.discr_eq_discr (rationalQuadraticAlgebra (-a)) b).symm
    _ = t ^ 2 + 4 * c :=
      shiftedSquareExplicitIntegralBasis_discr b omega t c hb0 hb1 homega

/-- The field-discriminant comparison gives a coarse but uniform bound for
the constant in either explicit integral-basis branch. -/
theorem abs_shiftedSquareExplicitIntegralBasis_constant_le
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (b : Module.Basis (Fin 2) ℤ
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))))
    (omega : NumberField.RingOfIntegers
      (rationalQuadraticAlgebra (-a))) (t c : ℤ)
    (hb0 : b 0 = 1) (hb1 : b 1 = omega)
    (ht : t = 0 ∨ t = 1)
    (homega : omega ^ 2 =
      (t : NumberField.RingOfIntegers
        (rationalQuadraticAlgebra (-a))) * omega + c) :
    |c| ≤ 4 * |a| + 1 := by
  have hdiscEq :=
    shiftedSquareExplicitIntegralBasis_fieldDiscr b omega t c hb0 hb1 homega
  have hfourEq :
      4 * c = NumberField.discr (rationalQuadraticAlgebra (-a)) - t ^ 2 := by
    linarith
  have hdisc :=
    rationalQuadraticAlgebra_neg_fieldDiscriminant_abs_le_four_mul_abs a
  calc
    |c| ≤ |4 * c| := by
      rw [abs_mul]
      norm_num
      nlinarith [abs_nonneg c]
    _ = |NumberField.discr (rationalQuadraticAlgebra (-a)) - t ^ 2| :=
      congrArg abs hfourEq
    _ ≤ |NumberField.discr (rationalQuadraticAlgebra (-a))| + |t ^ 2| :=
      abs_sub _ _
    _ ≤ 4 * |a| + 1 := by
      rcases ht with rfl | rfl <;> norm_num <;> omega

/-- Natural-number form of the preceding constant estimate. -/
theorem natAbs_shiftedSquareExplicitIntegralBasis_constant_le
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (b : Module.Basis (Fin 2) ℤ
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))))
    (omega : NumberField.RingOfIntegers
      (rationalQuadraticAlgebra (-a))) (t c : ℤ)
    (hb0 : b 0 = 1) (hb1 : b 1 = omega)
    (ht : t = 0 ∨ t = 1)
    (homega : omega ^ 2 =
      (t : NumberField.RingOfIntegers
        (rationalQuadraticAlgebra (-a))) * omega + c) :
    c.natAbs ≤ 4 * a.natAbs + 1 := by
  have h := abs_shiftedSquareExplicitIntegralBasis_constant_le
    b omega t c hb0 hb1 ht homega
  have h' : (c.natAbs : ℤ) ≤ 4 * (a.natAbs : ℤ) + 1 := by
    simpa only [Int.natCast_natAbs] using h
  exact_mod_cast h'

/-- Consequently the six-coefficient surface height is linear in `|a|`. -/
theorem shiftedSquareSurfaceCoefficientHeight_le_eight_mul_natAbs_add_four
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (b : Module.Basis (Fin 2) ℤ
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))))
    (omega : NumberField.RingOfIntegers
      (rationalQuadraticAlgebra (-a))) (t c : ℤ)
    (hb0 : b 0 = 1) (hb1 : b 1 = omega)
    (ht : t = 0 ∨ t = 1)
    (homega : omega ^ 2 =
      (t : NumberField.RingOfIntegers
        (rationalQuadraticAlgebra (-a))) * omega + c) :
    shiftedSquareSurfaceCoefficientHeight c ≤ 8 * a.natAbs + 4 := by
  have hc := natAbs_shiftedSquareExplicitIntegralBasis_constant_le
    b omega t c hb0 hb1 ht homega
  dsimp only [shiftedSquareSurfaceCoefficientHeight]
  omega

end

end PellPaper
