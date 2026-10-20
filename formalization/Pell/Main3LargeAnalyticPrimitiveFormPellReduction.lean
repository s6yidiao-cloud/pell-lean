import Pell.Main3LargeAnalyticTargetFibreSurfaceForm
import Mathlib.Tactic

/-!
# From a primitive surface-form representation to generalized Pell

This file records the exact completion-of-the-square map from an integral
binary quadratic form representation to a generalized Pell equation, then
specializes it to an actual main3 large-analytic target fibre.  The source
map is injective and retains the congruence needed to recover the original
source coordinate.

No unit-orbit estimate, height-window estimate, or cardinality bound is
asserted here.
-/

namespace PellPaper

namespace IntegralBinaryQuadraticForm

/-- Complete the square using the leading coefficient of `Q`. -/
def leadingPellMap (Q : IntegralBinaryQuadraticForm) (z : ℤ × ℤ) : ℤ × ℤ :=
  (2 * Q.a * z.1 + Q.b * z.2, z.2)

/-- Complete the square after swapping the two source coordinates. -/
def trailingPellMap (Q : IntegralBinaryQuadraticForm) (z : ℤ × ℤ) : ℤ × ℤ :=
  (2 * Q.c * z.2 + Q.b * z.1, z.1)

/-- The exact completion-of-the-square identity at the leading
coefficient. -/
theorem leadingCoefficient_pell_identity
    (Q : IntegralBinaryQuadraticForm) (x y : ℤ) :
    (2 * Q.a * x + Q.b * y) ^ 2 - Q.discriminant * y ^ 2 =
      4 * Q.a * Q.eval x y := by
  simp only [discriminant, eval]
  ring

/-- The coordinate-swapped completion-of-the-square identity.  In
particular, this is the alternative orientation available when one begins
with a vanishing leading coefficient. -/
theorem trailingCoefficient_pell_identity
    (Q : IntegralBinaryQuadraticForm) (x y : ℤ) :
    (2 * Q.c * y + Q.b * x) ^ 2 - Q.discriminant * x ^ 2 =
      4 * Q.c * Q.eval x y := by
  simp only [discriminant, eval]
  ring

theorem leadingPellMap_spec
    (Q : IntegralBinaryQuadraticForm) (z : ℤ × ℤ) :
    (Q.leadingPellMap z).1 ^ 2 -
        Q.discriminant * (Q.leadingPellMap z).2 ^ 2 =
      4 * Q.a * Q.eval z.1 z.2 := by
  exact leadingCoefficient_pell_identity Q z.1 z.2

theorem trailingPellMap_spec
    (Q : IntegralBinaryQuadraticForm) (z : ℤ × ℤ) :
    (Q.trailingPellMap z).1 ^ 2 -
        Q.discriminant * (Q.trailingPellMap z).2 ^ 2 =
      4 * Q.c * Q.eval z.1 z.2 := by
  exact trailingCoefficient_pell_identity Q z.1 z.2

/-- The leading orientation retains the exact congruence required to recover
the original first coordinate. -/
theorem leadingCoefficient_dvd_pellMap_fst_sub
    (Q : IntegralBinaryQuadraticForm) (z : ℤ × ℤ) :
    2 * Q.a ∣ (Q.leadingPellMap z).1 - Q.b * (Q.leadingPellMap z).2 := by
  refine ⟨z.1, ?_⟩
  simp only [leadingPellMap]
  ring

/-- The swapped orientation retains the analogous recovery congruence. -/
theorem trailingCoefficient_dvd_pellMap_fst_sub
    (Q : IntegralBinaryQuadraticForm) (z : ℤ × ℤ) :
    2 * Q.c ∣ (Q.trailingPellMap z).1 - Q.b * (Q.trailingPellMap z).2 := by
  refine ⟨z.2, ?_⟩
  simp only [trailingPellMap]
  ring

/-- A nonsquare discriminant forces the leading coefficient to be nonzero. -/
theorem leadingCoefficient_ne_zero_of_discriminant_not_isSquare
    (Q : IntegralBinaryQuadraticForm)
    (hdisc : ¬ IsSquare Q.discriminant) : Q.a ≠ 0 := by
  intro ha
  apply hdisc
  refine ⟨Q.b, ?_⟩
  simp only [discriminant, ha, zero_mul, mul_zero, sub_zero]
  ring

/-- Likewise a nonsquare discriminant forces the trailing coefficient to be
nonzero. -/
theorem trailingCoefficient_ne_zero_of_discriminant_not_isSquare
    (Q : IntegralBinaryQuadraticForm)
    (hdisc : ¬ IsSquare Q.discriminant) : Q.c ≠ 0 := by
  intro hc
  apply hdisc
  refine ⟨Q.b, ?_⟩
  simp only [discriminant, hc, mul_zero, sub_zero]
  ring

/-- The leading completion-of-the-square map is injective as soon as its
orientation coefficient is nonzero. -/
theorem leadingPellMap_injective
    (Q : IntegralBinaryQuadraticForm) (ha : Q.a ≠ 0) :
    Function.Injective Q.leadingPellMap := by
  rintro ⟨x, y⟩ ⟨x', y'⟩ hmap
  have hy : y = y' := congrArg Prod.snd hmap
  have hfirst := congrArg Prod.fst hmap
  simp only [leadingPellMap] at hfirst
  subst y'
  have hxmul : (2 * Q.a) * x = (2 * Q.a) * x' := by
    apply add_right_cancel (b := Q.b * y)
    simpa only [mul_assoc] using hfirst
  have hx : x = x' := mul_left_cancel₀ (mul_ne_zero (by norm_num) ha) hxmul
  exact Prod.ext hx rfl

/-- The swapped completion-of-the-square map is injective under its
corresponding nonvanishing condition. -/
theorem trailingPellMap_injective
    (Q : IntegralBinaryQuadraticForm) (hc : Q.c ≠ 0) :
    Function.Injective Q.trailingPellMap := by
  rintro ⟨x, y⟩ ⟨x', y'⟩ hmap
  have hx : x = x' := congrArg Prod.snd hmap
  have hfirst := congrArg Prod.fst hmap
  simp only [trailingPellMap] at hfirst
  subst x'
  have hymul : (2 * Q.c) * y = (2 * Q.c) * y' := by
    apply add_right_cancel (b := Q.b * x)
    simpa only [mul_assoc] using hfirst
  have hy : y = y' := mul_left_cancel₀ (mul_ne_zero (by norm_num) hc) hymul
  exact Prod.ext rfl hy

end IntegralBinaryQuadraticForm

/-- The integer solution fibre of one generalized Pell equation. -/
def generalizedPellSolutionFibre (Delta level : ℤ) : Set (ℤ × ℤ) :=
  {z | z.1 ^ 2 - Delta * z.2 ^ 2 = level}

/-- The literal surface form selected by the fixed shift and target vector.
It is independent of the source point in the target fibre. -/
noncomputable def main3LargeAnalyticFixedTargetSurfaceForm
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (y : Fin 2 → ℤ) : IntegralBinaryQuadraticForm := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let B := shiftedSquareFixedExplicitIntegralBasisData
    (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
  exact shiftedSquareSurfaceForm B.t B.c y

/-- The primitive part of the fixed-target surface form. -/
noncomputable def main3LargeAnalyticFixedTargetPrimitiveSurfaceForm
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (y : Fin 2 → ℤ) : IntegralBinaryQuadraticForm :=
  integralBinaryQuadraticFormPrimitivePart
    (main3LargeAnalyticFixedTargetSurfaceForm hi y)

/-- The common coefficient content removed from the fixed-target surface
form. -/
noncomputable def main3LargeAnalyticFixedTargetSurfaceContent
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (y : Fin 2 → ℤ) : ℕ :=
  integralBinaryQuadraticFormContent
    (main3LargeAnalyticFixedTargetSurfaceForm hi y)

/-- A point retained by one literal fixed-key, fixed-cell target fibre. -/
abbrev Main3LargeAnalyticFixedKeyCellTargetFibrePoint
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (y : Fin 2 → ℤ) :=
  {p : (Fin 2 → ℤ) × (Fin 2 → ℤ) //
    p ∈ main3LargeAnalyticFixedKeyCellTargetFibre
      htheta hY hi key cell y}

/-- Complete the square on the source coordinates of a target-fibre point,
using the one primitive form fixed by the shift and `y`. -/
noncomputable def main3LargeAnalyticTargetFibreLeadingPellMap
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (y : Fin 2 → ℤ)
    (p : Main3LargeAnalyticFixedKeyCellTargetFibrePoint
      htheta hY hi key cell y) : ℤ × ℤ :=
  (main3LargeAnalyticFixedTargetPrimitiveSurfaceForm hi y).leadingPellMap
    (p.1.1 0, p.1.1 1)

end PellPaper
