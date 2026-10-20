import Pell.QuadraticOrderPellFundamentalUnitModelCutoff

/-!
# A total normalized regulator from the selected maximal-order unit model

For every positive fundamental discriminant, the preceding construction
selects one oriented rank-one generator of the maximal-order unit group.  This
file packages its normalized logarithm as a total function on `ℕ`, assigning
zero outside that intended family.

The selected generator is noncomputable and definition-fixed through
Mathlib's fundamental system; it is not asserted to be a canonical closed
form for a fundamental unit.  The results below are only the algebraic
maximal-order-unit-to-Pell cutoff transfer.  In particular, they supply
neither a class-number formula nor an analytic estimate.
-/

namespace PellPaper

noncomputable section

/-- The normalized logarithm of the internally selected, positively oriented
maximal-order unit at a positive fundamental discriminant.  This is a
definition-fixed noncomputable choice, rather than a claim of a canonical
closed-form fundamental generator. -/
noncomputable def chosenMaximalOrderFundamentalUnitNormalizedLog
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) : ℝ := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  exact Real.log (concreteFundamentalUnitRealModel D hD).eta /
    Real.log (D : ℝ)

/-- A total normalized maximal-order fundamental-unit regulator.  It is zero
away from positive fundamental discriminants; on the intended family it is
the normalized logarithm of the internally selected unit model. -/
noncomputable def maximalOrderFundamentalUnitRegulator (D : ℕ) : ℝ := by
  classical
  exact if hD : PositiveFundamentalDiscriminant D then
    chosenMaximalOrderFundamentalUnitNormalizedLog D hD
  else 0

/-- On the intended family, the total regulator is exactly the normalized
logarithm attached to its definition-fixed selected maximal-order unit. -/
theorem maximalOrderFundamentalUnitRegulator_eq_chosenNormalizedLog
    {D : ℕ} (hD : PositiveFundamentalDiscriminant D) :
    maximalOrderFundamentalUnitRegulator D =
      chosenMaximalOrderFundamentalUnitNormalizedLog D hD := by
  simp [maximalOrderFundamentalUnitRegulator, hD]

/-- Expanded intended-family form of
`maximalOrderFundamentalUnitRegulator_eq_chosenNormalizedLog`.  The local
field instance is derived from `hD`, so no model or field-instance premise is
exposed to callers. -/
theorem maximalOrderFundamentalUnitRegulator_eq_log_of_positiveFundamentalDiscriminant
    {D : ℕ} (hD : PositiveFundamentalDiscriminant D) :
    maximalOrderFundamentalUnitRegulator D =
      let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
        ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
      Real.log (concreteFundamentalUnitRealModel D hD).eta /
        Real.log (D : ℝ) := by
  rw [maximalOrderFundamentalUnitRegulator_eq_chosenNormalizedLog hD]
  rfl

/-- Outside the positive fundamental-discriminant family, the total regulator
uses its stipulated value zero. -/
theorem maximalOrderFundamentalUnitRegulator_eq_zero_of_not_positiveFundamentalDiscriminant
    {D : ℕ} (hD : ¬ PositiveFundamentalDiscriminant D) :
    maximalOrderFundamentalUnitRegulator D = 0 := by
  simp [maximalOrderFundamentalUnitRegulator, hD]

/-- A strict cutoff on the total maximal-order fundamental-unit regulator
forces the literal Pell exceptional condition at the reparameterized
exponent.  This is an algebraic transfer only, not an analytic cutoff
estimate. -/
theorem smallFundamentalSolution_regulatorPellExponent_of_maximalOrderFundamentalUnitRegulator_lt
    {D : ℕ} (hD : PositiveFundamentalDiscriminant D) (t : ℝ)
    (hcutoff : maximalOrderFundamentalUnitRegulator D < t) :
    SmallFundamentalSolution (regulatorPellExponent t) D := by
  rw [maximalOrderFundamentalUnitRegulator_eq_chosenNormalizedLog hD] at hcutoff
  exact smallFundamentalSolution_regulatorPellExponent_of_concreteFundamentalUnitRealModel_cutoff_at_positiveFundamentalDiscriminant
    D hD t (by
      simpa [chosenMaximalOrderFundamentalUnitNormalizedLog] using hcutoff)

/-- The concrete Pell-order regulator is at most six times the total
maximal-order fundamental-unit regulator on positive fundamental
discriminants.  This compares the two algebraic parameters only; it makes no
class-number or analytic assertion. -/
theorem pellOrderRegulator_le_six_mul_maximalOrderFundamentalUnitRegulator
    {D : ℕ} (hD : PositiveFundamentalDiscriminant D) :
    pellOrderRegulator D ≤ 6 * maximalOrderFundamentalUnitRegulator D := by
  rw [maximalOrderFundamentalUnitRegulator_eq_chosenNormalizedLog hD]
  simpa [chosenMaximalOrderFundamentalUnitNormalizedLog] using
    pellOrderRegulator_le_six_mul_log_div_of_concreteFundamentalUnitRealModel_at_positiveFundamentalDiscriminant
      D hD

end

end PellPaper
