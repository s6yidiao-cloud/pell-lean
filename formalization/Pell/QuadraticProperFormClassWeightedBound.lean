import Pell.QuadraticAlgebraSelectedCharacterClassNumberFormula
import Pell.QuadraticAlgebraClassAverageFormulaBridge
import Pell.QuadraticFormWideClassFibreCard

/-!
# A genuine proper-form class sum bounded by selected L-values

The actual finite proper-form quotient, not the surrogate form coordinate,
is bounded pointwise and in the finite discriminant sum by sqrt(D)*L(1)/R.
Only the actual two-to-one bound and the proved selected-character
class-number formula enter. The weighted analytic estimate and the reverse
field/form comparison remain separate obligations.
-/

namespace PellPaper

noncomputable section

open IntegralBinaryQuadraticForm

/-- The real L-value of the selected discriminant character, extended by
zero outside positive fundamental discriminants. -/
def selectedKroneckerLValue (D : ℕ) : ℝ := by
  classical
  exact if hD : PositiveFundamentalDiscriminant D then
    let _ : NeZero D := ⟨by have := hD.1; omega⟩
    (DirichletCharacter.LFunction
      (kroneckerCharacterAtPositiveFundamentalDiscriminantC D hD) 1).re
  else 0

/-- The selected character supplies the actual pointwise formula input. -/
theorem selectedKroneckerLValue_classNumberFormulaInput :
    RationalQuadraticAlgebraClassNumberFormulaInput selectedKroneckerLValue := by
  intro D hD
  simp only [selectedKroneckerLValue, dif_pos hD]
  exact rationalQuadraticAlgebraRegulator_mul_classNumber_eq_sqrt_mul_selected_LFunction_re D hD

/-- The literal finite proper-form class number has the source weighted
L-value upper bound, without using the surrogate model coordinate. -/
theorem properFormClass_card_le_sqrt_mul_selectedKroneckerLValue_div_regulator
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) :
    (Nat.card (ProperFormClass (D : ℤ)) : ℝ) ≤
      Real.sqrt (D : ℝ) * selectedKroneckerLValue D /
        rationalQuadraticAlgebraRegulatorAtPositiveFundamentalDiscriminant D hD := by
  have hR := rationalQuadraticAlgebraRegulatorAtPositiveFundamentalDiscriminant_pos D hD
  have hf := selectedKroneckerLValue_classNumberFormulaInput D hD
  have hbound : (Nat.card (ProperFormClass (D : ℤ)) : ℝ) ≤
      2 * rationalQuadraticAlgebraClassNumberAtPositiveFundamentalDiscriminant D hD := by
    exact_mod_cast properFormClass_card_le_two_mul_classNumber D hD
  apply (le_div_iff₀ hR).mpr
  nlinarith [mul_le_mul_of_nonneg_right hbound hR.le]

/-- The actual proper-form sum is bounded by the selected-character
weighted sum at every real cutoff. No analytic estimate is assumed. -/
theorem properFormClass_sum_le_selectedKronecker_weightedLRegulatorSum (X : ℝ) :
    (∑ D ∈ fundamentalDiscriminantsBelow X,
      (Nat.card (ProperFormClass (D : ℤ)) : ℝ)) ≤
      rationalQuadraticAlgebraWeightedLRegulatorSum selectedKroneckerLValue X := by
  classical
  unfold rationalQuadraticAlgebraWeightedLRegulatorSum
  apply Finset.sum_le_sum
  intro D hDX
  have hD := (mem_fundamentalDiscriminantsBelow.mp hDX).1
  rw [dif_pos hD]
  exact properFormClass_card_le_sqrt_mul_selectedKroneckerLValue_div_regulator D hD

end
end PellPaper
