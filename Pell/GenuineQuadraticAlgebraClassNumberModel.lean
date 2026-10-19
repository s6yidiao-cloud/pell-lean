import Pell.QuadraticFormWideClassSurjectivity
import Pell.QuadraticProperFormClassWeightedBound

/-!
# A genuine discriminant-indexed field/form class-number model

Unlike the earlier explicitly named surrogate, the ordinary coordinate is
the actual ideal class number of the concrete quadratic field and the form
coordinate is the cardinality of the literal proper primitive form quotient.
Both comparison fields are proved from the actual wide-class map, not
defined into the coordinates. Values outside positive fundamental
discriminants are set to zero and do not affect the sums.

This constructs a genuine model for the chosen field representatives. It
does not classify all real quadratic fields or prove the analytic average.
-/

namespace PellPaper

noncomputable section

open IntegralBinaryQuadraticForm

/-- The two actual class numbers with their proved positivity and bounds. -/
def genuineQuadraticAlgebraClassNumberModel : ClassNumberModel := by
  classical
  exact
    { ordinaryClassNumber := fun D => if hD : PositiveFundamentalDiscriminant D then
        rationalQuadraticAlgebraClassNumberAtPositiveFundamentalDiscriminant D hD else 0
      formClassNumber := fun D => if PositiveFundamentalDiscriminant D then
        Nat.card (ProperFormClass (D : ℤ)) else 0
      ordinaryClassNumber_pos := fun D hD => by
        simp only [dif_pos hD]
        exact rationalQuadraticAlgebraClassNumberAtPositiveFundamentalDiscriminant_pos D hD
      formClassNumber_pos := fun D hD => by
        simp only [if_pos hD]
        exact properFormClass_card_pos_of_positiveFundamentalDiscriminant D hD
      ordinary_le_form := fun D hD => by
        simp only [dif_pos hD, if_pos hD]
        exact classNumber_le_properFormClass_card D hD
      form_le_twice_ordinary := fun D hD => by
        simp only [dif_pos hD, if_pos hD]
        exact properFormClass_card_le_two_mul_classNumber D hD }

/-- The ordinary coordinate is the actual ideal class number. -/
theorem genuineQuadraticAlgebraClassNumberModel_ordinary_eq
    {D : ℕ} (hD : PositiveFundamentalDiscriminant D) :
    genuineQuadraticAlgebraClassNumberModel.ordinaryClassNumber D =
      rationalQuadraticAlgebraClassNumberAtPositiveFundamentalDiscriminant D hD := by
  simp [genuineQuadraticAlgebraClassNumberModel, hD]

/-- The form coordinate is the genuine proper-form quotient cardinality. -/
theorem genuineQuadraticAlgebraClassNumberModel_form_eq
    {D : ℕ} (hD : PositiveFundamentalDiscriminant D) :
    genuineQuadraticAlgebraClassNumberModel.formClassNumber D =
      Nat.card (ProperFormClass (D : ℤ)) := by
  simp [genuineQuadraticAlgebraClassNumberModel, hD]

/-- The model sum is literally the actual proper-form discriminant sum. -/
theorem genuineQuadraticAlgebraClassNumberModel_formClassSum_eq (X : ℝ) :
    genuineQuadraticAlgebraClassNumberModel.formClassSum X =
      ∑ D ∈ fundamentalDiscriminantsBelow X, (Nat.card (ProperFormClass (D : ℤ)) : ℝ) := by
  unfold ClassNumberModel.formClassSum
  apply Finset.sum_congr rfl
  intro D hDX
  rw [genuineQuadraticAlgebraClassNumberModel_form_eq (mem_fundamentalDiscriminantsBelow.mp hDX).1]

/-- The genuine model's form sum has the proved actual L-value weight bound. -/
theorem genuineQuadraticAlgebraClassNumberModel_formClassSum_le_weightedLRegulatorSum (X : ℝ) :
    genuineQuadraticAlgebraClassNumberModel.formClassSum X ≤
      rationalQuadraticAlgebraWeightedLRegulatorSum selectedKroneckerLValue X := by
  rw [genuineQuadraticAlgebraClassNumberModel_formClassSum_eq]
  exact properFormClass_sum_le_selectedKronecker_weightedLRegulatorSum X

end
end PellPaper
