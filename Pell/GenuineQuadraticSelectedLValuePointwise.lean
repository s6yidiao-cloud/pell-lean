import Pell.GenuineQuadraticAlgebraClassNumberModel
import Pell.QuadraticSelectedLValueNormalizedRegulator

/-!
# The genuine class model's proved Cauchy pointwise comparison

This is the actual form-class coordinate of the genuine model, with the
proved normalized regulator and the explicitly scaled weight `4 * L`.
The estimate holds for every real cutoff and every discriminant in its
strict-cutoff family, exactly as required by `ClassAverageCauchyInputs`.
No moment or exceptional-cardinality premise is used.
-/

namespace PellPaper

noncomputable section

/-- The genuine model's Cauchy pointwise field is supplied by actual
arithmetic, with `L D = 4 * selectedKroneckerLValue D` and the actual selected
normalized maximal-order regulator. -/
theorem genuineQuadraticAlgebraClassNumberModel_pointwise_selectedLValue_normalizedRegulator
    (X : ℝ) (D : ℕ) (hDX : D ∈ fundamentalDiscriminantsBelow X) :
    (genuineQuadraticAlgebraClassNumberModel.formClassNumber D : ℝ) ≤
      (Real.sqrt X / Real.log X) *
        ((4 * selectedKroneckerLValue D) / maximalOrderFundamentalUnitRegulator D) := by
  rw [genuineQuadraticAlgebraClassNumberModel_form_eq
    (mem_fundamentalDiscriminantsBelow.mp hDX).1]
  exact properFormClass_card_le_cutoff_selectedLValue_div_normalizedRegulator X D hDX

end
end PellPaper
