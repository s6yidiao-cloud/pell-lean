import Pell.QuadraticOrderPellFundamentalUnitModel
import Pell.QuadraticOrderPellFundamentalUnitCutoff

/-!
# The internally scoped fundamental-unit/Pell cutoff bridge

`QuadraticOrderPellFundamentalUnitModel` constructs the positive signed-power
unit model that was an explicit premise of the earlier cutoff bridge.  This
module specializes that bridge to the model selected from Mathlib's
rank-one Dirichlet fundamental system.  The choice is noncomputable, but its
defining positivity and signed-power properties are kernel checked.

This is still only the algebraic regulator-to-Pell transfer.  It supplies no
class-number formula, analytic `L`-value moment, or uniform Pell estimate.
-/

namespace PellPaper

noncomputable section

/-- At a positive fundamental discriminant, the concretely selected
fundamental-unit model bounds the Pell-order regulator by six times its
normalized logarithm, with no caller-supplied model or field-instance premise. -/
theorem pellOrderRegulator_le_six_mul_log_div_of_concreteFundamentalUnitRealModel_at_positiveFundamentalDiscriminant
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) :
    let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
      ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
    pellOrderRegulator D ≤
      6 * (Real.log (concreteFundamentalUnitRealModel D hD).eta /
        Real.log (D : ℝ)) := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  exact pellOrderRegulator_le_six_mul_log_div_of_concreteFundamentalUnitRealModel
    D hD (concreteFundamentalUnitRealModel D hD)

/-- A strict cutoff on the normalized logarithm of the concretely selected
fundamental unit yields the literal Pell exceptional condition, without a
separate model hypothesis. -/
theorem smallFundamentalSolution_regulatorPellExponent_of_concreteFundamentalUnitRealModel_cutoff_at_positiveFundamentalDiscriminant
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) (t : ℝ)
    (hcutoff :
      let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
        ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
      Real.log (concreteFundamentalUnitRealModel D hD).eta /
        Real.log (D : ℝ) < t) :
    SmallFundamentalSolution (regulatorPellExponent t) D := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  exact smallFundamentalSolution_regulatorPellExponent_of_concreteFundamentalUnitRealModel_cutoff
    D hD (concreteFundamentalUnitRealModel D hD) t hcutoff

end

end PellPaper
