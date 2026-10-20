import Pell.QuadraticOrderPellFundamentalUnitComparison
import Pell.FundamentalDiscriminantPellRegulator

/-!
# The concrete fundamental-unit model to Pell-cutoff bridge

`QuadraticOrderPellFundamentalUnitComparison` proves the numerical comparison
`eta ≤ epsilon ≤ eta^6` once a positive rank-one model for the maximal-order
unit group is supplied.  This module feeds that exact comparison into the
existing logarithmic Pell-cutoff bridge for the actual chosen fundamental Pell
solution.  It remains conditional on construction of the unit model itself.
-/

namespace PellPaper

noncomputable section

/-- A concrete positive rank-one maximal-order unit model bounds the actual
Pell-order regulator by six times its normalized logarithm. -/
theorem pellOrderRegulator_le_six_mul_log_div_of_concreteFundamentalUnitRealModel
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ))]
    (model : FundamentalUnitRealModel
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ)))
      (quadraticOrderPellRealEval (D : ℤ)
        (int_pos_of_positiveFundamentalDiscriminant hD).le)) :
    pellOrderRegulator D ≤
      6 * (Real.log model.eta / Real.log (D : ℝ)) := by
  rw [pellOrderRegulator_eq_pellNormalizedLog hD]
  exact pellNormalizedLog_le_six_mul_log_div_of_epsilon_le_pow_six hD
    (fundamentalPellSolution_isFundamental D hD)
    (eta := model.eta) (zero_lt_one.trans model.eta_one_lt)
    (eta_le_epsilon_le_eta_pow_six_of_concreteFundamentalUnitRealModel
      D hD model
      (fundamentalPellSolution_isFundamental D hD)).2

/-- The same concrete model turns a strict normalized maximal-order unit
cutoff directly into the Pell exceptional condition used by the uniform
class-side pipeline. -/
theorem smallFundamentalSolution_regulatorPellExponent_of_concreteFundamentalUnitRealModel_cutoff
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ))]
    (model : FundamentalUnitRealModel
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ)))
      (quadraticOrderPellRealEval (D : ℤ)
        (int_pos_of_positiveFundamentalDiscriminant hD).le))
    (t : ℝ)
    (hcutoff : Real.log model.eta / Real.log (D : ℝ) < t) :
    SmallFundamentalSolution (regulatorPellExponent t) D := by
  exact smallFundamentalSolution_regulatorPellExponent_of_unitComparison hD
    (fundamentalPellSolution_isFundamental D hD)
    (eta := model.eta) (t := t) (zero_lt_one.trans model.eta_one_lt)
    (eta_le_epsilon_le_eta_pow_six_of_concreteFundamentalUnitRealModel
      D hD model
      (fundamentalPellSolution_isFundamental D hD)).2
    hcutoff

end

end PellPaper
