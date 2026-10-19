import Pell.MaximalOrderFundamentalUnitRegulator
import Pell.FundamentalDiscriminantPellRegulator

/-!
# A uniform lower bound for the selected maximal-order regulator

The concrete maximal-order fundamental-unit model is compared to the
fundamental Pell unit by a factor-six power.  Combining that comparison with
the elementary inequality `sqrt D < epsilon_D` gives a fixed positive lower
bound for its normalized logarithm.  This is only a regulator normalization
fact; it does not provide a class-number formula or analytic estimate.
-/

namespace PellPaper

noncomputable section

/-- At every positive fundamental discriminant, the definition-fixed
maximal-order regulator is strictly larger than `1 / 12`.  The constant is
the elementary `1 / 2` lower bound for the Pell regulator divided by the
factor-six unit comparison. -/
theorem one_div_twelve_lt_maximalOrderFundamentalUnitRegulator
    {D : ℕ} (hD : PositiveFundamentalDiscriminant D) :
    (1 / 12 : ℝ) < maximalOrderFundamentalUnitRegulator D := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  rw [maximalOrderFundamentalUnitRegulator_eq_chosenNormalizedLog hD]
  unfold chosenMaximalOrderFundamentalUnitNormalizedLog
  have hDreal : 1 < (D : ℝ) := by
    exact_mod_cast hD.1
  have hDnonneg : 0 ≤ (D : ℝ) := by linarith
  have hlogD : 0 < Real.log (D : ℝ) := Real.log_pos hDreal
  let a := fundamentalPellSolution D hD
  have ha : Pell.IsFundamental a :=
    fundamentalPellSolution_isFundamental D hD
  have heta : 0 < (concreteFundamentalUnitRealModel D hD).eta := by
    linarith [(concreteFundamentalUnitRealModel D hD).eta_one_lt]
  have hcomparison : epsilon a ≤ (concreteFundamentalUnitRealModel D hD).eta ^ 6 :=
    (concreteFundamentalUnitRealModel_eta_le_epsilon_le_eta_pow_six
      D hD ha).2
  have heps : 0 < epsilon a :=
    epsilon_pos_of_isFundamental_of_positiveFundamentalDiscriminant hD ha
  have hsqrt : 0 < Real.sqrt (D : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hlogsqrt : Real.log (Real.sqrt (D : ℝ)) < Real.log (epsilon a) :=
    Real.log_lt_log hsqrt (sqrt_lt_epsilon ha)
  rw [Real.log_sqrt hDnonneg] at hlogsqrt
  have hloge : Real.log (epsilon a) ≤
      (6 : ℝ) * Real.log (concreteFundamentalUnitRealModel D hD).eta := by
    have h := Real.log_le_log heps hcomparison
    rw [← Real.rpow_natCast, Real.log_rpow heta] at h
    norm_num at h ⊢
    exact h
  apply (lt_div_iff₀ hlogD).mpr
  nlinarith

end

end PellPaper
