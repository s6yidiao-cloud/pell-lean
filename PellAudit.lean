import Pell.MainResults

/-! Declaration, definition, and transitive-axiom audit for `paper/main.tex`. -/

#check PellPaper.proper_form_classes_finite
#check PellPaper.field_class_average
#check PellPaper.odd_class_average
#check PellPaper.uniform_exceptional
#check PellPaper.pell_unit_growth_density
#check PellPaper.fixed_power_density

#print PellPaper.PositiveQuadraticOrderDiscriminant
#print PellPaper.properOrderFormClassSum
#print PellPaper.realQuadraticFieldClassSum
#print PellPaper.realQuadraticFieldOddClassSum
#print PellPaper.classAverageScale
#print PellPaper.oddClassAverageScale
#print PellPaper.SmallFundamentalSolution
#print PellPaper.paperExceptionalSet
#print PellPaper.paperPellGrowthBadSet

#print axioms PellPaper.proper_form_classes_finite
#print axioms PellPaper.field_class_average
#print axioms PellPaper.odd_class_average
#print axioms PellPaper.uniform_exceptional
#print axioms PellPaper.pell_unit_growth_density
#print axioms PellPaper.fixed_power_density

#check PellPaper.final_field_class_average
#check PellPaper.final_odd_class_average
#check PellPaper.final_uniform_exceptional
#check PellPaper.final_pell_unit_growth_density
#check PellPaper.final_fixed_power_density
#check PellPaper.realQuadraticFieldOddClassNumber_eq_card_oddOrderClasses

#print axioms PellPaper.final_field_class_average
#print axioms PellPaper.final_odd_class_average
#print axioms PellPaper.final_uniform_exceptional
#print axioms PellPaper.final_pell_unit_growth_density
#print axioms PellPaper.final_fixed_power_density
#print axioms PellPaper.realQuadraticFieldOddClassNumber_eq_card_oddOrderClasses

/-! These literal type challenges fail to elaborate if an endpoint is weakened
or gains a premise. The class-average scales and strict exceptional set are
expanded here so their normalizations participate in the check. The remaining
semantic closure is printed above and reviewed in the paper-to-Lean map. -/

open Filter
open scoped Topology
open PellPaper

example (D : ℕ) (hD : PositiveQuadraticOrderDiscriminant D) :
    Finite (IntegralBinaryQuadraticForm.ProperFormClass (D : ℤ)) :=
  proper_form_classes_finite D hD

example :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 3 ≤ X →
      realQuadraticFieldClassSum X ≤ properOrderFormClassSum X ∧
        properOrderFormClassSum X ≤
          C * (X ^ ((3 : ℝ) / 2) * Real.sqrt (Real.log (Real.log X)) /
            (Real.log X) ^ ((3 : ℝ) / 2)) :=
  field_class_average

example :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 3 ≤ X →
      realQuadraticFieldOddClassSum X ≤
        C * (X ^ ((3 : ℝ) / 2) * Real.sqrt (Real.log (Real.log X)) /
          (Real.log X) ^ 2) :=
  odd_class_average

example :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ᶠ X : ℝ in atTop, ∀ θ : ℝ,
        3 ≤ θ →
        θ ≤ c * Real.sqrt (Real.log X / Real.log (Real.log X)) →
        (((exceptionalSet θ ⌊X⌋₊).filter fun D : ℕ => (D : ℝ) < X).card : ℝ) ≤
          C * X ^ (1 - c / θ ^ 2) := by
  classical
  exact uniform_exceptional

example :
    ∃ c : ℝ, 0 < c ∧
      Tendsto (fun X : ℝ => ((paperPellGrowthBadSet c X).card : ℝ) / X)
        atTop (𝓝 0) :=
  pell_unit_growth_density

example (θ : ℝ) (hθ : 0 < θ) :
    Tendsto (fun X : ℝ =>
      (((exceptionalSet θ ⌊X⌋₊).filter fun D : ℕ => (D : ℝ) < X).card : ℝ) / X)
      atTop (𝓝 0) := by
  classical
  exact fixed_power_density θ hθ
