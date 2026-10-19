import Pell

/-! Declaration, definition, and transitive-axiom audit for `paper/main.tex`. -/

#check PellPaper.proper_form_classes_finite
#check PellPaper.field_class_average
#check PellPaper.odd_class_average
#check PellPaper.uniform_exceptional
#check PellPaper.pell_unit_growth_density
#check PellPaper.fixed_power_density
#check PellPaper.anisotropic_product_squareSieve
#check PellPaper.anisotropic_sharp_squareSieve
#check PellPaper.uniform_exceptional_doubled_parameter

#print PellPaper.PositiveQuadraticOrderDiscriminant
#print PellPaper.properOrderFormClassSum
#print PellPaper.realQuadraticFieldClassSum
#print PellPaper.realQuadraticFieldOddClassSum
#print PellPaper.classAverageScale
#print PellPaper.oddClassAverageScale
#print PellPaper.SmallFundamentalSolution
#print PellPaper.paperExceptionalSet
#print PellPaper.paperPellGrowthBadSet
#print PellPaper.closedRealRectangle
#print PellPaper.homogeneousRectangleValueHeight
#print PellPaper.doubledParameterLowCover
#print PellPaper.doubledParameterHighBlock

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

#print axioms PellPaper.eventually_oddHomogeneous_rectangle_squareSieve
#print axioms PellPaper.anisotropic_sharp_squareSieve_rectangle
#print axioms PellPaper.anisotropic_sharp_squareSieve_intervals
#print axioms PellPaper.anisotropic_sharp_squareSieve
#print axioms PellPaper.smallFundamentalSolution_doubled_of_sqrt_le
#print axioms PellPaper.doubledParameterLowCover_card_le
#print axioms PellPaper.doubledParameterHighBlock_card_le
#print axioms PellPaper.exceptionalSet_subset_doubledParameter_cover
#print axioms PellPaper.E_le_doubledParameter_geometric
#print axioms PellPaper.uniform_exceptional_doubled_parameter
#print axioms PellPaper.anisotropic_product_squareSieve_rectangle
#print axioms PellPaper.anisotropic_product_squareSieve_intervals
#print axioms PellPaper.anisotropic_product_squareSieve
#print axioms PellPaper.uniform_exceptional_E_doubled_parameter
#print axioms PellPaper.uniformExceptionalEstimate_doubled_parameter

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

/-! Literal source-shaped types for the two added manuscript arguments. -/

example :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (F : MvPolynomial (Fin 2) ℤ) (d : ℕ)
        (a₁ b₁ a₂ b₂ : ℝ),
        F.IsHomogeneous d → Odd d →
        1 ≤ b₂ - a₂ → b₂ - a₂ ≤ b₁ - a₁ →
        C * Real.log (homogeneousRectangleValueHeight F a₁ b₁ a₂ b₂) ≤
          Real.sqrt (b₂ - a₂) →
        (((closedRealRectangle a₁ b₁ a₂ b₂).filter
          (fun xy => MvPolynomial.eval ![xy.1, xy.2] F ≠ 0 ∧
            IsSquare (MvPolynomial.eval ![xy.1, xy.2] F))).card : ℝ) ≤
          K * (Real.log (2 * (b₂ - a₂))) ^ 2 *
            (b₁ - a₁) * Real.sqrt (b₂ - a₂) :=
  anisotropic_sharp_squareSieve

example :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (F : MvPolynomial (Fin 2) ℤ) (d : ℕ)
        (a₁ b₁ a₂ b₂ : ℝ),
        F.IsHomogeneous d → Odd d →
        1 ≤ b₂ - a₂ → b₂ - a₂ ≤ b₁ - a₁ →
        C * Real.log (homogeneousRectangleValueHeight F a₁ b₁ a₂ b₂) ≤
          ((b₁ - a₁) * (b₂ - a₂)) ^ (1 / 4 : ℝ) →
        (((closedRealRectangle a₁ b₁ a₂ b₂).filter
          (fun xy => MvPolynomial.eval ![xy.1, xy.2] F ≠ 0 ∧
            IsSquare (MvPolynomial.eval ![xy.1, xy.2] F))).card : ℝ) ≤
          K * (Real.log (2 * ((b₁ - a₁) * (b₂ - a₂)))) ^ 2 *
            (b₁ - a₁) ^ (5 / 4 : ℝ) * (b₂ - a₂) ^ (1 / 4 : ℝ) := by
  classical
  exact anisotropic_product_squareSieve

example :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ X : ℝ in atTop, ∀ θ : ℝ,
        3 ≤ θ →
        θ ≤ ((1 : ℝ) / 3200) *
          Real.sqrt (Real.log X / Real.log (Real.log X)) →
        (((exceptionalSet θ ⌊X⌋₊).filter fun D : ℕ => (D : ℝ) < X).card : ℝ) ≤
          C * X ^ (1 - ((1 : ℝ) / 3200) / θ ^ 2) := by
  classical
  exact uniform_exceptional_doubled_parameter

example (θ : ℝ) (hθ : 0 < θ) :
    Tendsto (fun X : ℝ =>
      (((exceptionalSet θ ⌊X⌋₊).filter fun D : ℕ => (D : ℝ) < X).card : ℝ) / X)
      atTop (𝓝 0) := by
  classical
  exact fixed_power_density θ hθ

/-! All main results must use the manuscript restoration and sieve proofs. -/

open Lean Elab Command

private def isProjectConstant (n : Name) : Bool :=
  n.toString.startsWith "PellPaper." || n.toString.startsWith "_private.Pell."

private partial def collectRoute (env : Environment) (n : Name) :
    StateM NameSet Unit := do
  if !isProjectConstant n || (← get).contains n then return
  modify fun s => s.insert n
  if let some info := env.find? n then
    for dep in info.type.getUsedConstants do collectRoute env dep
    if let some value := info.value? (allowOpaque := true) then
      for dep in value.getUsedConstants do collectRoute env dep

run_cmd do
  let env := (← getEnv).setExporting false
  let targets := [
    ``PellPaper.field_class_average,
    ``PellPaper.odd_class_average,
    ``PellPaper.uniform_exceptional,
    ``PellPaper.pell_unit_growth_density,
    ``PellPaper.fixed_power_density,
    ``PellPaper.final_field_class_average,
    ``PellPaper.final_odd_class_average,
    ``PellPaper.final_uniform_exceptional,
    ``PellPaper.final_pell_unit_growth_density,
    ``PellPaper.final_fixed_power_density]
  let required := [
    ``PellPaper.smallFundamentalSolution_doubled_of_sqrt_le,
    ``PellPaper.exceptionalSet_subset_doubledParameter_cover,
    ``PellPaper.E_le_doubledParameter_geometric,
    ``PellPaper.eventually_oddHomogeneous_rectangle_squareSieve,
    ``PellPaper.eventually_sum_full_dyadicTarget_eliminant_squareFilters_le_elementary,
    ``PellPaper.eventually_fullCellElementaryOddHomogeneousPolynomialSieveAt]
  let forbiddenNames := [
    "PellPaper.exists_pos_uniform_squarefreeDyadicCoverSum_le_of_main3BlockEstimates",
    "PellPaper.uniformDyadicAllRadicandEstimate_one_div_6400_of_main3BlockEstimates",
    "PellPaper.uniformExceptionalEstimate_one_div_6400_of_main3BlockEstimates",
    "PellPaper.exists_pos_uniform_squarefreeDyadicCoverSum_le_elementary_of_large",
    "PellPaper.uniformDyadicAllRadicandEstimate_one_div_6400_elementary_of_large",
    "PellPaper.uniformExceptionalEstimate_one_div_6400_elementary_of_large",
    "PellPaper.dyadicSquarePartExceptionalCount_le_sum_transferred_add_rpow"]
  for target in targets do
    let deps := ((collectRoute env target).run {}).2
    let missing := required.filter fun n => !deps.contains n
    let forbidden := deps.toArray.filter fun n => forbiddenNames.contains n.toString
    logInfo m!"{target}: {deps.toArray.size} project constants; missing required leaves {missing}; old restoration leaves {forbidden}"
    unless missing.isEmpty && forbidden.isEmpty do
      throwError "Primary proof-route review failed for {target}"
