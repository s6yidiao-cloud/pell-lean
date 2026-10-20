# Fresh integrated type and axiom audit

```text
PellPaper.proper_form_classes_finite (D : ℕ) (hD : PellPaper.PositiveQuadraticOrderDiscriminant D) :
  Finite (PellPaper.IntegralBinaryQuadraticForm.ProperFormClass ↑D)
PellPaper.field_class_average :
  ∃ C,
    0 < C ∧
      ∀ (X : ℝ),
        3 ≤ X →
          PellPaper.realQuadraticFieldClassSum X ≤ PellPaper.properOrderFormClassSum X ∧
            PellPaper.properOrderFormClassSum X ≤ C * PellPaper.classAverageScale X
PellPaper.odd_class_average :
  ∃ C, 0 < C ∧ ∀ (X : ℝ), 3 ≤ X → PellPaper.realQuadraticFieldOddClassSum X ≤ C * PellPaper.oddClassAverageScale X
PellPaper.uniform_exceptional :
  ∃ c C,
    0 < c ∧
      0 < C ∧
        ∀ᶠ (X : ℝ) in Filter.atTop,
          ∀ (θ : ℝ),
            3 ≤ θ →
              θ ≤ c * √(Real.log X / Real.log (Real.log X)) →
                ↑(PellPaper.paperExceptionalCount θ X) ≤ C * X ^ (1 - c / θ ^ 2)
PellPaper.pell_unit_growth_density :
  ∃ c, 0 < c ∧ Filter.Tendsto (fun X => ↑(PellPaper.paperPellGrowthBadSet c X).card / X) Filter.atTop (nhds 0)
PellPaper.fixed_power_density (θ : ℝ) (hθ : 0 < θ) :
  Filter.Tendsto (fun X => ↑(PellPaper.paperExceptionalCount θ X) / X) Filter.atTop (nhds 0)
PellPaper.anisotropic_sharp_squareSieve :
  ∃ C K,
    0 < C ∧
      0 < K ∧
        ∀ (F : MvPolynomial (Fin 2) ℤ) (d : ℕ) (a₁ b₁ a₂ b₂ : ℝ),
          F.IsHomogeneous d →
            Odd d →
              1 ≤ b₂ - a₂ →
                b₂ - a₂ ≤ b₁ - a₁ →
                  C * Real.log (PellPaper.homogeneousRectangleValueHeight F a₁ b₁ a₂ b₂) ≤ √(b₂ - a₂) →
                    ↑{xy ∈ PellPaper.closedRealRectangle a₁ b₁ a₂ b₂ |
                            (MvPolynomial.eval ![xy.1, xy.2]) F ≠ 0 ∧
                              IsSquare ((MvPolynomial.eval ![xy.1, xy.2]) F)}.card ≤
                      K * Real.log (2 * (b₂ - a₂)) ^ 2 * (b₁ - a₁) * √(b₂ - a₂)
PellPaper.uniform_exceptional_doubled_parameter :
  ∃ C,
    0 < C ∧
      ∀ᶠ (X : ℝ) in Filter.atTop,
        ∀ (theta : ℝ),
          3 ≤ theta →
            theta ≤ 1 / 3200 * √(Real.log X / Real.log (Real.log X)) →
              ↑(PellPaper.paperExceptionalCount theta X) ≤ C * X ^ (1 - 1 / 3200 / theta ^ 2)
def PellPaper.PositiveQuadraticOrderDiscriminant : ℕ → Prop :=
fun D => 0 < D ∧ ¬IsSquare D ∧ (D % 4 = 0 ∨ D % 4 = 1)
def PellPaper.properOrderFormClassSum : ℝ → ℝ :=
fun X =>
  ∑ D ∈ PellPaper.orderDiscriminantsBelow X, ↑(Nat.card (PellPaper.IntegralBinaryQuadraticForm.ProperFormClass ↑D))
def PellPaper.realQuadraticFieldClassSum : ℝ → ℝ :=
fun X => ∑ c ∈ PellPaper.realQuadraticFieldClassesBelow X, ↑(PellPaper.realQuadraticFieldClassNumber c)
def PellPaper.realQuadraticFieldOddClassSum : ℝ → ℝ :=
fun X => ∑ K ∈ PellPaper.realQuadraticFieldClassesBelow X, ↑(PellPaper.realQuadraticFieldOddClassNumber K)
def PellPaper.classAverageScale : ℝ → ℝ :=
fun X => X.rpow (3 / 2) * √(Real.log (Real.log X)) / (Real.log X).rpow (3 / 2)
def PellPaper.oddClassAverageScale : ℝ → ℝ :=
fun X => X.rpow (3 / 2) * √(Real.log (Real.log X)) / Real.log X ^ 2
def PellPaper.SmallFundamentalSolution : ℝ → ℕ → Prop :=
fun θ m => ∃ a, Pell.IsFundamental a ∧ PellPaper.epsilon a ≤ ↑m ^ θ
def PellPaper.paperExceptionalSet : ℝ → ℝ → Finset ℕ :=
fun θ X => {D ∈ PellPaper.exceptionalSet θ ⌊X⌋₊ | ↑D < X}
def PellPaper.paperPellGrowthBadSet : ℝ → ℝ → Finset ℕ :=
fun c X =>
  {D ∈ Finset.Icc 1 ⌊X⌋₊ |
    ↑D < X ∧
      ∃ a,
        Pell.IsFundamental a ∧ Real.log (PellPaper.epsilon a) ≤ c * (Real.log ↑D ^ (3 / 2) / √(Real.log (Real.log ↑D)))}
def PellPaper.closedRealRectangle : ℝ → ℝ → ℝ → ℝ → Finset (ℤ × ℤ) :=
fun a₁ b₁ a₂ b₂ => (Finset.Icc ⌈a₁⌉ ⌊b₁⌋).product (Finset.Icc ⌈a₂⌉ ⌊b₂⌋)
def PellPaper.homogeneousRectangleValueHeight : MvPolynomial (Fin 2) ℤ → ℝ → ℝ → ℝ → ℝ → ℝ :=
fun F a₁ b₁ a₂ b₂ =>
  2 + ↑((PellPaper.closedRealRectangle a₁ b₁ a₂ b₂).sup fun xy => ((MvPolynomial.eval ![xy.1, xy.2]) F).natAbs)
def PellPaper.doubledParameterLowCover : ℝ → Finset ℕ :=
fun X => (Finset.Icc 1 ⌊√X⌋₊).biUnion (PellPaper.doubledParameterSquareMultiples X)
def PellPaper.doubledParameterHighBlock : ℝ → ℝ → ℕ → Finset ℕ :=
fun theta X Y =>
  (PellPaper.squarefreeDyadicExceptionalSet (2 * theta) Y).biUnion (PellPaper.doubledParameterSquareMultiples X)
'PellPaper.proper_form_classes_finite' depends on axioms: [propext, Classical.choice, Quot.sound]
'PellPaper.field_class_average' depends on axioms: [propext, Classical.choice, Quot.sound]
'PellPaper.odd_class_average' depends on axioms: [propext, Classical.choice, Quot.sound]
'PellPaper.uniform_exceptional' depends on axioms: [propext, Classical.choice, Quot.sound]
'PellPaper.pell_unit_growth_density' depends on axioms: [propext, Classical.choice, Quot.sound]
'PellPaper.fixed_power_density' depends on axioms: [propext, Classical.choice, Quot.sound]
PellPaper.final_field_class_average : PellPaper.RealQuadraticOrderClassAverageAssertion
PellPaper.final_odd_class_average : PellPaper.RealQuadraticFieldOddClassAverageAssertion
PellPaper.final_uniform_exceptional :
  ∃ c C,
    0 < c ∧
      0 < C ∧
        ∀ᶠ (X : ℝ) in Filter.atTop,
          ∀ (θ : ℝ),
            3 ≤ θ →
              θ ≤ c * √(Real.log X / Real.log (Real.log X)) →
                ↑(PellPaper.paperExceptionalCount θ X) ≤ C * X ^ (1 - c / θ ^ 2)
PellPaper.final_pell_unit_growth_density :
  ∃ c, 0 < c ∧ Filter.Tendsto (fun X => ↑(PellPaper.paperPellGrowthBadSet c X).card / X) Filter.atTop (nhds 0)
PellPaper.final_fixed_power_density (θ : ℝ) (_hθ : 0 < θ) :
  Filter.Tendsto (fun X => ↑(PellPaper.paperExceptionalCount θ X) / X) Filter.atTop (nhds 0)
PellPaper.realQuadraticFieldOddClassNumber_eq_card_oddOrderClasses (K : PellPaper.RealQuadraticFieldClass)
  (F : PellPaper.RealQuadraticField) (hFK : F.toClass = K) :
  PellPaper.realQuadraticFieldOddClassNumber K = Nat.card { c // Odd (orderOf c) }
'PellPaper.final_field_class_average' depends on axioms: [propext, Classical.choice, Quot.sound]
'PellPaper.final_odd_class_average' depends on axioms: [propext, Classical.choice, Quot.sound]
'PellPaper.final_uniform_exceptional' depends on axioms: [propext, Classical.choice, Quot.sound]
'PellPaper.final_pell_unit_growth_density' depends on axioms: [propext, Classical.choice, Quot.sound]
'PellPaper.final_fixed_power_density' depends on axioms: [propext, Classical.choice, Quot.sound]
'PellPaper.realQuadraticFieldOddClassNumber_eq_card_oddOrderClasses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'PellPaper.eventually_oddHomogeneous_rectangle_squareSieve' depends on axioms: [propext, Classical.choice, Quot.sound]
'PellPaper.anisotropic_sharp_squareSieve_rectangle' depends on axioms: [propext, Classical.choice, Quot.sound]
'PellPaper.anisotropic_sharp_squareSieve_intervals' depends on axioms: [propext, Classical.choice, Quot.sound]
'PellPaper.anisotropic_sharp_squareSieve' depends on axioms: [propext, Classical.choice, Quot.sound]
'PellPaper.smallFundamentalSolution_doubled_of_sqrt_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'PellPaper.doubledParameterLowCover_card_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'PellPaper.doubledParameterHighBlock_card_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'PellPaper.exceptionalSet_subset_doubledParameter_cover' depends on axioms: [propext, Classical.choice, Quot.sound]
'PellPaper.E_le_doubledParameter_geometric' depends on axioms: [propext, Classical.choice, Quot.sound]
'PellPaper.uniform_exceptional_doubled_parameter' depends on axioms: [propext, Classical.choice, Quot.sound]
Project proof/type route contains 3862 project constants.
Old arbitrary-radicand endpoint matches: []

```
