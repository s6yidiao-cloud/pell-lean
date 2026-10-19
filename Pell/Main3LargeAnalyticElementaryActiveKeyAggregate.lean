import Pell.Main3LargeAnalyticActiveKeySieveAggregate
import Pell.Main3LargeAnalyticElementaryComplexCellAggregate
import Pell.Main3LargeAnalyticElementaryRealCellAggregate
import Mathlib.Tactic

namespace PellPaper

open Filter
open scoped BigOperators

noncomputable section

local instance main3LargeAnalyticElementaryActiveKeySieveAggregate_numberField
    (a : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

/-- Empty active complex families contribute zero; nonempty ones receive the
moving-scale complex aggregate envelope. -/
theorem eventually_main3LargeAnalytic_sum_selectedComplexCellPointFibers_at_sieveScale_le_ite_elementary
    (c : ℝ) (hc : 0 < c)
    (hsmall : 10 * c ^ 2 ≤ (1 : ℝ) / 2400) :
    ∀ᶠ Y : ℕ in atTop, ∀ theta : ℝ,
      ∀ (htheta : 3 ≤ theta),
      theta ≤ c * Real.sqrt
        (Real.log (Y : ℝ) / Real.log (Real.log (Y : ℝ))) →
      ∀ (hY : 65536 ≤ Y),
      ∀ {h : ℤ} {v D N : ℕ}
        (hi : (h, v, D, N) ∈
          main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
        (key : ShiftedSquareAuxiliaryKey)
        (_hkeyGate : key ∈ main3LargeAnalytic_blockAuxiliaryKeyGate h v)
        (_ha : 0 < shiftedSquareA h v),
        letI : Fact (rationalQuadraticAlgebraNoRationalRoot
          (-(shiftedSquareA h v))) :=
          ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
        let I := main3LargeAnalytic_nonemptyComplexCellIndices
          htheta hY hi key
        let E := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
        let Delta := Real.sqrt
          |(NumberField.discr
            (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ)|
        let Mmesh := (main3UnbalancedM theta Y : ℝ)
        let K := (6 * E / Mmesh) / Delta
        let L := K / 2 + 2
        let H₀ := 2 * Real.sqrt E
        let reciprocalBudget :=
          9216 * Real.sqrt E * (2 + Real.log H₀) *
              (1 + Real.log (2 * L)) +
            663552 * Real.sqrt (E * Mmesh / Delta)
        let baseCost :=
          2048 * (main3BalancedDegree theta : ℝ) * theta *
              ((shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs.divisors.card : ℝ) +
            4
        (∑ cell : ↑I,
          ((main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
            htheta hY hi key (Sum.inr cell.1)).card : ℝ)) ≤
          if I.Nonempty then
            (10 * Mmesh) * baseCost +
              2 * fullCellElementarySieveVariableAggregateEnvelope
                (main3LargeAnalyticSieveN theta Y)
                (2 * main3BalancedDegree theta + 1)
                (10 * Mmesh) (3 * E / (Mmesh * Delta))
                reciprocalBudget
          else 0 := by
  filter_upwards
      [eventually_main3LargeAnalytic_sum_selectedComplexCellPointFibers_at_sieveScale_le_elementary
        c hc hsmall]
      with Y haggregate
  intro theta htheta hadmissible hY h v D N hi key hkeyGate ha
  dsimp only
  let I := main3LargeAnalytic_nonemptyComplexCellIndices htheta hY hi key
  by_cases hI : I.Nonempty
  · have hbound := (haggregate theta htheta hadmissible hY hi key
      hkeyGate ha (by simpa only [I] using hI)).1
    simpa only [I, if_pos hI] using hbound
  · have hIempty : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hI
    have hIfalse : ¬ (main3LargeAnalytic_nonemptyComplexCellIndices
        htheta hY hi key).Nonempty := by simpa only [I] using hI
    rw [if_neg hIfalse]
    have huniv : (Finset.univ : Finset ↑I) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro cell hcell
      exact hI ⟨cell.1, cell.2⟩
    rw [← Finset.sum_attach]
    rw [Finset.attach_eq_univ, huniv]
    simp

/-- Empty active real families contribute zero; nonempty ones receive the
moving-scale real aggregate envelope. -/
theorem eventually_main3LargeAnalytic_sum_selectedRealCellPointFibers_at_sieveScale_le_ite_elementary
    (c : ℝ) (hc : 0 < c)
    (hsmall : 10 * c ^ 2 ≤ (1 : ℝ) / 2400) :
    ∀ᶠ Y : ℕ in atTop, ∀ theta : ℝ,
      ∀ (htheta : 3 ≤ theta),
      theta ≤ c * Real.sqrt
        (Real.log (Y : ℝ) / Real.log (Real.log (Y : ℝ))) →
      ∀ (hY : 65536 ≤ Y),
      ∀ {h : ℤ} {v D N : ℕ}
        (hi : (h, v, D, N) ∈
          main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
        (key : ShiftedSquareAuxiliaryKey)
        (_hkeyGate : key ∈ main3LargeAnalytic_blockAuxiliaryKeyGate h v)
        (_ha : shiftedSquareA h v < 0),
        letI : Fact (rationalQuadraticAlgebraNoRationalRoot
          (-(shiftedSquareA h v))) :=
          ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
        let I := main3LargeAnalytic_nonemptyRealCellIndices htheta hY hi key
        let Fscale := shiftedSquareEmbeddingScaleLoss (shiftedSquareA h v)
        let E := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
        let Delta := Real.sqrt
          |(NumberField.discr
            (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ)|
        let Mmesh := (main3UnbalancedM theta Y : ℝ)
        let K := (2 * E / Mmesh) / Delta
        let L := K / 2 + 5
        let Lscale := (annularDyadicScaleCount Fscale : ℝ)
        let H₀ := 144 * Real.sqrt E
        let reciprocalBudget :=
          38880000 * Lscale * Real.sqrt E * (2 + Real.log H₀) *
              (1 + Real.log (2 * L)) +
            201553920000 * Lscale * Real.sqrt (E * Mmesh / Delta)
        let baseCost :=
          2048 * (main3BalancedDegree theta : ℝ) * theta *
              ((shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs.divisors.card : ℝ) +
            4
        (∑ cell : ↑I,
          ((main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
            htheta hY hi key (Sum.inl cell.1)).card : ℝ)) ≤
          if I.Nonempty then
            (36 * Mmesh * Lscale) * baseCost +
              2 * fullCellElementarySieveVariableAggregateEnvelope
                (main3LargeAnalyticSieveN theta Y)
                (2 * main3BalancedDegree theta + 1)
                (36 * Mmesh * Lscale) (4 * E / (Mmesh * Delta))
                reciprocalBudget
          else 0 := by
  filter_upwards
      [eventually_main3LargeAnalytic_sum_selectedRealCellPointFibers_at_sieveScale_le_elementary
        c hc hsmall]
      with Y haggregate
  intro theta htheta hadmissible hY h v D N hi key hkeyGate ha
  dsimp only
  let I := main3LargeAnalytic_nonemptyRealCellIndices htheta hY hi key
  by_cases hI : I.Nonempty
  · have hbound := (haggregate theta htheta hadmissible hY hi key
      hkeyGate ha (by simpa only [I] using hI)).1
    simpa only [I, if_pos hI] using hbound
  · have hIempty : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hI
    have hIfalse : ¬ (main3LargeAnalytic_nonemptyRealCellIndices
        htheta hY hi key).Nonempty := by simpa only [I] using hI
    rw [if_neg hIfalse]
    have huniv : (Finset.univ : Finset ↑I) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro cell hcell
      exact hI ⟨cell.1, cell.2⟩
    rw [← Finset.sum_attach]
    rw [Finset.attach_eq_univ, huniv]
    simp

/-- Exact positive-shift block partition followed by the empty-aware complex
key envelope, ready for the outer auxiliary-key summation. -/
theorem eventually_main3LargeAnalytic_positiveShift_block_cast_le_sum_ite_complexEnvelopes_elementary
    (c : ℝ) (hc : 0 < c)
    (hsmall : 10 * c ^ 2 ≤ (1 : ℝ) / 2400) :
    ∀ᶠ Y : ℕ in atTop, ∀ theta : ℝ,
      ∀ (htheta : 3 ≤ theta),
      theta ≤ c * Real.sqrt
        (Real.log (Y : ℝ) / Real.log (Real.log (Y : ℝ))) →
      ∀ (hY : 65536 ≤ Y),
      ∀ {h : ℤ} {v D N : ℕ}
        (hi : (h, v, D, N) ∈
          main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
        (_ha : 0 < shiftedSquareA h v),
        letI : Fact (rationalQuadraticAlgebraNoRationalRoot
          (-(shiftedSquareA h v))) :=
          ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
        ((squarefreeShiftedSquareBlock
          (shiftedSquareA h v) D Y N).card : ℝ) ≤
          ∑ key ∈ main3LargeAnalytic_blockAuxiliaryKeyGate h v,
            let I := main3LargeAnalytic_nonemptyComplexCellIndices
              htheta hY hi key
            let E := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
            let Delta := Real.sqrt
              |(NumberField.discr
                (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ)|
            let Mmesh := (main3UnbalancedM theta Y : ℝ)
            let K := (6 * E / Mmesh) / Delta
            let L := K / 2 + 2
            let H₀ := 2 * Real.sqrt E
            let reciprocalBudget :=
              9216 * Real.sqrt E * (2 + Real.log H₀) *
                  (1 + Real.log (2 * L)) +
                663552 * Real.sqrt (E * Mmesh / Delta)
            let baseCost :=
              2048 * (main3BalancedDegree theta : ℝ) * theta *
                  ((shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs.divisors.card : ℝ) +
                4
            if I.Nonempty then
              (10 * Mmesh) * baseCost +
                2 * fullCellElementarySieveVariableAggregateEnvelope
                  (main3LargeAnalyticSieveN theta Y)
                  (2 * main3BalancedDegree theta + 1)
                  (10 * Mmesh) (3 * E / (Mmesh * Delta))
                  reciprocalBudget
            else 0 := by
  filter_upwards
      [eventually_main3LargeAnalytic_sum_selectedComplexCellPointFibers_at_sieveScale_le_ite_elementary
        c hc hsmall]
      with Y hkeyBound
  intro theta htheta hadmissible hY h v D N hi ha
  rw [card_main3LargeAnalytic_block_eq_sum_auxiliaryKeys_nonemptyComplexCells_of_shift_pos
    htheta hY hi ha]
  push_cast
  apply Finset.sum_le_sum
  intro key hkey
  exact hkeyBound theta htheta hadmissible hY hi key hkey ha

/-- Exact negative-shift block partition followed by the empty-aware real key
envelope, ready for the outer auxiliary-key summation. -/
theorem eventually_main3LargeAnalytic_negativeShift_block_cast_le_sum_ite_realEnvelopes_elementary
    (c : ℝ) (hc : 0 < c)
    (hsmall : 10 * c ^ 2 ≤ (1 : ℝ) / 2400) :
    ∀ᶠ Y : ℕ in atTop, ∀ theta : ℝ,
      ∀ (htheta : 3 ≤ theta),
      theta ≤ c * Real.sqrt
        (Real.log (Y : ℝ) / Real.log (Real.log (Y : ℝ))) →
      ∀ (hY : 65536 ≤ Y),
      ∀ {h : ℤ} {v D N : ℕ}
        (hi : (h, v, D, N) ∈
          main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
        (_ha : shiftedSquareA h v < 0),
        letI : Fact (rationalQuadraticAlgebraNoRationalRoot
          (-(shiftedSquareA h v))) :=
          ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
        ((squarefreeShiftedSquareBlock
          (shiftedSquareA h v) D Y N).card : ℝ) ≤
          ∑ key ∈ main3LargeAnalytic_blockAuxiliaryKeyGate h v,
            let I := main3LargeAnalytic_nonemptyRealCellIndices
              htheta hY hi key
            let Fscale := shiftedSquareEmbeddingScaleLoss
              (shiftedSquareA h v)
            let E := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
            let Delta := Real.sqrt
              |(NumberField.discr
                (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ)|
            let Mmesh := (main3UnbalancedM theta Y : ℝ)
            let K := (2 * E / Mmesh) / Delta
            let L := K / 2 + 5
            let Lscale := (annularDyadicScaleCount Fscale : ℝ)
            let H₀ := 144 * Real.sqrt E
            let reciprocalBudget :=
              38880000 * Lscale * Real.sqrt E * (2 + Real.log H₀) *
                  (1 + Real.log (2 * L)) +
                201553920000 * Lscale * Real.sqrt (E * Mmesh / Delta)
            let baseCost :=
              2048 * (main3BalancedDegree theta : ℝ) * theta *
                  ((shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs.divisors.card : ℝ) +
                4
            if I.Nonempty then
              (36 * Mmesh * Lscale) * baseCost +
                2 * fullCellElementarySieveVariableAggregateEnvelope
                  (main3LargeAnalyticSieveN theta Y)
                  (2 * main3BalancedDegree theta + 1)
                  (36 * Mmesh * Lscale) (4 * E / (Mmesh * Delta))
                  reciprocalBudget
            else 0 := by
  filter_upwards
      [eventually_main3LargeAnalytic_sum_selectedRealCellPointFibers_at_sieveScale_le_ite_elementary
        c hc hsmall]
      with Y hkeyBound
  intro theta htheta hadmissible hY h v D N hi ha
  rw [card_main3LargeAnalytic_block_eq_sum_auxiliaryKeys_nonemptyRealCells_of_shift_neg
    htheta hY hi ha]
  push_cast
  apply Finset.sum_le_sum
  intro key hkey
  exact hkeyBound theta htheta hadmissible hY hi key hkey ha


end

end PellPaper

#print axioms PellPaper.eventually_main3LargeAnalytic_positiveShift_block_cast_le_sum_ite_complexEnvelopes_elementary
#print axioms PellPaper.eventually_main3LargeAnalytic_negativeShift_block_cast_le_sum_ite_realEnvelopes_elementary
