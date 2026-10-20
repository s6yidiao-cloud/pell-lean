import Pell.Main3LargeAnalyticRealCellCoverSelection
import Pell.Main3LargeAnalyticBlockSumExistential
import Pell.Main3LargeAnalyticIntrinsicEliminantSieveUniformLogBudget
import Pell.Main3LargeAnalyticFixedKeyCellIntrinsicSieve
import Mathlib.Tactic

/-!
# Workspace: Main3 real-cell sieve selection

For every active real cell, this file selects the bounded auxiliary factor
and couples it to the already selected same-witness real target cover.  The
Weil estimate remains an explicit reusable proposition premise.
-/

namespace PellPaper

noncomputable section

open Filter

local instance main3LargeAnalyticRealCellSieveSelection_numberField
    (a : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

/-- Nonemptiness of the target-vector projection recovers nonemptiness of
the coordinate-point image from which it was formed. -/
theorem main3LargeAnalytic_realCellCoordinatePointImage_nonempty_of_targetVectorImage_nonempty
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (hnonempty :
      (main3LargeAnalyticFixedKeyCellTargetVectorImage
        htheta hY hi key cell).Nonempty) :
    (main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
      htheta hY hi key cell).Nonempty := by
  obtain ⟨y, hy⟩ := hnonempty
  obtain ⟨z, hz, _hzy⟩ :=
    (mem_main3LargeAnalyticFixedKeyCellTargetVectorImage_iff
      htheta hY hi key cell y).mp hy
  exact ⟨z, hz⟩

/-- Choose one bounded auxiliary-factor package on every active real cell. -/
noncomputable def main3LargeAnalytic_realCellAuxiliaryFactorSelection
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hYgrow : Real.exp (800 * theta ^ 2) < (Y : ℝ))
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : ↑(main3LargeAnalytic_nonemptyRealCellIndices
      htheta hY hi key)) :
    Main3LargeAnalyticFixedKeyCellAuxiliaryFactorData
      htheta hY hi key (Sum.inl cell.1) (main3BalancedDegree theta) := by
  apply Classical.choice
  apply nonempty_main3LargeAnalyticFixedKeyCellAuxiliaryFactorData_of_growth
    htheta hY hYgrow hi key (Sum.inl cell.1)
  apply main3LargeAnalytic_realCellCoordinatePointImage_nonempty_of_targetVectorImage_nonempty
    htheta hY hi key (Sum.inl cell.1)
  exact (mem_main3LargeAnalytic_nonemptyRealCellIndices
    htheta hY hi key cell.1).mp cell.2 |>.2

/-- The selected factor and real cover satisfy the uniform explicit sieve
threshold already proved for the intrinsic eliminant. -/
theorem main3LargeAnalytic_realCell_selectedSieveBudgetThreshold_le
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hYgrow : Real.exp (800 * theta ^ 2) < (Y : ℝ))
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (ha : shiftedSquareA h v < 0)
    (cell : ↑(main3LargeAnalytic_nonemptyRealCellIndices
      htheta hY hi key)) :
    let Q := main3LargeAnalytic_realCellCoverSelection
      htheta hY hi key ha cell
    let data := main3LargeAnalytic_realCellAuxiliaryFactorSelection
      htheta hY hYgrow hi key cell
    main3LargeAnalyticIntrinsicEliminantSieveBudgetThreshold
        data Q.productHeight Q.U Q.V ≤
      128000 * theta ^ 7 * Real.log (Y : ℝ) := by
  dsimp only
  let Q := main3LargeAnalytic_realCellCoverSelection
    htheta hY hi key ha cell
  let data := main3LargeAnalytic_realCellAuxiliaryFactorSelection
    htheta hY hYgrow hi key cell
  have hbudget :=
    main3LargeAnalyticIntrinsicEliminantSieveBudgetThreshold_balancedDegree_le
      htheta hY hi key (Sum.inl cell.1) data
        Q.productHeight Q.U Q.V
        Q.log_productHeight_bound Q.log_scaleSum_bound
  simpa only [Q, data] using hbudget

/-- Uniform thin/full dichotomy for one selected active real cell.  The
additive four covers the thin branch; the full branch retains twice the exact
square-sieve envelope. -/
theorem eventually_card_main3LargeAnalytic_selectedRealCellPointFiber_le
    (hWeil : OneVariableQuadraticWeilDegreeBound)
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hYgrow : Real.exp (800 * theta ^ 2) < (Y : ℝ))
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (hkeyGate : key ∈ main3LargeAnalytic_blockAuxiliaryKeyGate h v)
    (ha : shiftedSquareA h v < 0)
    (cell : ↑(main3LargeAnalytic_nonemptyRealCellIndices
      htheta hY hi key)) :
    let Q := main3LargeAnalytic_realCellCoverSelection
      htheta hY hi key ha cell
    let data := main3LargeAnalytic_realCellAuxiliaryFactorSelection
      htheta hY hYgrow hi key cell
    let d := main3LargeAnalyticIntrinsicEliminantDegree data
    ∀ᶠ sieveN : ℕ in atTop,
      128000 * theta ^ 7 * Real.log (Y : ℝ) ≤ (sieveN : ℝ) →
        ((main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
          htheta hY hi key (Sum.inl cell.1)).card : ℝ) ≤
          2048 * (main3BalancedDegree theta : ℝ) * theta *
              ((shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs.divisors.card : ℝ) +
            4 + 2 * fullCellOddDegreeSieveEnvelope
              sieveN d Q.U Q.V Q.M₀ Q.mu := by
  dsimp only
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let Q := main3LargeAnalytic_realCellCoverSelection
    htheta hY hi key ha cell
  let data := main3LargeAnalytic_realCellAuxiliaryFactorSelection
    htheta hY hYgrow hi key cell
  let d := main3LargeAnalyticIntrinsicEliminantDegree data
  let delta := Q.M₀ / (Q.U * Q.V)
  let Brect := 4 * Q.mu / delta
  have htarget :
      (main3LargeAnalyticFixedKeyCellTargetVectorImage
        htheta hY hi key (Sum.inl cell.1)).Nonempty :=
    (mem_main3LargeAnalytic_nonemptyRealCellIndices
      htheta hY hi key cell.1).mp cell.2 |>.2
  have hcoordinate :=
    main3LargeAnalytic_realCellCoordinatePointImage_nonempty_of_targetVectorImage_nonempty
      htheta hY hi key (Sum.inl cell.1) htarget
  have hentry : PrimitiveWedgeReducedTargetCoverEntryBoundSpec
      (main3LargeAnalyticFixedKeyCellTargetVectorImage
        htheta hY hi key (Sum.inl cell.1))
      Q.cert.ell Q.cert.anchor
      (2 * main3LargeAnalyticFixedKeyTargetScaleUpper Y key)
      ((2 * main3LargeAnalyticFixedKeyTargetScaleUpper Y key /
          (main3UnbalancedM theta Y : ℝ)) /
        Real.sqrt |(NumberField.discr
          (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ)|)
      8
      (main3LargeAnalyticFixedKeyTargetCoordinateRadius
        (shiftedSquareA h v) Y key)
      Q.G Q.H := Q.completion_spec.2
  have hbudget :=
    main3LargeAnalytic_realCell_selectedSieveBudgetThreshold_le
      htheta hY hYgrow hi key ha cell
  have hU : 0 < Q.U := by
    dsimp only [Main3LargeAnalyticRealCellCoverSelectionData.U]
    exact div_pos Q.cert.K_pos (by norm_num)
  have hV : 0 < Q.V := by
    dsimp only [Main3LargeAnalyticRealCellCoverSelectionData.V]
    norm_num
  have hM₀ : 0 < Q.M₀ :=
    (by norm_num : (0 : ℝ) < 5 / 4).trans_le Q.calibration.2.2.1
  have hmu : 0 < Q.mu := Q.mu_pos
  by_cases hthin : Brect < 1
  · filter_upwards [eventually_ge_atTop 4] with sieveN hN
    intro _hscale
    have hthinBound :=
      card_main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber_cast_le_commonFactor_add_four_of_entryBoundSpec
        htheta hY hi key (Sum.inl cell.1) data Q.cert Q.G Q.H hentry
    have hthinBound' :
        ((main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
          htheta hY hi key (Sum.inl cell.1)).card : ℝ) ≤
          2048 * (main3BalancedDegree theta : ℝ) * theta *
              ((shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs.divisors.card : ℝ) +
            4 := by
      apply hthinBound
      simpa only [Brect, delta,
        Main3LargeAnalyticRealCellCoverSelectionData.mu,
        Main3LargeAnalyticRealCellCoverSelectionData.M₀,
        Main3LargeAnalyticRealCellCoverSelectionData.U,
        Main3LargeAnalyticRealCellCoverSelectionData.V,
        Main3LargeAnalyticRealCellCoverSelectionData.rho,
        Main3LargeAnalyticRealCellCoverSelectionData.z,
        Main3LargeAnalyticRealCellCoverSelectionData.beta,
        Q] using hthin
    have henv : 0 ≤ fullCellOddDegreeSieveEnvelope
        sieveN d Q.U Q.V Q.M₀ Q.mu :=
      fullCellOddDegreeSieveEnvelope_nonnegative
        sieveN d Q.U Q.V Q.M₀ Q.mu hN hU hV hM₀ hmu
    linarith
  · have hfull : 1 ≤ Brect := le_of_not_gt hthin
    have hfullEventually :=
      eventually_card_main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber_cast_le_commonFactor_add_twice_fullCellEnvelope_of_entryBoundSpec
        hWeil htheta hY hi key (Sum.inl cell.1) hcoordinate hkeyGate
          data Q.cert Q.G Q.H hentry
    have hfullEventually' : ∀ᶠ sieveN : ℕ in atTop,
        main3LargeAnalyticIntrinsicEliminantSieveBudgetThreshold
            data Q.productHeight Q.U Q.V ≤ (sieveN : ℝ) →
          ((main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
            htheta hY hi key (Sum.inl cell.1)).card : ℝ) ≤
            2048 * (main3BalancedDegree theta : ℝ) * theta *
                ((shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs.divisors.card : ℝ) +
              2 * fullCellOddDegreeSieveEnvelope
                sieveN d Q.U Q.V Q.M₀ Q.mu := by
      have := hfullEventually
      apply this
      simpa only [Brect, delta,
        Main3LargeAnalyticRealCellCoverSelectionData.mu,
        Main3LargeAnalyticRealCellCoverSelectionData.M₀,
        Main3LargeAnalyticRealCellCoverSelectionData.U,
        Main3LargeAnalyticRealCellCoverSelectionData.V,
        Main3LargeAnalyticRealCellCoverSelectionData.rho,
        Main3LargeAnalyticRealCellCoverSelectionData.z,
        Main3LargeAnalyticRealCellCoverSelectionData.beta,
        Q] using hfull
    filter_upwards [hfullEventually'] with sieveN hsieve
    intro hscale
    have hthreshold :
        main3LargeAnalyticIntrinsicEliminantSieveBudgetThreshold
            data Q.productHeight Q.U Q.V ≤ (sieveN : ℝ) :=
      hbudget.trans hscale
    linarith [hsieve hthreshold]

end

end PellPaper
