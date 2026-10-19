import Pell.Main3LargeAnalyticRealCellSieveAggregate
import Pell.Main3LargeAnalyticElementarySieveEnvelope
import Pell.Main3LargeAnalyticElementaryIntrinsicSieveAt
import Pell.Main3LargeAnalyticElementaryUniformSieveChoice
import Mathlib.Tactic

/-!
# Elementary Main3 real-cell sieve aggregate

This module propagates the unconditional elementary full-cell character-sum
bound through the accepted real-cell geometry.  It is intentionally isolated
from production while the large-analytic branch is reviewed.
-/

namespace PellPaper

open Filter
open scoped BigOperators

noncomputable section

local instance main3LargeAnalyticElementaryRealCellAggregate_numberField
    (a : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

/-- Sum all selected real-cell sieve envelopes using the explicit cell-count,
area, and reciprocal-minimum budgets. -/
theorem sum_main3LargeAnalytic_selectedRealCell_fullCellElementaryEnvelope_le
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hYgrow : Real.exp (800 * theta ^ 2) < (Y : ℝ))
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (ha : shiftedSquareA h v < 0)
    (hnonempty :
      (main3LargeAnalytic_nonemptyRealCellIndices
        htheta hY hi key).Nonempty)
    (sieveN : ℕ) (hsieveN : 4 ≤ sieveN) :
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
    (∑ cell : ↑I,
      let data := main3LargeAnalytic_realCellAuxiliaryFactorSelection
        htheta hY hYgrow hi key cell
      let Q := main3LargeAnalytic_realCellCoverSelection
        htheta hY hi key ha cell
      fullCellElementarySieveEnvelope sieveN
        (main3LargeAnalyticIntrinsicEliminantDegree data)
        Q.U Q.V Q.M₀ Q.mu) ≤
      fullCellElementarySieveVariableAggregateEnvelope
        sieveN (2 * main3BalancedDegree theta + 1)
        (36 * Mmesh * Lscale) (4 * E / (Mmesh * Delta))
        reciprocalBudget := by
  dsimp only
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
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
  let degree : ↑I → ℕ := fun cell =>
    main3LargeAnalyticIntrinsicEliminantDegree
      (main3LargeAnalytic_realCellAuxiliaryFactorSelection
        htheta hY hYgrow hi key cell)
  let Q : (cell : ↑I) →
      Main3LargeAnalyticFixedKeyRealCellCoverSelection
        htheta hY hi key cell.1 ha :=
    fun cell => main3LargeAnalytic_realCellCoverSelection
      htheta hY hi key ha cell
  have hnonempty' := hnonempty
  obtain ⟨cell₀, hcell₀⟩ := hnonempty
  let c₀ : ↑I := ⟨cell₀, by simpa only [I] using hcell₀⟩
  have hE : 0 < E := by
    have htwoE : 0 < 2 * E := by
      simpa only [E, Q] using (Q c₀).cert.R_pos
    linarith
  have hdiscR : (NumberField.discr
      (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ) ≠ 0 := by
    exact_mod_cast NumberField.discr_ne_zero
      (rationalQuadraticAlgebra (-(shiftedSquareA h v)))
  have hDelta : 0 < Delta := by
    dsimp only [Delta]
    exact Real.sqrt_pos.2 (abs_pos.mpr hdiscR)
  have hMmesh : 0 < Mmesh := by
    dsimp only [Mmesh]
    exact_mod_cast (lt_of_lt_of_le (by omega)
      (six_le_main3UnbalancedM htheta hY))
  have hdegree : ∀ cell ∈ (Finset.univ : Finset ↑I),
      degree cell ≤ 2 * main3BalancedDegree theta + 1 := by
    intro cell _hcell
    dsimp only [degree]
    exact main3LargeAnalyticRealIntrinsicEliminantDegree_le_two_mul_add_one
      (main3LargeAnalytic_realCellAuxiliaryFactorSelection
        htheta hY hYgrow hi key cell)
  have hmu : ∀ cell ∈ (Finset.univ : Finset ↑I), 0 < (Q cell).mu := by
    intro cell _hcell
    exact (Q cell).mu_pos
  have hcellCount : ((Finset.univ : Finset ↑I).card : ℝ) ≤
      36 * Mmesh * Lscale := by
    simpa only [Finset.card_univ, Fintype.card_coe, I, Mmesh,
      Lscale, Fscale] using
      card_main3LargeAnalytic_nonemptyRealCellIndices_cast_le
        htheta hY hi key
  have hareaNonneg : 0 ≤ 4 * E / (Mmesh * Delta) := by positivity
  have harea : ∀ cell ∈ (Finset.univ : Finset ↑I),
      (Q cell).U * (Q cell).V / (Q cell).M₀ ≤
        4 * E / (Mmesh * Delta) := by
    intro cell _hcell
    exact (Q cell).area_le_four_scale hE hDelta hMmesh (by rfl)
  have hreciprocal :
      (∑ cell ∈ (Finset.univ : Finset ↑I), 1 / (Q cell).mu) ≤
        reciprocalBudget := by
    simpa only [I, Fscale, E, Delta, Mmesh, K, L, Lscale, H₀,
      reciprocalBudget, Q] using
      sum_main3LargeAnalytic_selectedRealCell_coverMu_le_intrinsicShape
        htheta hY hi key ha hnonempty'
  have haggregate :=
    sum_fullCellElementarySieveEnvelope_le_variableAggregate
      (Finset.univ : Finset ↑I) sieveN
      (2 * main3BalancedDegree theta + 1)
      degree
      (fun cell => (Q cell).U) (fun cell => (Q cell).V)
      (fun cell => (Q cell).M₀) (fun cell => (Q cell).mu)
      (36 * Mmesh * Lscale) (4 * E / (Mmesh * Delta))
      reciprocalBudget hsieveN hdegree hmu hcellCount hareaNonneg harea
        hreciprocal
  simpa only [I, Fscale, E, Delta, Mmesh, K, L, Lscale, H₀,
    reciprocalBudget, degree, Q] using haggregate

/-- A fixed globally valid sieve event bounds one selected active real cell,
with a single statement covering the thin and full branches. -/
theorem FullCellElementaryOddHomogeneousPolynomialSieveAt.card_main3LargeAnalytic_selectedRealCellPointFiber_le_elementary
    {sieveN : ℕ}
    (hsieve : FullCellElementaryOddHomogeneousPolynomialSieveAt sieveN)
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hYgrow : Real.exp (800 * theta ^ 2) < (Y : ℝ))
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (hkeyGate : key ∈ main3LargeAnalytic_blockAuxiliaryKeyGate h v)
    (ha : shiftedSquareA h v < 0)
    (cell : ↑(main3LargeAnalytic_nonemptyRealCellIndices
      htheta hY hi key))
    (hsieveN : 4 ≤ sieveN)
    (hscale :
      128000 * theta ^ 7 * Real.log (Y : ℝ) ≤ (sieveN : ℝ)) :
    let Q := main3LargeAnalytic_realCellCoverSelection
      htheta hY hi key ha cell
    let data := main3LargeAnalytic_realCellAuxiliaryFactorSelection
      htheta hY hYgrow hi key cell
    let d := main3LargeAnalyticIntrinsicEliminantDegree data
    ((main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
      htheta hY hi key (Sum.inl cell.1)).card : ℝ) ≤
      2048 * (main3BalancedDegree theta : ℝ) * theta *
          ((shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs.divisors.card : ℝ) +
        4 + 2 * fullCellElementarySieveEnvelope
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
  · have hthinBound :=
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
    have henv : 0 ≤ fullCellElementarySieveEnvelope
        sieveN d Q.U Q.V Q.M₀ Q.mu :=
      fullCellElementarySieveEnvelope_nonnegative
        sieveN d Q.U Q.V Q.M₀ Q.mu hsieveN hU hV hM₀ hmu
    linarith
  · have hfull : 1 ≤ Brect := le_of_not_gt hthin
    have hthreshold :
        main3LargeAnalyticIntrinsicEliminantSieveBudgetThreshold
            data Q.productHeight Q.U Q.V ≤ (sieveN : ℝ) :=
      hbudget.trans hscale
    have hfullBound :=
      hsieve.card_main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber_cast_le_commonFactor_add_twice_fullCellEnvelope_of_entryBoundSpec
        htheta hY hi key (Sum.inl cell.1) hcoordinate hkeyGate
          data Q.cert Q.G Q.H hentry
    have hfullBound' :
        ((main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
          htheta hY hi key (Sum.inl cell.1)).card : ℝ) ≤
          2048 * (main3BalancedDegree theta : ℝ) * theta *
              ((shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs.divisors.card : ℝ) +
            2 * fullCellElementarySieveEnvelope
              sieveN d Q.U Q.V Q.M₀ Q.mu := by
      apply hfullBound
      · simpa only [Brect, delta,
          Main3LargeAnalyticRealCellCoverSelectionData.mu,
          Main3LargeAnalyticRealCellCoverSelectionData.M₀,
          Main3LargeAnalyticRealCellCoverSelectionData.U,
          Main3LargeAnalyticRealCellCoverSelectionData.V,
          Main3LargeAnalyticRealCellCoverSelectionData.rho,
          Main3LargeAnalyticRealCellCoverSelectionData.z,
          Main3LargeAnalyticRealCellCoverSelectionData.beta,
          Q] using hfull
      · simpa only [
          Main3LargeAnalyticRealCellCoverSelectionData.productHeight,
          Main3LargeAnalyticRealCellCoverSelectionData.U,
          Main3LargeAnalyticRealCellCoverSelectionData.V,
          Main3LargeAnalyticRealCellCoverSelectionData.M₀,
          Main3LargeAnalyticRealCellCoverSelectionData.rho,
          Main3LargeAnalyticRealCellCoverSelectionData.z,
          Main3LargeAnalyticRealCellCoverSelectionData.beta,
          Q] using hthreshold
    linarith

/-- Sum all active real cells at one sieve parameter satisfying the globally
uniform generic square-sieve event. -/
theorem FullCellElementaryOddHomogeneousPolynomialSieveAt.sum_main3LargeAnalytic_selectedRealCellPointFibers_le_elementary
    {sieveN : ℕ}
    (hsieve : FullCellElementaryOddHomogeneousPolynomialSieveAt sieveN)
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hYgrow : Real.exp (800 * theta ^ 2) < (Y : ℝ))
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (hkeyGate : key ∈ main3LargeAnalytic_blockAuxiliaryKeyGate h v)
    (ha : shiftedSquareA h v < 0)
    (hnonempty :
      (main3LargeAnalytic_nonemptyRealCellIndices
        htheta hY hi key).Nonempty)
    (hsieveN : 4 ≤ sieveN)
    (hscale :
      128000 * theta ^ 7 * Real.log (Y : ℝ) ≤ (sieveN : ℝ)) :
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
      (36 * Mmesh * Lscale) * baseCost +
        2 * fullCellElementarySieveVariableAggregateEnvelope
          sieveN (2 * main3BalancedDegree theta + 1)
          (36 * Mmesh * Lscale) (4 * E / (Mmesh * Delta))
          reciprocalBudget := by
  dsimp only
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
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
  let degree : ↑I → ℕ := fun cell =>
    main3LargeAnalyticIntrinsicEliminantDegree
      (main3LargeAnalytic_realCellAuxiliaryFactorSelection
        htheta hY hYgrow hi key cell)
  let Q : (cell : ↑I) →
      Main3LargeAnalyticFixedKeyRealCellCoverSelection
        htheta hY hi key cell.1 ha :=
    fun cell => main3LargeAnalytic_realCellCoverSelection
      htheta hY hi key ha cell
  have hpoint : ∀ cell : ↑I,
      ((main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
        htheta hY hi key (Sum.inl cell.1)).card : ℝ) ≤
        baseCost + 2 * fullCellElementarySieveEnvelope
          sieveN (degree cell) (Q cell).U (Q cell).V
            (Q cell).M₀ (Q cell).mu := by
    intro cell
    simpa only [I, baseCost, degree, Q, add_assoc] using
      hsieve.card_main3LargeAnalytic_selectedRealCellPointFiber_le_elementary
        htheta hY hYgrow hi key hkeyGate ha cell hsieveN hscale
  have hsum :
      (∑ cell : ↑I,
        ((main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
          htheta hY hi key (Sum.inl cell.1)).card : ℝ)) ≤
        (I.card : ℝ) * baseCost +
          2 * (∑ cell : ↑I, fullCellElementarySieveEnvelope
            sieveN (degree cell) (Q cell).U (Q cell).V
              (Q cell).M₀ (Q cell).mu) := by
    calc
      _ ≤ ∑ cell : ↑I,
          (baseCost + 2 * fullCellElementarySieveEnvelope
            sieveN (degree cell) (Q cell).U (Q cell).V
              (Q cell).M₀ (Q cell).mu) := by
        exact Finset.sum_le_sum fun cell _hcell => hpoint cell
      _ = (I.card : ℝ) * baseCost +
          2 * (∑ cell : ↑I, fullCellElementarySieveEnvelope
            sieveN (degree cell) (Q cell).U (Q cell).V
              (Q cell).M₀ (Q cell).mu) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
          Fintype.card_coe]
  have hcard : (I.card : ℝ) ≤ 36 * Mmesh * Lscale := by
    simpa only [I, Mmesh, Lscale, Fscale] using
      card_main3LargeAnalytic_nonemptyRealCellIndices_cast_le
        htheta hY hi key
  have hbaseCost : 0 ≤ baseCost := by
    dsimp only [baseCost]
    positivity
  have henvelopes :=
    sum_main3LargeAnalytic_selectedRealCell_fullCellElementaryEnvelope_le
      htheta hY hYgrow hi key ha hnonempty sieveN hsieveN
  have henvelopes' :
      (∑ cell : ↑I, fullCellElementarySieveEnvelope
        sieveN (degree cell) (Q cell).U (Q cell).V
          (Q cell).M₀ (Q cell).mu) ≤
        fullCellElementarySieveVariableAggregateEnvelope
          sieveN (2 * main3BalancedDegree theta + 1)
          (36 * Mmesh * Lscale) (4 * E / (Mmesh * Delta))
          reciprocalBudget := by
    simpa only [I, Fscale, E, Delta, Mmesh, K, L, Lscale, H₀,
      reciprocalBudget, degree, Q] using henvelopes
  calc
    (∑ cell : ↑I,
      ((main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
        htheta hY hi key (Sum.inl cell.1)).card : ℝ)) ≤
        (I.card : ℝ) * baseCost +
          2 * (∑ cell : ↑I, fullCellElementarySieveEnvelope
            sieveN (degree cell) (Q cell).U (Q cell).V
              (Q cell).M₀ (Q cell).mu) := hsum
    _ ≤ (36 * Mmesh * Lscale) * baseCost +
        2 * fullCellElementarySieveVariableAggregateEnvelope
          sieveN (2 * main3BalancedDegree theta + 1)
          (36 * Mmesh * Lscale) (4 * E / (Mmesh * Delta))
          reciprocalBudget := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right hcard hbaseCost
      · exact mul_le_mul_of_nonneg_left henvelopes' (by norm_num)

/-- At the explicit Main3 sieve scale, the selected real-cell sum obeys the
aggregated envelope uniformly after one cutoff in `Y`; the same package keeps
the moving scale's upper bound for the final power comparison. -/
theorem eventually_main3LargeAnalytic_sum_selectedRealCellPointFibers_at_sieveScale_le_elementary
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
        (_ha : shiftedSquareA h v < 0)
        (_hnonempty :
          (main3LargeAnalytic_nonemptyRealCellIndices
            htheta hY hi key).Nonempty),
        letI : Fact (rationalQuadraticAlgebraNoRationalRoot
          (-(shiftedSquareA h v))) :=
          ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
        let I := main3LargeAnalytic_nonemptyRealCellIndices
          htheta hY hi key
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
            (36 * Mmesh * Lscale) * baseCost +
              2 * fullCellElementarySieveVariableAggregateEnvelope
                (main3LargeAnalyticSieveN theta Y)
                (2 * main3BalancedDegree theta + 1)
                (36 * Mmesh * Lscale) (4 * E / (Mmesh * Delta))
                reciprocalBudget ∧
          (main3LargeAnalyticSieveN theta Y : ℝ) ≤
            2 * (Y : ℝ) ^ (1 / (32 * theta ^ 2)) := by
  filter_upwards
      [eventually_main3LargeAnalytic_uniformElementarySieveChoice c hc hsmall]
      with Y hchoice
  intro theta htheta hadmissible hY h v D N hi key hkeyGate ha hnonempty
  have hpackage := hchoice theta htheta hadmissible
  refine ⟨?_, hpackage.2.2.2.2⟩
  exact hpackage.1.sum_main3LargeAnalytic_selectedRealCellPointFibers_le_elementary
    htheta hY hpackage.2.1 hi key hkeyGate ha hnonempty
      hpackage.2.2.1 hpackage.2.2.2.1


end

end PellPaper

#print axioms PellPaper.sum_main3LargeAnalytic_selectedRealCell_fullCellElementaryEnvelope_le
#print axioms PellPaper.FullCellElementaryOddHomogeneousPolynomialSieveAt.card_main3LargeAnalytic_selectedRealCellPointFiber_le_elementary
#print axioms PellPaper.FullCellElementaryOddHomogeneousPolynomialSieveAt.sum_main3LargeAnalytic_selectedRealCellPointFibers_le_elementary
#print axioms PellPaper.eventually_main3LargeAnalytic_sum_selectedRealCellPointFibers_at_sieveScale_le_elementary
