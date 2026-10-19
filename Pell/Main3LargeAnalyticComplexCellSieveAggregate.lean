import Pell.Main3LargeAnalyticComplexShortVectorBandIncidence
import Pell.Main3LargeAnalyticComplexCellSieveSelection
import Pell.Main3LargeAnalyticVariableCellEnvelopeSum
import Pell.Main3LargeAnalyticUniformIntrinsicSieveAt
import Pell.Main3LargeAnalyticUniformSieveChoice
import Mathlib.Tactic

/-!
# Main3 complex-cell sieve aggregate

This file sums the selected full-cell square-sieve envelopes over the active
complex mesh.  It keeps the exact cell-dependent covers, but replaces their
total area and reciprocal minima by the proved intrinsic budgets.
-/

namespace PellPaper

open Filter
open scoped BigOperators

noncomputable section

local instance main3LargeAnalyticComplexCellSieveAggregate_numberField
    (a : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

/-- The literal residual eliminant degree is at most twice the selected
auxiliary degree plus one. -/
theorem main3LargeAnalyticIntrinsicEliminantDegree_le_two_mul_add_one
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N B : ℕ}
    {htheta : 3 ≤ theta} {hY : 65536 ≤ Y}
    {hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y}
    {key : ShiftedSquareAuxiliaryKey}
    {cell : Main3LargeAnalyticArchimedeanCellIndex}
    (data : Main3LargeAnalyticFixedKeyCellAuxiliaryFactorData
      htheta hY hi key cell B) :
    main3LargeAnalyticIntrinsicEliminantDegree data ≤ 2 * B + 1 := by
  dsimp only [main3LargeAnalyticIntrinsicEliminantDegree]
  have hresidual : data.residualDegree ≤ B := by
    have hsplit := data.degree_split
    omega
  omega

/-- The number of active complex cells is bounded by ten times the mesh
parameter. -/
theorem card_main3LargeAnalytic_nonemptyComplexCellIndices_cast_le_ten_mul
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey) :
    ((main3LargeAnalytic_nonemptyComplexCellIndices
      htheta hY hi key).card : ℝ) ≤
        10 * (main3UnbalancedM theta Y : ℝ) := by
  have hcard := card_main3LargeAnalytic_nonemptyComplexCellIndices_le
    htheta hY hi key
  have hM : 6 ≤ main3UnbalancedM theta Y :=
    six_le_main3UnbalancedM htheta hY
  have hfinal :
    (main3LargeAnalytic_nonemptyComplexCellIndices
      htheta hY hi key).card ≤ 10 * main3UnbalancedM theta Y := by
    omega
  exact_mod_cast hfinal

/-- Each selected complex cover has normalized rectangle-area scale at most
`3E/(M Delta)`. -/
theorem Main3LargeAnalyticComplexCellCoverSelectionData.area_le_three_scale
    {T : Finset (Fin 2 → ℤ)} {omega : ℂ}
    {E Delta Mmesh K T₀ A Y : ℝ}
    (Q : Main3LargeAnalyticComplexCellCoverSelectionData
      T omega E Delta Mmesh K T₀ A Y)
    (hE : 0 < E) (hDelta : 0 < Delta) (hMmesh : 0 < Mmesh)
    (hK : K = (6 * E / Mmesh) / Delta) :
    Q.U * Q.V / Q.M₀ ≤ 3 * E / (Mmesh * Delta) := by
  have hM₀ : 2 ≤ Q.M₀ := Q.calibration.2.2.1
  have hM₀pos : 0 < Q.M₀ := zero_lt_two.trans_le hM₀
  have hKpos : 0 < K := by rw [hK]; positivity
  have hUV : Q.U * Q.V = K := by
    dsimp only [Main3LargeAnalyticComplexCellCoverSelectionData.U,
      Main3LargeAnalyticComplexCellCoverSelectionData.V]
    ring
  calc
    Q.U * Q.V / Q.M₀ = K / Q.M₀ := by rw [hUV]
    _ ≤ K / 2 := by
      exact div_le_div_of_nonneg_left hKpos.le (by norm_num) hM₀
    _ = 3 * E / (Mmesh * Delta) := by
      rw [hK]
      field_simp [hMmesh.ne', hDelta.ne']
      ring

/-- Summing the actual selected complex-cover areas over all active cells
costs at most `30E/Delta`; the mesh factor cancels. -/
theorem sum_main3LargeAnalytic_selectedComplexCell_area_le
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (ha : 0 < shiftedSquareA h v)
    (hnonempty :
      (main3LargeAnalytic_nonemptyComplexCellIndices
        htheta hY hi key).Nonempty) :
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    let E := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
    let Delta := Real.sqrt
      |(NumberField.discr
        (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ)|
    (∑ cell : ↑(main3LargeAnalytic_nonemptyComplexCellIndices
        htheta hY hi key),
      let Q := main3LargeAnalytic_complexCellCoverSelection
        htheta hY hi key ha cell
      Q.U * Q.V / Q.M₀) ≤ 30 * E / Delta := by
  dsimp only
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let I := main3LargeAnalytic_nonemptyComplexCellIndices htheta hY hi key
  let E := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
  let Delta := Real.sqrt
    |(NumberField.discr
      (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ)|
  let Mmesh := (main3UnbalancedM theta Y : ℝ)
  obtain ⟨cell₀, hcell₀⟩ := hnonempty
  let c₀ : ↑I := ⟨cell₀, by simpa only [I] using hcell₀⟩
  let Q₀ := main3LargeAnalytic_complexCellCoverSelection
    htheta hY hi key ha c₀
  have hE : 0 < E := by simpa only [E] using Q₀.cert.R_pos
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
  have hpoint : ∀ cell : ↑I,
      let Q := main3LargeAnalytic_complexCellCoverSelection
        htheta hY hi key ha cell
      Q.U * Q.V / Q.M₀ ≤ 3 * E / (Mmesh * Delta) := by
    intro cell
    let Q := main3LargeAnalytic_complexCellCoverSelection
      htheta hY hi key ha cell
    exact Q.area_le_three_scale hE hDelta hMmesh (by rfl)
  have hsum :
      (∑ cell : ↑I,
        let Q := main3LargeAnalytic_complexCellCoverSelection
          htheta hY hi key ha cell
        Q.U * Q.V / Q.M₀) ≤
        (I.card : ℝ) * (3 * E / (Mmesh * Delta)) := by
    calc
      _ ≤ ∑ _cell : ↑I, (3 * E / (Mmesh * Delta)) := by
        exact Finset.sum_le_sum fun cell _hcell => hpoint cell
      _ = (I.card : ℝ) * (3 * E / (Mmesh * Delta)) := by simp
  have hcard : (I.card : ℝ) ≤ 10 * Mmesh := by
    simpa only [I, Mmesh] using
      card_main3LargeAnalytic_nonemptyComplexCellIndices_cast_le_ten_mul
        htheta hY hi key
  calc
    (∑ cell : ↑I,
      let Q := main3LargeAnalytic_complexCellCoverSelection
        htheta hY hi key ha cell
      Q.U * Q.V / Q.M₀) ≤
        (I.card : ℝ) * (3 * E / (Mmesh * Delta)) := hsum
    _ ≤ (10 * Mmesh) * (3 * E / (Mmesh * Delta)) := by
      gcongr
    _ = 30 * E / Delta := by
      field_simp [hMmesh.ne', hDelta.ne']
      ring

/-- On an active cell, the globally extended reciprocal minimum is exactly
the minimum stored in that cell's selected cover. -/
theorem main3LargeAnalytic_selectedComplexCellMu_eq_coverSelection_mu
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (ha : 0 < shiftedSquareA h v)
    (cell : ↑(main3LargeAnalytic_nonemptyComplexCellIndices
      htheta hY hi key)) :
    main3LargeAnalytic_selectedComplexCellMu
        htheta hY hi key ha cell.1 =
      (main3LargeAnalytic_complexCellCoverSelection
        htheta hY hi key ha cell).mu := by
  simp only [main3LargeAnalytic_selectedComplexCellMu, dif_pos cell.2]

/-- The intrinsic-shape reciprocal-minimum bound can be read directly as a
sum over the selected active-cell subtype. -/
theorem sum_main3LargeAnalytic_selectedComplexCell_coverMu_le_intrinsicShape
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (ha : 0 < shiftedSquareA h v)
    (hnonempty :
      (main3LargeAnalytic_nonemptyComplexCellIndices
        htheta hY hi key).Nonempty) :
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    let E := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
    let Delta := Real.sqrt
      |(NumberField.discr
        (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ)|
    let K := (6 * E / (main3UnbalancedM theta Y : ℝ)) / Delta
    let L := K / 2 + 2
    let H₀ := 2 * Real.sqrt E
    (∑ cell : ↑(main3LargeAnalytic_nonemptyComplexCellIndices
        htheta hY hi key),
      1 / (main3LargeAnalytic_complexCellCoverSelection
        htheta hY hi key ha cell).mu) ≤
      9216 * Real.sqrt E * (2 + Real.log H₀) *
          (1 + Real.log (2 * L)) +
        663552 * Real.sqrt
          (E * (main3UnbalancedM theta Y : ℝ) / Delta) := by
  dsimp only
  have hsum :=
    sum_main3LargeAnalytic_nonemptyComplexCell_reciprocalMinimum_le_intrinsicShape
      htheta hY hi key ha hnonempty
  rw [← Finset.sum_attach] at hsum
  rw [Finset.attach_eq_univ] at hsum
  simpa only [main3LargeAnalytic_selectedComplexCellMu_eq_coverSelection_mu]
    using hsum

/-- Sum all selected complex-cell sieve envelopes using the literal area
and reciprocal-minimum budgets.  The returned expression is the generic
variable-cell aggregate with fully explicit Main3 inputs. -/
theorem sum_main3LargeAnalytic_selectedComplexCell_fullCellEnvelope_le
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hYgrow : Real.exp (800 * theta ^ 2) < (Y : ℝ))
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (ha : 0 < shiftedSquareA h v)
    (hnonempty :
      (main3LargeAnalytic_nonemptyComplexCellIndices
        htheta hY hi key).Nonempty)
    (sieveN : ℕ) (hsieveN : 4 ≤ sieveN) :
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    let I := main3LargeAnalytic_nonemptyComplexCellIndices htheta hY hi key
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
    (∑ cell : ↑I,
      let data := main3LargeAnalytic_complexCellAuxiliaryFactorSelection
        htheta hY hYgrow hi key cell
      let Q := main3LargeAnalytic_complexCellCoverSelection
        htheta hY hi key ha cell
      fullCellOddDegreeSieveEnvelope sieveN
        (main3LargeAnalyticIntrinsicEliminantDegree data)
        Q.U Q.V Q.M₀ Q.mu) ≤
      fullCellOddDegreeSieveVariableAggregateEnvelope
        sieveN (2 * main3BalancedDegree theta + 1)
        (10 * Mmesh) (3 * E / (Mmesh * Delta)) reciprocalBudget := by
  dsimp only
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let I := main3LargeAnalytic_nonemptyComplexCellIndices htheta hY hi key
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
  let degree : ↑I → ℕ := fun cell =>
    main3LargeAnalyticIntrinsicEliminantDegree
      (main3LargeAnalytic_complexCellAuxiliaryFactorSelection
        htheta hY hYgrow hi key cell)
  let Q : (cell : ↑I) →
      Main3LargeAnalyticFixedKeyComplexCellCoverSelection
        htheta hY hi key cell.1 ha :=
    fun cell => main3LargeAnalytic_complexCellCoverSelection
      htheta hY hi key ha cell
  have hnonempty' := hnonempty
  obtain ⟨cell₀, hcell₀⟩ := hnonempty
  let c₀ : ↑I := ⟨cell₀, by simpa only [I] using hcell₀⟩
  have hE : 0 < E := by simpa only [E, Q] using (Q c₀).cert.R_pos
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
    exact main3LargeAnalyticIntrinsicEliminantDegree_le_two_mul_add_one
      (main3LargeAnalytic_complexCellAuxiliaryFactorSelection
        htheta hY hYgrow hi key cell)
  have hmu : ∀ cell ∈ (Finset.univ : Finset ↑I), 0 < (Q cell).mu := by
    intro cell _hcell
    exact (Q cell).mu_pos
  have hcellCount : ((Finset.univ : Finset ↑I).card : ℝ) ≤
      10 * Mmesh := by
    simpa only [Finset.card_univ, Fintype.card_coe, I, Mmesh] using
      card_main3LargeAnalytic_nonemptyComplexCellIndices_cast_le_ten_mul
        htheta hY hi key
  have hareaNonneg : 0 ≤ 3 * E / (Mmesh * Delta) := by positivity
  have harea : ∀ cell ∈ (Finset.univ : Finset ↑I),
      (Q cell).U * (Q cell).V / (Q cell).M₀ ≤
        3 * E / (Mmesh * Delta) := by
    intro cell _hcell
    exact (Q cell).area_le_three_scale hE hDelta hMmesh (by rfl)
  have hreciprocal :
      (∑ cell ∈ (Finset.univ : Finset ↑I), 1 / (Q cell).mu) ≤
        reciprocalBudget := by
    simpa only [I, E, Delta, Mmesh, K, L, H₀, reciprocalBudget, Q] using
      sum_main3LargeAnalytic_selectedComplexCell_coverMu_le_intrinsicShape
        htheta hY hi key ha hnonempty'
  have haggregate :=
    sum_fullCellOddDegreeSieveEnvelope_le_variableAggregate
      (Finset.univ : Finset ↑I) sieveN
      (2 * main3BalancedDegree theta + 1)
      degree
      (fun cell => (Q cell).U) (fun cell => (Q cell).V)
      (fun cell => (Q cell).M₀) (fun cell => (Q cell).mu)
      (10 * Mmesh) (3 * E / (Mmesh * Delta)) reciprocalBudget
      hsieveN hdegree hmu hcellCount hareaNonneg harea hreciprocal
  simpa only [I, E, Delta, Mmesh, K, L, H₀, reciprocalBudget, degree, Q]
    using haggregate

/-- A fixed globally valid sieve event bounds the selected active complex
cell, with one statement covering both the thin and full branches. -/
theorem FullCellOddHomogeneousPolynomialSieveAt.card_main3LargeAnalytic_selectedComplexCellPointFiber_le
    {sieveN : ℕ}
    (hsieve : FullCellOddHomogeneousPolynomialSieveAt sieveN)
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hYgrow : Real.exp (800 * theta ^ 2) < (Y : ℝ))
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (hkeyGate : key ∈ main3LargeAnalytic_blockAuxiliaryKeyGate h v)
    (ha : 0 < shiftedSquareA h v)
    (cell : ↑(main3LargeAnalytic_nonemptyComplexCellIndices
      htheta hY hi key))
    (hsieveN : 4 ≤ sieveN)
    (hscale :
      128000 * theta ^ 7 * Real.log (Y : ℝ) ≤ (sieveN : ℝ)) :
    let Q := main3LargeAnalytic_complexCellCoverSelection
      htheta hY hi key ha cell
    let data := main3LargeAnalytic_complexCellAuxiliaryFactorSelection
      htheta hY hYgrow hi key cell
    let d := main3LargeAnalyticIntrinsicEliminantDegree data
    ((main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
      htheta hY hi key (Sum.inr cell.1)).card : ℝ) ≤
      2048 * (main3BalancedDegree theta : ℝ) * theta *
          ((shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs.divisors.card : ℝ) +
        4 + 2 * fullCellOddDegreeSieveEnvelope
          sieveN d Q.U Q.V Q.M₀ Q.mu := by
  dsimp only
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let Q := main3LargeAnalytic_complexCellCoverSelection
    htheta hY hi key ha cell
  let data := main3LargeAnalytic_complexCellAuxiliaryFactorSelection
    htheta hY hYgrow hi key cell
  let d := main3LargeAnalyticIntrinsicEliminantDegree data
  let delta := Q.M₀ / (Q.U * Q.V)
  let Brect := 4 * Q.mu / delta
  have htarget :
      (main3LargeAnalyticFixedKeyCellTargetVectorImage
        htheta hY hi key (Sum.inr cell.1)).Nonempty :=
    (mem_main3LargeAnalytic_nonemptyComplexCellIndices
      htheta hY hi key cell.1).mp cell.2 |>.2
  have hcoordinate :=
    main3LargeAnalytic_coordinatePointImage_nonempty_of_targetVectorImage_nonempty
      htheta hY hi key (Sum.inr cell.1) htarget
  have hentry : PrimitiveWedgeReducedTargetCoverEntryBoundSpec
      (main3LargeAnalyticFixedKeyCellTargetVectorImage
        htheta hY hi key (Sum.inr cell.1))
      Q.cert.ell Q.cert.anchor
      (main3LargeAnalyticFixedKeyTargetScaleUpper Y key)
      ((6 * main3LargeAnalyticFixedKeyTargetScaleUpper Y key /
          (main3UnbalancedM theta Y : ℝ)) /
        Real.sqrt |(NumberField.discr
          (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ)|)
      2
      (main3LargeAnalyticFixedKeyTargetCoordinateRadius
        (shiftedSquareA h v) Y key)
      Q.G Q.H := Q.completion_spec.2
  have hbudget :=
    main3LargeAnalytic_complexCell_selectedSieveBudgetThreshold_le
      htheta hY hYgrow hi key ha cell
  have hU : 0 < Q.U := by
    dsimp only [Main3LargeAnalyticComplexCellCoverSelectionData.U]
    exact div_pos Q.cert.K_pos (by norm_num)
  have hV : 0 < Q.V := by
    dsimp only [Main3LargeAnalyticComplexCellCoverSelectionData.V]
    norm_num
  have hM₀ : 0 < Q.M₀ :=
    zero_lt_two.trans_le Q.calibration.2.2.1
  have hmu : 0 < Q.mu := Q.mu_pos
  by_cases hthin : Brect < 1
  · have hthinBound :=
      card_main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber_cast_le_commonFactor_add_four_of_entryBoundSpec
        htheta hY hi key (Sum.inr cell.1) data Q.cert Q.G Q.H hentry
    have hthinBound' :
        ((main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
          htheta hY hi key (Sum.inr cell.1)).card : ℝ) ≤
          2048 * (main3BalancedDegree theta : ℝ) * theta *
              ((shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs.divisors.card : ℝ) +
            4 := by
      apply hthinBound
      simpa only [Brect, delta,
        Main3LargeAnalyticComplexCellCoverSelectionData.mu,
        Main3LargeAnalyticComplexCellCoverSelectionData.M₀,
        Main3LargeAnalyticComplexCellCoverSelectionData.U,
        Main3LargeAnalyticComplexCellCoverSelectionData.V,
        Main3LargeAnalyticComplexCellCoverSelectionData.rho,
        Main3LargeAnalyticComplexCellCoverSelectionData.z,
        Main3LargeAnalyticComplexCellCoverSelectionData.beta,
        Q] using hthin
    have henv : 0 ≤ fullCellOddDegreeSieveEnvelope
        sieveN d Q.U Q.V Q.M₀ Q.mu :=
      fullCellOddDegreeSieveEnvelope_nonnegative
        sieveN d Q.U Q.V Q.M₀ Q.mu hsieveN hU hV hM₀ hmu
    linarith
  · have hfull : 1 ≤ Brect := le_of_not_gt hthin
    have hthreshold :
        main3LargeAnalyticIntrinsicEliminantSieveBudgetThreshold
            data Q.productHeight Q.U Q.V ≤ (sieveN : ℝ) :=
      hbudget.trans hscale
    have hfullBound :=
      hsieve.card_main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber_cast_le_commonFactor_add_twice_fullCellEnvelope_of_entryBoundSpec
        htheta hY hi key (Sum.inr cell.1) hcoordinate hkeyGate
          data Q.cert Q.G Q.H hentry
    have hfullBound' :
        ((main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
          htheta hY hi key (Sum.inr cell.1)).card : ℝ) ≤
          2048 * (main3BalancedDegree theta : ℝ) * theta *
              ((shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs.divisors.card : ℝ) +
            2 * fullCellOddDegreeSieveEnvelope
              sieveN d Q.U Q.V Q.M₀ Q.mu := by
      apply hfullBound
      · simpa only [Brect, delta,
          Main3LargeAnalyticComplexCellCoverSelectionData.mu,
          Main3LargeAnalyticComplexCellCoverSelectionData.M₀,
          Main3LargeAnalyticComplexCellCoverSelectionData.U,
          Main3LargeAnalyticComplexCellCoverSelectionData.V,
          Main3LargeAnalyticComplexCellCoverSelectionData.rho,
          Main3LargeAnalyticComplexCellCoverSelectionData.z,
          Main3LargeAnalyticComplexCellCoverSelectionData.beta,
          Q] using hfull
      · simpa only [
          Main3LargeAnalyticComplexCellCoverSelectionData.productHeight,
          Main3LargeAnalyticComplexCellCoverSelectionData.U,
          Main3LargeAnalyticComplexCellCoverSelectionData.V,
          Main3LargeAnalyticComplexCellCoverSelectionData.M₀,
          Main3LargeAnalyticComplexCellCoverSelectionData.rho,
          Main3LargeAnalyticComplexCellCoverSelectionData.z,
          Main3LargeAnalyticComplexCellCoverSelectionData.beta,
          Q] using hthreshold
    linarith

/-- Sum all active complex cells at one sieve parameter already known to
satisfy the globally uniform generic square-sieve event. -/
theorem FullCellOddHomogeneousPolynomialSieveAt.sum_main3LargeAnalytic_selectedComplexCellPointFibers_le
    {sieveN : ℕ}
    (hsieve : FullCellOddHomogeneousPolynomialSieveAt sieveN)
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hYgrow : Real.exp (800 * theta ^ 2) < (Y : ℝ))
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (hkeyGate : key ∈ main3LargeAnalytic_blockAuxiliaryKeyGate h v)
    (ha : 0 < shiftedSquareA h v)
    (hnonempty :
      (main3LargeAnalytic_nonemptyComplexCellIndices
        htheta hY hi key).Nonempty)
    (hsieveN : 4 ≤ sieveN)
    (hscale :
      128000 * theta ^ 7 * Real.log (Y : ℝ) ≤ (sieveN : ℝ)) :
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    let I := main3LargeAnalytic_nonemptyComplexCellIndices htheta hY hi key
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
      (10 * Mmesh) * baseCost +
        2 * fullCellOddDegreeSieveVariableAggregateEnvelope
          sieveN (2 * main3BalancedDegree theta + 1)
          (10 * Mmesh) (3 * E / (Mmesh * Delta))
          reciprocalBudget := by
  dsimp only
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let I := main3LargeAnalytic_nonemptyComplexCellIndices htheta hY hi key
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
  let degree : ↑I → ℕ := fun cell =>
    main3LargeAnalyticIntrinsicEliminantDegree
      (main3LargeAnalytic_complexCellAuxiliaryFactorSelection
        htheta hY hYgrow hi key cell)
  let Q : (cell : ↑I) →
      Main3LargeAnalyticFixedKeyComplexCellCoverSelection
        htheta hY hi key cell.1 ha :=
    fun cell => main3LargeAnalytic_complexCellCoverSelection
      htheta hY hi key ha cell
  have hpoint : ∀ cell : ↑I,
      ((main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
        htheta hY hi key (Sum.inr cell.1)).card : ℝ) ≤
        baseCost + 2 * fullCellOddDegreeSieveEnvelope
          sieveN (degree cell) (Q cell).U (Q cell).V
            (Q cell).M₀ (Q cell).mu := by
    intro cell
    simpa only [I, baseCost, degree, Q, add_assoc] using
      hsieve.card_main3LargeAnalytic_selectedComplexCellPointFiber_le
        htheta hY hYgrow hi key hkeyGate ha cell hsieveN hscale
  have hsum :
      (∑ cell : ↑I,
        ((main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
          htheta hY hi key (Sum.inr cell.1)).card : ℝ)) ≤
        (I.card : ℝ) * baseCost +
          2 * (∑ cell : ↑I, fullCellOddDegreeSieveEnvelope
            sieveN (degree cell) (Q cell).U (Q cell).V
              (Q cell).M₀ (Q cell).mu) := by
    calc
      _ ≤ ∑ cell : ↑I,
          (baseCost + 2 * fullCellOddDegreeSieveEnvelope
            sieveN (degree cell) (Q cell).U (Q cell).V
              (Q cell).M₀ (Q cell).mu) := by
        exact Finset.sum_le_sum fun cell _hcell => hpoint cell
      _ = (I.card : ℝ) * baseCost +
          2 * (∑ cell : ↑I, fullCellOddDegreeSieveEnvelope
            sieveN (degree cell) (Q cell).U (Q cell).V
              (Q cell).M₀ (Q cell).mu) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
          Fintype.card_coe]
  have hcard : (I.card : ℝ) ≤ 10 * Mmesh := by
    simpa only [I, Mmesh] using
      card_main3LargeAnalytic_nonemptyComplexCellIndices_cast_le_ten_mul
        htheta hY hi key
  have hbaseCost : 0 ≤ baseCost := by
    dsimp only [baseCost]
    positivity
  have henvelopes :=
    sum_main3LargeAnalytic_selectedComplexCell_fullCellEnvelope_le
      htheta hY hYgrow hi key ha hnonempty sieveN hsieveN
  have henvelopes' :
      (∑ cell : ↑I, fullCellOddDegreeSieveEnvelope
        sieveN (degree cell) (Q cell).U (Q cell).V
          (Q cell).M₀ (Q cell).mu) ≤
        fullCellOddDegreeSieveVariableAggregateEnvelope
          sieveN (2 * main3BalancedDegree theta + 1)
          (10 * Mmesh) (3 * E / (Mmesh * Delta)) reciprocalBudget := by
    simpa only [I, E, Delta, Mmesh, K, L, H₀, reciprocalBudget,
      degree, Q] using henvelopes
  calc
    (∑ cell : ↑I,
      ((main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
        htheta hY hi key (Sum.inr cell.1)).card : ℝ)) ≤
        (I.card : ℝ) * baseCost +
          2 * (∑ cell : ↑I, fullCellOddDegreeSieveEnvelope
            sieveN (degree cell) (Q cell).U (Q cell).V
              (Q cell).M₀ (Q cell).mu) := hsum
    _ ≤ (10 * Mmesh) * baseCost +
        2 * fullCellOddDegreeSieveVariableAggregateEnvelope
          sieveN (2 * main3BalancedDegree theta + 1)
          (10 * Mmesh) (3 * E / (Mmesh * Delta))
          reciprocalBudget := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right hcard hbaseCost
      · exact mul_le_mul_of_nonneg_left henvelopes' (by norm_num)

/-- The complete selected complex-cell point-fibre sum, conditional only on
the cited Weil proposition, is bounded by one explicit common-factor charge
plus the aggregated intrinsic square-sieve envelope. -/
theorem eventually_sum_main3LargeAnalytic_selectedComplexCellPointFibers_le
    (hWeil : OneVariableQuadraticWeilDegreeBound)
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hYgrow : Real.exp (800 * theta ^ 2) < (Y : ℝ))
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (hkeyGate : key ∈ main3LargeAnalytic_blockAuxiliaryKeyGate h v)
    (ha : 0 < shiftedSquareA h v)
    (hnonempty :
      (main3LargeAnalytic_nonemptyComplexCellIndices
        htheta hY hi key).Nonempty) :
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    let I := main3LargeAnalytic_nonemptyComplexCellIndices htheta hY hi key
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
    ∀ᶠ sieveN : ℕ in atTop,
      128000 * theta ^ 7 * Real.log (Y : ℝ) ≤ (sieveN : ℝ) →
        (∑ cell : ↑I,
          ((main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
            htheta hY hi key (Sum.inr cell.1)).card : ℝ)) ≤
          (10 * Mmesh) * baseCost +
            2 * fullCellOddDegreeSieveVariableAggregateEnvelope
              sieveN (2 * main3BalancedDegree theta + 1)
              (10 * Mmesh) (3 * E / (Mmesh * Delta))
              reciprocalBudget := by
  dsimp only
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let I := main3LargeAnalytic_nonemptyComplexCellIndices htheta hY hi key
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
  let degree : ↑I → ℕ := fun cell =>
    main3LargeAnalyticIntrinsicEliminantDegree
      (main3LargeAnalytic_complexCellAuxiliaryFactorSelection
        htheta hY hYgrow hi key cell)
  let Q : (cell : ↑I) →
      Main3LargeAnalyticFixedKeyComplexCellCoverSelection
        htheta hY hi key cell.1 ha :=
    fun cell => main3LargeAnalytic_complexCellCoverSelection
      htheta hY hi key ha cell
  have hpoint : ∀ cell : ↑I, ∀ᶠ sieveN : ℕ in atTop,
      128000 * theta ^ 7 * Real.log (Y : ℝ) ≤ (sieveN : ℝ) →
        ((main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
          htheta hY hi key (Sum.inr cell.1)).card : ℝ) ≤
          baseCost + 2 * fullCellOddDegreeSieveEnvelope
            sieveN (degree cell) (Q cell).U (Q cell).V
              (Q cell).M₀ (Q cell).mu := by
    intro cell
    simpa only [I, baseCost, degree, Q, add_assoc] using
      eventually_card_main3LargeAnalytic_selectedComplexCellPointFiber_le
        hWeil htheta hY hYgrow hi key hkeyGate ha cell
  have hall : ∀ᶠ sieveN : ℕ in atTop,
      ∀ cell ∈ (Finset.univ : Finset ↑I),
        128000 * theta ^ 7 * Real.log (Y : ℝ) ≤ (sieveN : ℝ) →
          ((main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
            htheta hY hi key (Sum.inr cell.1)).card : ℝ) ≤
            baseCost + 2 * fullCellOddDegreeSieveEnvelope
              sieveN (degree cell) (Q cell).U (Q cell).V
                (Q cell).M₀ (Q cell).mu :=
    (Filter.eventually_all_finset (Finset.univ : Finset ↑I)).2
      (fun cell _hcell => hpoint cell)
  filter_upwards [hall, eventually_ge_atTop 4] with sieveN hallN hsieveN
  intro hscale
  have hsum :
      (∑ cell : ↑I,
        ((main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
          htheta hY hi key (Sum.inr cell.1)).card : ℝ)) ≤
        (I.card : ℝ) * baseCost +
          2 * (∑ cell : ↑I, fullCellOddDegreeSieveEnvelope
            sieveN (degree cell) (Q cell).U (Q cell).V
              (Q cell).M₀ (Q cell).mu) := by
    calc
      _ ≤ ∑ cell : ↑I,
          (baseCost + 2 * fullCellOddDegreeSieveEnvelope
            sieveN (degree cell) (Q cell).U (Q cell).V
              (Q cell).M₀ (Q cell).mu) := by
        exact Finset.sum_le_sum fun cell hcell =>
          hallN cell (Finset.mem_univ cell) hscale
      _ = (I.card : ℝ) * baseCost +
          2 * (∑ cell : ↑I, fullCellOddDegreeSieveEnvelope
            sieveN (degree cell) (Q cell).U (Q cell).V
              (Q cell).M₀ (Q cell).mu) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
          Fintype.card_coe]
  have hcard : (I.card : ℝ) ≤ 10 * Mmesh := by
    simpa only [I, Mmesh] using
      card_main3LargeAnalytic_nonemptyComplexCellIndices_cast_le_ten_mul
        htheta hY hi key
  have hbaseCost : 0 ≤ baseCost := by
    dsimp only [baseCost]
    positivity
  have henvelopes :=
    sum_main3LargeAnalytic_selectedComplexCell_fullCellEnvelope_le
      htheta hY hYgrow hi key ha hnonempty sieveN hsieveN
  have henvelopes' :
      (∑ cell : ↑I, fullCellOddDegreeSieveEnvelope
        sieveN (degree cell) (Q cell).U (Q cell).V
          (Q cell).M₀ (Q cell).mu) ≤
        fullCellOddDegreeSieveVariableAggregateEnvelope
          sieveN (2 * main3BalancedDegree theta + 1)
          (10 * Mmesh) (3 * E / (Mmesh * Delta)) reciprocalBudget := by
    simpa only [I, E, Delta, Mmesh, K, L, H₀, reciprocalBudget,
      degree, Q] using henvelopes
  calc
    (∑ cell : ↑I,
      ((main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
        htheta hY hi key (Sum.inr cell.1)).card : ℝ)) ≤
        (I.card : ℝ) * baseCost +
          2 * (∑ cell : ↑I, fullCellOddDegreeSieveEnvelope
            sieveN (degree cell) (Q cell).U (Q cell).V
              (Q cell).M₀ (Q cell).mu) := hsum
    _ ≤ (10 * Mmesh) * baseCost +
        2 * fullCellOddDegreeSieveVariableAggregateEnvelope
          sieveN (2 * main3BalancedDegree theta + 1)
          (10 * Mmesh) (3 * E / (Mmesh * Delta))
          reciprocalBudget := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right hcard hbaseCost
      · exact mul_le_mul_of_nonneg_left henvelopes' (by norm_num)

/-- The uniform version places the sieve event before every Main3 block,
key, cell family, and selected cover.  This is the quantifier order needed
to substitute a single explicit moving sieve scale. -/
theorem eventually_uniform_sum_main3LargeAnalytic_selectedComplexCellPointFibers_le
    (hWeil : OneVariableQuadraticWeilDegreeBound) :
    ∀ᶠ sieveN : ℕ in atTop,
      ∀ {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
        (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
        (_hYgrow : Real.exp (800 * theta ^ 2) < (Y : ℝ))
        (hi : (h, v, D, N) ∈
          main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
        (key : ShiftedSquareAuxiliaryKey)
        (_hkeyGate : key ∈ main3LargeAnalytic_blockAuxiliaryKeyGate h v)
        (_ha : 0 < shiftedSquareA h v)
        (_hnonempty :
          (main3LargeAnalytic_nonemptyComplexCellIndices
            htheta hY hi key).Nonempty),
        128000 * theta ^ 7 * Real.log (Y : ℝ) ≤ (sieveN : ℝ) →
          letI : Fact (rationalQuadraticAlgebraNoRationalRoot
            (-(shiftedSquareA h v))) :=
            ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
          let I := main3LargeAnalytic_nonemptyComplexCellIndices htheta hY hi key
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
            (10 * Mmesh) * baseCost +
              2 * fullCellOddDegreeSieveVariableAggregateEnvelope
                sieveN (2 * main3BalancedDegree theta + 1)
                (10 * Mmesh) (3 * E / (Mmesh * Delta))
                reciprocalBudget := by
  filter_upwards
      [eventually_fullCellOddHomogeneousPolynomialSieveAt hWeil,
        eventually_ge_atTop 4]
      with sieveN hsieve hsieveN
  intro theta Y h v D N htheta hY hYgrow hi key hkeyGate ha hnonempty
    hscale
  exact hsieve.sum_main3LargeAnalytic_selectedComplexCellPointFibers_le
    htheta hY hYgrow hi key hkeyGate ha hnonempty hsieveN hscale

/-- At the single explicit Main3 sieve scale, the selected complex-cell sum
obeys the aggregated envelope uniformly after one cutoff in `Y`.  The same
conclusion retains the upper bound for the moving scale used in the final
power-saving comparison. -/
theorem eventually_main3LargeAnalytic_sum_selectedComplexCellPointFibers_at_sieveScale_le
    (hWeil : OneVariableQuadraticWeilDegreeBound)
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
        (_ha : 0 < shiftedSquareA h v)
        (_hnonempty :
          (main3LargeAnalytic_nonemptyComplexCellIndices
            htheta hY hi key).Nonempty),
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
            (10 * Mmesh) * baseCost +
              2 * fullCellOddDegreeSieveVariableAggregateEnvelope
                (main3LargeAnalyticSieveN theta Y)
                (2 * main3BalancedDegree theta + 1)
                (10 * Mmesh) (3 * E / (Mmesh * Delta))
                reciprocalBudget ∧
          (main3LargeAnalyticSieveN theta Y : ℝ) ≤
            2 * (Y : ℝ) ^ (1 / (32 * theta ^ 2)) := by
  filter_upwards
      [eventually_main3LargeAnalytic_uniformSieveChoice hWeil c hc hsmall]
      with Y hchoice
  intro theta htheta hadmissible hY h v D N hi key hkeyGate ha hnonempty
  have hpackage := hchoice theta htheta hadmissible
  refine ⟨?_, hpackage.2.2.2.2⟩
  exact hpackage.1.sum_main3LargeAnalytic_selectedComplexCellPointFibers_le
    htheta hY hpackage.2.1 hi key hkeyGate ha hnonempty
      hpackage.2.2.1 hpackage.2.2.2.1

end

end PellPaper
