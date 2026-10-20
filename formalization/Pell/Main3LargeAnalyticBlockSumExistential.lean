import Pell.Main3LargeAnalyticBlockSumLowerEvidence
import Pell.Main3LargeAnalyticRealCellRateLedger
import Pell.Main3LargeAnalyticComplexCellMinorVanishing
import Pell.Main3LargeAnalyticFixedKeyCellArithmetic
import Mathlib.Tactic

/-!
# Existential-constant large-analytic block-sum boundary

This candidate records the qualitative uniform estimate actually needed from
the large-analytic branch without fixing numerical values for its saving or
admissibility constants.  All three witnesses are absolute: they are chosen
before the eventual scale `Y` and before the growing parameter `theta`.

The statement still concerns the literal total large-analytic block sum.  It
does not replace that sum by a local interface and does not assume any
common-factor, residual-square, or intrinsic-completion conclusion.
-/

namespace PellPaper

open Filter
open scoped BigOperators

noncomputable section

/-- The separately checked real- and complex-cell determinant endpoints give
minor vanishing uniformly for the combined archimedean cell type.  A selected
full minor supplies a point of the cell image; its retained certificate
determines the required sign of the quadratic shift. -/
theorem main3LargeAnalytic_archimedeanCellCoordinatePointImage_selectedMinor_det_eq_zero
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hYgrow : Real.exp (800 * theta ^ 2) < (Y : ℝ))
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (s : generalBidegreeFormIndex 1 (main3BalancedDegree theta) ↪
      {z // z ∈
        main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
          htheta hY hi key cell}) :
    ((generalBidegreeFormEvaluationMatrix 1 (main3BalancedDegree theta)
      (fun z : {z // z ∈
        main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
          htheta hY hi key cell} => z.1)).submatrix s id).det = 0 := by
  cases cell with
  | inl realCell =>
      let r₀ : generalBidegreeFormIndex 1 (main3BalancedDegree theta) :=
        (⟨0, by omega⟩, ⟨0, by omega⟩)
      have hz := (s r₀).2
      obtain ⟨p, _hp, _hkey, _hselector, hgeometry, _hcode, _hpoint⟩ :=
        main3LargeAnalytic_blockCellCoordinatePointImage_sameCertificate
          htheta hY hi hz
      obtain ⟨ha, _hcell⟩ := hgeometry
      exact
        main3LargeAnalytic_realCellCoordinatePointImage_selectedMinor_det_eq_zero
          htheta hY hYgrow hi ha key realCell s
  | inr complexCell =>
      let r₀ : generalBidegreeFormIndex 1 (main3BalancedDegree theta) :=
        (⟨0, by omega⟩, ⟨0, by omega⟩)
      have hz := (s r₀).2
      obtain ⟨p, _hp, _hkey, _hselector, hgeometry, _hcode, _hpoint⟩ :=
        main3LargeAnalytic_blockCellCoordinatePointImage_sameCertificate
          htheta hY hi hz
      obtain ⟨ha, _hcell⟩ := hgeometry
      exact
        main3LargeAnalytic_complexCellCoordinatePointImage_selectedMinor_det_eq_zero
          htheta hY hYgrow hi ha key complexCell s

/-- Consequently every nonempty fixed-key/fixed-cell image has the existing
bounded auxiliary-factor package, with no determinant-rate premise left. -/
theorem nonempty_main3LargeAnalyticFixedKeyCellAuxiliaryFactorData_of_growth
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hYgrow : Real.exp (800 * theta ^ 2) < (Y : ℝ))
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (hnonempty :
      (main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
        htheta hY hi key cell).Nonempty) :
    Nonempty (Main3LargeAnalyticFixedKeyCellAuxiliaryFactorData
      htheta hY hi key cell (main3BalancedDegree theta)) := by
  apply exists_main3LargeAnalyticFixedKeyCellAuxiliaryFactorData
    htheta hY hi key cell hnonempty
  intro s
  exact
    main3LargeAnalytic_archimedeanCellCoordinatePointImage_selectedMinor_det_eq_zero
      htheta hY hYgrow hi key cell s

/-- A uniform total large-analytic block-sum estimate with unspecified
positive saving, admissibility, and multiplicative constants.  The
dependence on the standard one-variable Weil estimate remains explicit. -/
def Main3LargeAnalyticBlockSumEstimateExistential : Prop :=
  OneVariableQuadraticWeilDegreeBound →
    ∃ delta c₀ C : ℝ,
      0 < delta ∧ 0 < c₀ ∧ 0 < C ∧
        ∀ᶠ Y : ℕ in atTop, ∀ theta : ℝ,
          3 ≤ theta →
          theta ≤ c₀ * Real.sqrt
            (Real.log (Y : ℝ) / Real.log (Real.log (Y : ℝ))) →
          ((∑ i ∈
              main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y,
            (squarefreeShiftedSquareBlock
              (shiftedSquareA i.1 i.2.1) i.2.2.1 Y i.2.2.2).card : ℕ) : ℝ)
            ≤ C * (Y : ℝ) ^ (1 - delta / theta ^ 2)

/-- The same qualitative estimate in the manuscript-style normalization in
which one positive constant controls both the admissible range and the power
saving. -/
def Main3LargeAnalyticBlockSumEstimateExistentialCommonConstant : Prop :=
  OneVariableQuadraticWeilDegreeBound →
    ∃ c C : ℝ,
      0 < c ∧ 0 < C ∧
        ∀ᶠ Y : ℕ in atTop, ∀ theta : ℝ,
          3 ≤ theta →
          theta ≤ c * Real.sqrt
            (Real.log (Y : ℝ) / Real.log (Real.log (Y : ℝ))) →
          ((∑ i ∈
              main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y,
            (squarefreeShiftedSquareBlock
              (shiftedSquareA i.1 i.2.1) i.2.2.1 Y i.2.2.2).card : ℕ) : ℝ)
            ≤ C * (Y : ℝ) ^ (1 - c / theta ^ 2)

/-- The existing explicit-rate lower-evidence boundary implies the
existential-constant boundary.  This is a transport theorem only; it does not
prove the existing lower-evidence premise. -/
theorem main3LargeAnalyticBlockSumEstimateExistential_of_lowerEvidence
    (hLarge : Main3LargeAnalyticBlockSumEstimateLowerEvidence) :
    Main3LargeAnalyticBlockSumEstimateExistential := by
  intro hWeil
  obtain ⟨C, hC, hAll⟩ := hLarge hWeil
  refine ⟨(1 : ℝ) / 400, (1 : ℝ) / 1000, C, by norm_num, by norm_num,
    hC, ?_⟩
  simpa only [div_div] using
    hAll ((1 : ℝ) / 1000) (by norm_num) (by norm_num)

/-- Allowing separate positive saving and admissibility constants is
logically equivalent to using one unspecified positive constant: take their
minimum. -/
theorem main3LargeAnalyticBlockSumEstimateExistential_iff_commonConstant :
    Main3LargeAnalyticBlockSumEstimateExistential ↔
      Main3LargeAnalyticBlockSumEstimateExistentialCommonConstant := by
  constructor
  · intro h hWeil
    obtain ⟨delta, c₀, C, hdelta, hc₀, hC, hAll⟩ := h hWeil
    let c : ℝ := min delta c₀
    have hc : 0 < c := by
      dsimp [c]
      exact lt_min hdelta hc₀
    refine ⟨c, C, hc, hC, ?_⟩
    filter_upwards [hAll, eventually_ge_atTop 1] with Y hY hYone
    intro theta htheta hadmissible
    let q : ℝ :=
      Real.log (Y : ℝ) / Real.log (Real.log (Y : ℝ))
    have hadmissible₀ : theta ≤ c₀ * Real.sqrt q := by
      calc
        theta ≤ c * Real.sqrt q := by simpa only [q] using hadmissible
        _ ≤ c₀ * Real.sqrt q := by
          exact mul_le_mul_of_nonneg_right (min_le_right delta c₀)
            (Real.sqrt_nonneg q)
    have hbound := hY theta htheta (by simpa only [q] using hadmissible₀)
    have hquotient : c / theta ^ 2 ≤ delta / theta ^ 2 :=
      div_le_div_of_nonneg_right (min_le_left delta c₀)
        (sq_nonneg theta)
    have hexponent : 1 - delta / theta ^ 2 ≤ 1 - c / theta ^ 2 :=
      sub_le_sub_left hquotient 1
    have hpower :
        (Y : ℝ) ^ (1 - delta / theta ^ 2) ≤
          (Y : ℝ) ^ (1 - c / theta ^ 2) := by
      apply Real.rpow_le_rpow_of_exponent_le
      · exact_mod_cast hYone
      · exact hexponent
    exact hbound.trans (mul_le_mul_of_nonneg_left hpower hC.le)
  · intro h hWeil
    obtain ⟨c, C, hc, hC, hAll⟩ := h hWeil
    exact ⟨c, c, C, hc, hc, hC, hAll⟩

/-- Existential constants are sufficient for the already checked merger of
the balanced, direct-unbalanced, and large-analytic ranges.  The common
saving is the minimum of the unknown large-analytic saving and the checked
`1/400` saving; the common admissibility constant is the minimum of the
unknown cutoff and one fixed safe cutoff for the checked estimates.

This theorem is genuine class-A transport.  Its only mathematical premises
are the existing Weil and congruence-window inputs and the existential total
large-analytic estimate itself. -/
theorem
    exists_pos_uniform_squarefreeDyadicExceptionalCount_cast_le_of_existentialMain3BlockEstimate
    (hWeil : OneVariableQuadraticWeilDegreeBound)
    (haverage : ShiftedSquareCongruenceWindowAverageAssertion)
    (hLarge : Main3LargeAnalyticBlockSumEstimateExistential) :
    ∃ delta c₀ C : ℝ,
      0 < delta ∧ 0 < c₀ ∧ 0 < C ∧
        ∀ᶠ Y : ℕ in atTop, ∀ theta : ℝ,
          3 ≤ theta →
          theta ≤ c₀ * Real.sqrt
            (Real.log (Y : ℝ) / Real.log (Real.log (Y : ℝ))) →
          (squarefreeDyadicExceptionalCount (theta + 1 / 4) Y : ℝ) ≤
            C * (Y : ℝ) ^ (1 - delta / theta ^ 2) := by
  obtain ⟨deltaLarge, cLarge, CLarge, hdeltaLarge, hcLarge, hCLarge,
    hLargeAll⟩ := hLarge hWeil
  let delta : ℝ := min deltaLarge ((1 : ℝ) / 400)
  let c₀ : ℝ := min cLarge ((1 : ℝ) / 1000)
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact lt_min hdeltaLarge (by norm_num)
  have hc₀ : 0 < c₀ := by
    dsimp [c₀]
    exact lt_min hcLarge (by norm_num)
  have hc₀Large : c₀ ≤ cLarge := by
    dsimp [c₀]
    exact min_le_left _ _
  have hc₀Upper : c₀ ≤ (1 : ℝ) / 1000 := by
    dsimp [c₀]
    exact min_le_right _ _
  have hc₀sq : c₀ ^ 2 ≤ ((1 : ℝ) / 1000) ^ 2 :=
    (sq_le_sq₀ hc₀.le (by norm_num)).2 hc₀Upper
  have hsmall : 10 * c₀ ^ 2 ≤ (1 : ℝ) / 2400 := by
    calc
      10 * c₀ ^ 2 ≤ 10 * ((1 : ℝ) / 1000) ^ 2 := by nlinarith
      _ ≤ (1 : ℝ) / 2400 := by norm_num
  have hBalanced :=
    eventually_main3BalancedDyadicFactorTuples_card_le
      hWeil c₀ hc₀ hsmall
  have hDirect :=
    eventually_main3UnbalancedEnlargedDirectBlockSum_cast_le_of_congruenceWindowAverage
      haverage c₀ hc₀ hsmall
  refine ⟨delta, c₀, 37 + CLarge, hdelta, hc₀, by linarith, ?_⟩
  filter_upwards [hBalanced, hDirect, hLargeAll, eventually_ge_atTop 1] with
    Y hBalancedY hDirectY hLargeY hYone
  intro theta htheta hadmissible
  let q : ℝ :=
    Real.log (Y : ℝ) / Real.log (Real.log (Y : ℝ))
  have hadmissibleLarge : theta ≤ cLarge * Real.sqrt q := by
    calc
      theta ≤ c₀ * Real.sqrt q := by simpa only [q] using hadmissible
      _ ≤ cLarge * Real.sqrt q := by
        exact mul_le_mul_of_nonneg_right hc₀Large (Real.sqrt_nonneg q)
  have hthetaCover : 0 ≤ theta + 1 / 4 := by linarith
  have hCountNat :=
    squarefreeDyadicExceptionalCount_le_balanced_add_admissibleUnbalanced
      (Y := Y) (R := main3BalancedR theta Y) hthetaCover
  have hUnbalancedNat :=
    card_admissibleUnbalancedDyadicFactorTuples_le_main3EnlargedDirect_add_largeAnalytic
      theta Y
  have hCountNat' :
      squarefreeDyadicExceptionalCount (theta + 1 / 4) Y ≤
        (balancedDyadicFactorTuples (theta + 1 / 4) Y
          (main3BalancedR theta Y)).card +
        ((∑ i ∈ main3UnbalancedEnlargedDirectDyadicCoverIndices theta Y,
            (squarefreeShiftedSquareBlock
              (shiftedSquareA i.1 i.2.1) i.2.2.1 Y i.2.2.2).card) +
          ∑ i ∈
              main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y,
            (squarefreeShiftedSquareBlock
              (shiftedSquareA i.1 i.2.1) i.2.2.1 Y i.2.2.2).card) := by
    omega
  have hCount :
      (squarefreeDyadicExceptionalCount (theta + 1 / 4) Y : ℝ) ≤
        ((balancedDyadicFactorTuples (theta + 1 / 4) Y
          (main3BalancedR theta Y)).card : ℝ) +
        (((∑ i ∈ main3UnbalancedEnlargedDirectDyadicCoverIndices theta Y,
            (squarefreeShiftedSquareBlock
              (shiftedSquareA i.1 i.2.1) i.2.2.1 Y i.2.2.2).card : ℕ) : ℝ) +
          ((∑ i ∈
              main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y,
            (squarefreeShiftedSquareBlock
              (shiftedSquareA i.1 i.2.1) i.2.2.1 Y i.2.2.2).card : ℕ) : ℝ)) := by
    exact_mod_cast hCountNat'
  have hBalanced' := hBalancedY theta htheta hadmissible
  have hDirect' := hDirectY theta htheta hadmissible
  have hLarge' := hLargeY theta htheta
    (by simpa only [q] using hadmissibleLarge)
  let y : ℝ := Y
  let bChecked : ℝ := 1 - 1 / (400 * theta ^ 2)
  let bLarge : ℝ := 1 - deltaLarge / theta ^ 2
  let b : ℝ := 1 - delta / theta ^ 2
  have hyone : 1 ≤ y := by
    dsimp [y]
    exact_mod_cast hYone
  have hdeltaChecked : delta ≤ (1 : ℝ) / 400 := by
    dsimp [delta]
    exact min_le_right _ _
  have hdeltaLarge' : delta ≤ deltaLarge := by
    dsimp [delta]
    exact min_le_left _ _
  have hquotientChecked :
      delta / theta ^ 2 ≤ 1 / (400 * theta ^ 2) := by
    rw [← div_div]
    exact div_le_div_of_nonneg_right hdeltaChecked (sq_nonneg theta)
  have hquotientLarge :
      delta / theta ^ 2 ≤ deltaLarge / theta ^ 2 :=
    div_le_div_of_nonneg_right hdeltaLarge' (sq_nonneg theta)
  have hbChecked : bChecked ≤ b := by
    dsimp [bChecked, b]
    exact sub_le_sub_left hquotientChecked 1
  have hbLarge : bLarge ≤ b := by
    dsimp [bLarge, b]
    exact sub_le_sub_left hquotientLarge 1
  have hpowerChecked : y ^ bChecked ≤ y ^ b :=
    Real.rpow_le_rpow_of_exponent_le hyone hbChecked
  have hpowerLarge : y ^ bLarge ≤ y ^ b :=
    Real.rpow_le_rpow_of_exponent_le hyone hbLarge
  calc
    (squarefreeDyadicExceptionalCount (theta + 1 / 4) Y : ℝ) ≤
        ((balancedDyadicFactorTuples (theta + 1 / 4) Y
          (main3BalancedR theta Y)).card : ℝ) +
        (((∑ i ∈ main3UnbalancedEnlargedDirectDyadicCoverIndices theta Y,
            (squarefreeShiftedSquareBlock
              (shiftedSquareA i.1 i.2.1) i.2.2.1 Y i.2.2.2).card : ℕ) : ℝ) +
          ((∑ i ∈
              main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y,
            (squarefreeShiftedSquareBlock
              (shiftedSquareA i.1 i.2.1) i.2.2.1 Y i.2.2.2).card : ℕ) : ℝ)) :=
      hCount
    _ ≤ 35 * y ^ bChecked + (2 * y ^ bChecked + CLarge * y ^ bLarge) := by
      simpa only [y, bChecked, bLarge] using
        add_le_add hBalanced' (add_le_add hDirect' hLarge')
    _ ≤ 35 * y ^ b + (2 * y ^ b + CLarge * y ^ b) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hpowerChecked (by norm_num))
        (add_le_add
          (mul_le_mul_of_nonneg_left hpowerChecked (by norm_num))
          (mul_le_mul_of_nonneg_left hpowerLarge hCLarge.le))
    _ = (37 + CLarge) * y ^ b := by ring

end

end PellPaper
