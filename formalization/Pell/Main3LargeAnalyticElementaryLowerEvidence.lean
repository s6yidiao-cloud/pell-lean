import Pell.Main3LargeAnalyticElementaryPointwise
import Pell.Main3LargeAnalyticOuterAbsorption
import Mathlib.Tactic

namespace PellPaper

open Filter
open scoped BigOperators

noncomputable section

/-- Direct no-Weil large-analytic lower-evidence proposition.  It has the
same witnesses and quantifier order as the production evidence boundary, with
the obsolete Weil implication removed. -/
def Main3LargeAnalyticBlockSumEstimateLowerEvidenceElementary : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ c : ℝ, 0 < c →
      10 * c ^ 2 ≤ (1 : ℝ) / 2400 →
      ∀ᶠ Y : ℕ in atTop, ∀ theta : ℝ,
        3 ≤ theta →
        theta ≤ c * Real.sqrt
          (Real.log (Y : ℝ) / Real.log (Real.log (Y : ℝ))) →
        ((∑ i ∈
            main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y,
          (squarefreeShiftedSquareBlock
            (shiftedSquareA i.1 i.2.1) i.2.2.1 Y i.2.2.2).card : ℕ) : ℝ)
          ≤ C * (Y : ℝ) ^ (1 - 1 / (400 * theta ^ 2))

/-- A key-summed pointwise block estimate of the preceding explicit shape
implies the exact public lower-evidence proposition.  Before the final
weakening, the proof obtains the stronger exponent
`1 - 3/(400*theta^2)`, leaving the literal margin
`1/(200*theta^2)`. -/
theorem main3LargeAnalyticBlockSumEstimateLowerEvidenceElementary_of_thetaTwelveLogSix
    (hPointwise :
      Main3LargeAnalyticThetaTwelveLogSixPointwiseBlockEstimateElementary) :
    Main3LargeAnalyticBlockSumEstimateLowerEvidenceElementary := by
  obtain ⟨K, hK, hPointwiseAll⟩ := hPointwise
  let C : ℝ := 4 ^ ((9 : ℝ) / 8)
  have hC : 0 < C := by
    dsimp only [C]
    exact Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨C, hC, ?_⟩
  intro c hc hsmall
  have hcoefficient :=
    eventually_main3LargeAnalytic_indexThetaTwelveLogSix_le_rpow
      (K * 3 ^ 6) c (by positivity) hc hsmall
  have hlocal := hPointwiseAll c hc hsmall
  filter_upwards [hcoefficient, hlocal, eventually_ge_atTop 2] with
    Y hcoefficientY hlocalY hY
  intro theta htheta hadmissible
  let I :=
    main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y
  let y : ℝ := Y
  let L : ℝ := 1 + Real.log (2 * y)
  let delta : ℝ := main3BalancedRExponent theta
  let q : ℝ := ((1 : ℝ) / 100 + 1 / 400) / theta ^ 2
  let sourceExponent : ℝ := 1 - 1 / (32 * theta ^ 2)
  let strongExponent : ℝ := 1 - 3 / (400 * theta ^ 2)
  let targetExponent : ℝ := 1 - 1 / (400 * theta ^ 2)
  have hypos : 0 < y := by dsimp only [y]; positivity
  have hyone : 1 ≤ y := by
    dsimp only [y]
    exact_mod_cast (show 1 ≤ Y by omega)
  have hcoefficientBound :
      (I.card : ℝ) * ((K * 3 ^ 6) * theta ^ 12 * L ^ 6) ≤
        y ^ q := by
    simpa only [I, y, L, q, mul_assoc] using
      hcoefficientY theta htheta hadmissible
  have hpoint : ∀ i ∈ I,
      ((squarefreeShiftedSquareBlock
        (shiftedSquareA i.1 i.2.1) i.2.2.1 Y i.2.2.2).card : ℝ) ≤
        ((K * 3 ^ 6) * theta ^ 12 * L ^ 6) *
          (4 ^ ((9 : ℝ) / 8) *
            y ^ (delta * ((9 : ℝ) / 8)) * y ^ sourceExponent) := by
    intro i hi
    let A : ℝ := main3LargeAnalyticShiftWeight i.1 i.2.1
    let S : ℝ := 1 + Real.log (2 * A * y)
    have hlocalPoint :=
      hlocalY theta htheta hadmissible
        i.1 i.2.1 i.2.2.1 i.2.2.2 (by simpa only [I] using hi)
    have hS0 : 0 ≤ S := by
      simpa only [S, A, y] using
        main3LargeAnalytic_one_add_log_shiftWeight_mul_Y_nonneg
          hY (by simpa only [I] using hi)
    have hS : S ≤ 3 * L := by
      simpa only [S, A, L, y] using
        main3LargeAnalytic_one_add_log_shiftWeight_mul_Y_le_candidate
          htheta hY (by simpa only [I] using hi)
    have hSPow : S ^ 6 ≤ (3 * L) ^ 6 :=
      pow_le_pow_left₀ hS0 hS 6
    have hA : A ^ ((9 : ℝ) / 8) ≤
        4 ^ ((9 : ℝ) / 8) *
          y ^ (delta * ((9 : ℝ) / 8)) := by
      simpa only [A, y, delta] using
        main3LargeAnalyticShiftWeight_rpow_le_candidate
          htheta hY (by simpa only [I] using hi)
            (by norm_num : (0 : ℝ) ≤ 9 / 8)
    have hcoefficientPoint :
        K * theta ^ 12 * S ^ 6 ≤
          K * theta ^ 12 * (3 * L) ^ 6 := by
      exact mul_le_mul_of_nonneg_left hSPow (by positivity)
    have hgeometricPoint :
        A ^ ((9 : ℝ) / 8) * y ^ sourceExponent ≤
          (4 ^ ((9 : ℝ) / 8) *
            y ^ (delta * ((9 : ℝ) / 8))) * y ^ sourceExponent :=
      mul_le_mul_of_nonneg_right hA (Real.rpow_nonneg hypos.le _)
    have hAnonneg : 0 ≤ A := by
      dsimp only [A, main3LargeAnalyticShiftWeight]
      positivity
    have hgeometricPointNonneg :
        0 ≤ A ^ ((9 : ℝ) / 8) * y ^ sourceExponent :=
      mul_nonneg
        (Real.rpow_nonneg hAnonneg _)
        (Real.rpow_nonneg hypos.le _)
    have hcoefficientUpperNonneg :
        0 ≤ K * theta ^ 12 * (3 * L) ^ 6 := by positivity
    calc
      ((squarefreeShiftedSquareBlock
        (shiftedSquareA i.1 i.2.1) i.2.2.1 Y i.2.2.2).card : ℝ) ≤
          K * theta ^ 12 * S ^ 6 *
            (A ^ ((9 : ℝ) / 8) * y ^ sourceExponent) := by
        simpa only [A, S, y, sourceExponent, mul_assoc] using hlocalPoint
      _ ≤ (K * theta ^ 12 * (3 * L) ^ 6) *
          ((4 ^ ((9 : ℝ) / 8) *
            y ^ (delta * ((9 : ℝ) / 8))) * y ^ sourceExponent) := by
        exact mul_le_mul hcoefficientPoint hgeometricPoint
          hgeometricPointNonneg hcoefficientUpperNonneg
      _ = ((K * 3 ^ 6) * theta ^ 12 * L ^ 6) *
          (4 ^ ((9 : ℝ) / 8) *
            y ^ (delta * ((9 : ℝ) / 8)) * y ^ sourceExponent) := by
        rw [mul_pow]
        ring
  have hsum :
      (∑ i ∈ I,
        ((squarefreeShiftedSquareBlock
          (shiftedSquareA i.1 i.2.1) i.2.2.1 Y i.2.2.2).card : ℝ)) ≤
        (I.card : ℝ) * ((K * 3 ^ 6) * theta ^ 12 * L ^ 6) *
          (4 ^ ((9 : ℝ) / 8) *
            y ^ (delta * ((9 : ℝ) / 8)) * y ^ sourceExponent) := by
    calc
      (∑ i ∈ I,
        ((squarefreeShiftedSquareBlock
          (shiftedSquareA i.1 i.2.1) i.2.2.1 Y i.2.2.2).card : ℝ)) ≤
          ∑ _i ∈ I,
            (((K * 3 ^ 6) * theta ^ 12 * L ^ 6) *
              (4 ^ ((9 : ℝ) / 8) *
                y ^ (delta * ((9 : ℝ) / 8)) * y ^ sourceExponent)) := by
        exact Finset.sum_le_sum hpoint
      _ = (I.card : ℝ) * ((K * 3 ^ 6) * theta ^ 12 * L ^ 6) *
          (4 ^ ((9 : ℝ) / 8) *
            y ^ (delta * ((9 : ℝ) / 8)) * y ^ sourceExponent) := by
        simp
        ring
  have hfactorNonneg :
      0 ≤ 4 ^ ((9 : ℝ) / 8) *
        y ^ (delta * ((9 : ℝ) / 8)) * y ^ sourceExponent := by
    positivity
  have hexponent :
      q + delta * ((9 : ℝ) / 8) + sourceExponent =
        strongExponent := by
    simpa only [q, delta, sourceExponent, strongExponent] using
      main3LargeAnalytic_outer_nineEighth_exponent_eq htheta
  have hstrongTarget : strongExponent ≤ targetExponent := by
    simpa only [strongExponent, targetExponent] using
      main3LargeAnalytic_threeFourHundred_exponent_le_target htheta
  change
    (((∑ i ∈ I,
      (squarefreeShiftedSquareBlock
        (shiftedSquareA i.1 i.2.1) i.2.2.1 Y i.2.2.2).card : ℕ) : ℝ)) ≤
      C * y ^ targetExponent
  calc
    (((∑ i ∈ I,
        (squarefreeShiftedSquareBlock
          (shiftedSquareA i.1 i.2.1) i.2.2.1 Y i.2.2.2).card : ℕ) : ℝ)) =
        ∑ i ∈ I,
          ((squarefreeShiftedSquareBlock
            (shiftedSquareA i.1 i.2.1) i.2.2.1 Y i.2.2.2).card : ℝ) := by
      push_cast
      rfl
    _ ≤ (I.card : ℝ) * ((K * 3 ^ 6) * theta ^ 12 * L ^ 6) *
          (4 ^ ((9 : ℝ) / 8) *
            y ^ (delta * ((9 : ℝ) / 8)) * y ^ sourceExponent) := hsum
    _ ≤ y ^ q *
          (4 ^ ((9 : ℝ) / 8) *
            y ^ (delta * ((9 : ℝ) / 8)) * y ^ sourceExponent) :=
      mul_le_mul_of_nonneg_right hcoefficientBound hfactorNonneg
    _ = 4 ^ ((9 : ℝ) / 8) * y ^ strongExponent := by
      calc
        y ^ q *
            (4 ^ ((9 : ℝ) / 8) *
              y ^ (delta * ((9 : ℝ) / 8)) * y ^ sourceExponent) =
            4 ^ ((9 : ℝ) / 8) *
              ((y ^ q * y ^ (delta * ((9 : ℝ) / 8))) *
                y ^ sourceExponent) := by ring
        _ = 4 ^ ((9 : ℝ) / 8) *
              (y ^ (q + delta * ((9 : ℝ) / 8)) *
                y ^ sourceExponent) := by
          congr 1
          exact congrArg (fun t : ℝ => t * y ^ sourceExponent)
            (Real.rpow_add hypos q
              (delta * ((9 : ℝ) / 8))).symm
        _ = 4 ^ ((9 : ℝ) / 8) *
              y ^ (q + delta * ((9 : ℝ) / 8) + sourceExponent) := by
          congr 1
          exact (Real.rpow_add hypos
            (q + delta * ((9 : ℝ) / 8)) sourceExponent).symm
        _ = 4 ^ ((9 : ℝ) / 8) * y ^ strongExponent := by rw [hexponent]
    _ ≤ C * y ^ targetExponent := by
      dsimp only [C]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hyone hstrongTarget) hC.le


/-- The elementary pointwise theorem proves the direct no-Weil evidence. -/
theorem main3LargeAnalyticBlockSumEstimateLowerEvidence_elementary_proved :
    Main3LargeAnalyticBlockSumEstimateLowerEvidenceElementary :=
  main3LargeAnalyticBlockSumEstimateLowerEvidenceElementary_of_thetaTwelveLogSix
    main3LargeAnalytic_thetaTwelveLogSixPointwiseBlockEstimate_elementary

/-- Compatibility adapter for the current production lower-evidence API. -/
theorem main3LargeAnalyticBlockSumEstimateLowerEvidence_of_elementary :
    Main3LargeAnalyticBlockSumEstimateLowerEvidence := by
  intro _hWeil
  exact main3LargeAnalyticBlockSumEstimateLowerEvidence_elementary_proved


end

end PellPaper

#check PellPaper.Main3LargeAnalyticBlockSumEstimateLowerEvidenceElementary
#check PellPaper.main3LargeAnalyticBlockSumEstimateLowerEvidence_elementary_proved
#check PellPaper.main3LargeAnalyticBlockSumEstimateLowerEvidence_of_elementary
#print axioms PellPaper.main3LargeAnalyticBlockSumEstimateLowerEvidence_elementary_proved
#print axioms PellPaper.main3LargeAnalyticBlockSumEstimateLowerEvidence_of_elementary

