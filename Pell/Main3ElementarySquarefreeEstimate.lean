import Pell.Main3BalancedFinalElementary
import Pell.Main3LargeAnalyticElementaryLowerEvidence
import Pell.ShiftedSquareCongruenceWindowAverageProof
import Pell.Main3UnbalancedEnlargedDirectScaleAbsorption
import Mathlib.Tactic

/-!
# The squarefree dyadic estimate

The balanced and unbalanced estimates are combined before square factors
are restored. `UniformDoubledParameterEstimate` applies this bound at doubled
parameter.
-/

open Filter
open scoped BigOperators
namespace PellPaper
noncomputable section

/-- The exact large-analytic block estimate needed by the elementary final
assembly.  Unlike the older lower-evidence interface, this statement does not
take `OneVariableQuadraticWeilDegreeBound` as an argument. -/
def Main3LargeAnalyticBlockSumEstimateElementaryInput : Prop :=
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

/-- The elementary balanced estimate, the proved direct-unbalanced estimate,
and the explicit no-Weil large-analytic input give the squarefree dyadic
estimate.  The constant is `35 + 2 + C`. -/
theorem exists_pos_uniform_squarefreeDyadicExceptionalCount_cast_le_elementary_of_large
    (hLarge : Main3LargeAnalyticBlockSumEstimateElementaryInput) :
    ∃ C : ℝ, 0 < C ∧
      ∀ c : ℝ, 0 < c →
        10 * c ^ 2 ≤ (1 : ℝ) / 2400 →
        ∀ᶠ Y : ℕ in atTop, ∀ theta : ℝ,
          3 ≤ theta →
          theta ≤ c * Real.sqrt
            (Real.log (Y : ℝ) / Real.log (Real.log (Y : ℝ))) →
          (squarefreeDyadicExceptionalCount (theta + 1 / 4) Y : ℝ) ≤
            C * (Y : ℝ) ^ (1 - 1 / (400 * theta ^ 2)) := by
  obtain ⟨C, hC, hLargeAll⟩ := hLarge
  refine ⟨37 + C, by linarith, ?_⟩
  intro c hc hsmall
  have hBalanced :=
    eventually_main3BalancedDyadicFactorTuples_card_le_elementary c hc hsmall
  have hDirect :=
    eventually_main3UnbalancedEnlargedDirectBlockSum_cast_le_of_congruenceWindowAverage
      shiftedSquareCongruenceWindowAverageAssertion_proved c hc hsmall
  have hLargeAt := hLargeAll c hc hsmall
  filter_upwards [hBalanced, hDirect, hLargeAt] with Y hBalancedY hDirectY hLargeY
  intro theta htheta hadmissible
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
  have hLarge' := hLargeY theta htheta hadmissible
  let y : ℝ := Y
  let b : ℝ := 1 - 1 / (400 * theta ^ 2)
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
    _ ≤ 35 * y ^ b + (2 * y ^ b + C * y ^ b) := by
      simpa only [y, b] using
        add_le_add hBalanced' (add_le_add hDirect' hLarge')
    _ = (37 + C) * y ^ b := by ring

/-- Fixed-`c` specialization of the elementary squarefree dyadic estimate. -/
theorem eventually_squarefreeDyadicExceptionalCount_cast_le_elementary_of_large
    (hLarge : Main3LargeAnalyticBlockSumEstimateElementaryInput)
    (c : ℝ) (hc : 0 < c)
    (hsmall : 10 * c ^ 2 ≤ (1 : ℝ) / 2400) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ Y : ℕ in atTop, ∀ theta : ℝ,
        3 ≤ theta →
        theta ≤ c * Real.sqrt
          (Real.log (Y : ℝ) / Real.log (Real.log (Y : ℝ))) →
        (squarefreeDyadicExceptionalCount (theta + 1 / 4) Y : ℝ) ≤
          C * (Y : ℝ) ^ (1 - 1 / (400 * theta ^ 2)) := by
  obtain ⟨C, hC, hAll⟩ :=
    exists_pos_uniform_squarefreeDyadicExceptionalCount_cast_le_elementary_of_large
      hLarge
  exact ⟨C, hC, hAll c hc hsmall⟩

/-- The proved elementary large-analytic endpoint has exactly the raw shape
used by this assembly. -/
theorem main3LargeAnalyticBlockSumEstimateElementaryInput_proved :
    Main3LargeAnalyticBlockSumEstimateElementaryInput := by
  simpa only [Main3LargeAnalyticBlockSumEstimateElementaryInput,
    Main3LargeAnalyticBlockSumEstimateLowerEvidenceElementary] using
    main3LargeAnalyticBlockSumEstimateLowerEvidence_elementary_proved

/-- Unconditional squarefree dyadic estimate from the elementary route. -/
theorem exists_pos_uniform_squarefreeDyadicExceptionalCount_cast_le_elementary :
    ∃ C : ℝ, 0 < C ∧
      ∀ c : ℝ, 0 < c →
        10 * c ^ 2 ≤ (1 : ℝ) / 2400 →
        ∀ᶠ Y : ℕ in atTop, ∀ theta : ℝ,
          3 ≤ theta →
          theta ≤ c * Real.sqrt
            (Real.log (Y : ℝ) / Real.log (Real.log (Y : ℝ))) →
          (squarefreeDyadicExceptionalCount (theta + 1 / 4) Y : ℝ) ≤
            C * (Y : ℝ) ^ (1 - 1 / (400 * theta ^ 2)) :=
  exists_pos_uniform_squarefreeDyadicExceptionalCount_cast_le_elementary_of_large
    main3LargeAnalyticBlockSumEstimateElementaryInput_proved


end
end PellPaper
