import Pell.Main3BalancedFinal
import Pell.Main3UnbalancedEnlargedDirectScaleAbsorption
import Pell.Main3UnbalancedEnlargedActiveDyadicSplit
import Pell.UnbalancedShiftAdmissibility
import Mathlib.Tactic

/-!
# Lower-evidence boundary for the remaining large-analytic block sum

The manuscript's balanced and direct unbalanced estimates have already been
formalized from the two named class-(B) analytic inputs.  The remaining
large-analytic summation is isolated here as one explicit class-(C),
lower-evidence premise.  Its statement is the exact public block sum required
by the downstream proof: it does not assume any balanced estimate, square-part
reduction, global assembly, `UniformExceptionalEstimate`, or class-number
conclusion.
-/

namespace PellPaper

open Filter

noncomputable section

/-- **Evidence class C (lower-evidence premise).**  This is the one remaining
large-analytic estimate from Section 4 of the manuscript, stated at the stable
public summation boundary.  It is deliberately a `Prop` supplied as an
explicit theorem premise, not a Lean axiom.

The dependence on `OneVariableQuadraticWeilDegreeBound` is exposed rather than
silently folded into the premise.  The witnesses and eventual quantifiers
retain the manuscript's required uniformity: `C` is absolute, while the cutoff
may depend on the fixed admissibility constant `c` but precedes `theta`. -/
def Main3LargeAnalyticBlockSumEstimateLowerEvidence : Prop :=
  OneVariableQuadraticWeilDegreeBound →
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

/-- The checked balanced estimate, checked direct-unbalanced estimate, and the
single lower-evidence large-analytic premise imply a uniform dyadic estimate
for the squarefree exceptional count.  This theorem is class-(A) assembly; its
constant is exactly `35 + 2 + C` from the three summands. -/
theorem exists_pos_uniform_squarefreeDyadicExceptionalCount_cast_le_of_main3BlockEstimates
    (hWeil : OneVariableQuadraticWeilDegreeBound)
    (haverage : ShiftedSquareCongruenceWindowAverageAssertion)
    (hLarge : Main3LargeAnalyticBlockSumEstimateLowerEvidence) :
    ∃ C : ℝ, 0 < C ∧
      ∀ c : ℝ, 0 < c →
        10 * c ^ 2 ≤ (1 : ℝ) / 2400 →
        ∀ᶠ Y : ℕ in atTop, ∀ theta : ℝ,
          3 ≤ theta →
          theta ≤ c * Real.sqrt
            (Real.log (Y : ℝ) / Real.log (Real.log (Y : ℝ))) →
          (squarefreeDyadicExceptionalCount (theta + 1 / 4) Y : ℝ) ≤
            C * (Y : ℝ) ^ (1 - 1 / (400 * theta ^ 2)) := by
  obtain ⟨C, hC, hLargeAll⟩ := hLarge hWeil
  refine ⟨37 + C, by linarith, ?_⟩
  intro c hc hsmall
  have hBalanced :=
    eventually_main3BalancedDyadicFactorTuples_card_le hWeil c hc hsmall
  have hDirect :=
    eventually_main3UnbalancedEnlargedDirectBlockSum_cast_le_of_congruenceWindowAverage
      haverage c hc hsmall
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

/-- Fixed-`c` specialization of the preceding absolute-constant theorem. -/
theorem eventually_squarefreeDyadicExceptionalCount_cast_le_of_main3BlockEstimates
    (hWeil : OneVariableQuadraticWeilDegreeBound)
    (haverage : ShiftedSquareCongruenceWindowAverageAssertion)
    (hLarge : Main3LargeAnalyticBlockSumEstimateLowerEvidence)
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
    exists_pos_uniform_squarefreeDyadicExceptionalCount_cast_le_of_main3BlockEstimates
      hWeil haverage hLarge
  exact ⟨C, hC, hAll c hc hsmall⟩

end

end PellPaper
