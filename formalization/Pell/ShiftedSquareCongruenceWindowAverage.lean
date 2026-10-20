import Pell.ShiftedSquareCongruenceProjection

/-!
# Standard congruence-window input for the direct shifted-square estimate

The elementary direct estimate reduces to counting pairs `(d,n)` with
`d^2 ∣ n^2 + a` in two half-open intervals.  The standard proof bounds the
number of roots modulo each `d^2` by Hensel lifting and sums the resulting
`2^omega(d)` weight by its classical average order.

Mathlib does not package that complete estimate as one theorem.  We expose it
here as a transparent proposition about the exact finite congruence-pair
family; `Pell.ShiftedSquareCongruenceWindowAverageProof` proves the proposition
from prime-power root counts and a divisor summatory bound.  The
project-specific passage back to shifted-square triples is proved below from
the canonical injection.
-/

namespace PellPaper

noncomputable section

/-- The quadratic-congruence pairs in a dyadic window have their standard
uniform average bound for every nonzero squarefree integer shift. -/
def ShiftedSquareCongruenceWindowAverageAssertion : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (a : ℤ) (D N : ℕ),
      Squarefree a → a ≠ 0 → 1 ≤ D → 1 ≤ N →
      ((shiftedSquareCongruencePairs a D N).card : ℝ) ≤
        C * (((N : ℝ) / (D : ℝ) + (D : ℝ)) *
          (1 + Real.log (2 * (D : ℝ))))

/-- The standard congruence-window input implies the manuscript's direct
bound for the full shifted-square block, with the same uniform constant. -/
theorem shiftedSquareBlock_bound_of_congruenceWindowAverage
    (haverage : ShiftedSquareCongruenceWindowAverageAssertion) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : ℤ) (D Y N : ℕ),
        Squarefree a → a ≠ 0 → 1 ≤ D → 1 ≤ N →
        ((shiftedSquareBlock a D Y N).card : ℝ) ≤
          C * (((N : ℝ) / (D : ℝ) + (D : ℝ)) *
            (1 + Real.log (2 * (D : ℝ)))) := by
  obtain ⟨C, hC, hbound⟩ := haverage
  refine ⟨C, hC, ?_⟩
  intro a D Y N ha ha0 hD hN
  calc
    ((shiftedSquareBlock a D Y N).card : ℝ) ≤
        ((shiftedSquareCongruencePairs a D N).card : ℝ) := by
      exact_mod_cast card_shiftedSquareBlock_le_congruencePairs
    _ ≤ C * (((N : ℝ) / (D : ℝ) + (D : ℝ)) *
          (1 + Real.log (2 * (D : ℝ)))) :=
      hbound a D N ha ha0 hD hN

/-- The same standard input bounds the squarefree-`w` subblock.  No loss or
new hypothesis is introduced by imposing squarefreeness on `w`. -/
theorem squarefreeShiftedSquareBlock_bound_of_congruenceWindowAverage
    (haverage : ShiftedSquareCongruenceWindowAverageAssertion) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : ℤ) (D Y N : ℕ),
        Squarefree a → a ≠ 0 → 1 ≤ D → 1 ≤ N →
        ((squarefreeShiftedSquareBlock a D Y N).card : ℝ) ≤
          C * (((N : ℝ) / (D : ℝ) + (D : ℝ)) *
            (1 + Real.log (2 * (D : ℝ)))) := by
  obtain ⟨C, hC, hbound⟩ := haverage
  refine ⟨C, hC, ?_⟩
  intro a D Y N ha ha0 hD hN
  calc
    ((squarefreeShiftedSquareBlock a D Y N).card : ℝ) ≤
        ((shiftedSquareCongruencePairs a D N).card : ℝ) := by
      exact_mod_cast card_squarefreeShiftedSquareBlock_le_congruencePairs
    _ ≤ C * (((N : ℝ) / (D : ℝ) + (D : ℝ)) *
          (1 + Real.log (2 * (D : ℝ)))) :=
      hbound a D N ha ha0 hD hN

end

end PellPaper
