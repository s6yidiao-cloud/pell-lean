import Pell.DyadicCountingReduction

/-!
# Balanced and unbalanced factor ranges

The oriented factor tuples from `DyadicCountingReduction` have a preferred
squarefree coordinate `v`, with `v ≤ u`.  This file performs the elementary
finite split at an arbitrary natural threshold `R`.  It deliberately makes
no claim about either resulting cardinality; those are the separate balanced
determinant and unbalanced divisor problems in the manuscript.
-/

namespace PellPaper

/-- The tuples whose oriented squarefree coordinate is at least the chosen
threshold. -/
noncomputable def balancedDyadicFactorTuples (θ : ℝ) (Y R : ℕ) :
    Finset (ℕ × ℕ × ℕ × ℕ) := by
  classical
  exact (dyadicFactorTuples θ Y).filter fun p => R ≤ p.2.2.2

/-- The tuples whose oriented squarefree coordinate is below the chosen
threshold. -/
noncomputable def unbalancedDyadicFactorTuples (θ : ℝ) (Y R : ℕ) :
    Finset (ℕ × ℕ × ℕ × ℕ) := by
  classical
  exact (dyadicFactorTuples θ Y).filter fun p => p.2.2.2 < R

@[simp] theorem mem_balancedDyadicFactorTuples {θ : ℝ} {Y R : ℕ}
    {p : ℕ × ℕ × ℕ × ℕ} :
    p ∈ balancedDyadicFactorTuples θ Y R ↔
      p ∈ dyadicFactorTuples θ Y ∧ R ≤ p.2.2.2 := by
  classical
  simp [balancedDyadicFactorTuples]

@[simp] theorem mem_unbalancedDyadicFactorTuples {θ : ℝ} {Y R : ℕ}
    {p : ℕ × ℕ × ℕ × ℕ} :
    p ∈ unbalancedDyadicFactorTuples θ Y R ↔
      p ∈ dyadicFactorTuples θ Y ∧ p.2.2.2 < R := by
  classical
  simp [unbalancedDyadicFactorTuples]

/-- The two ranges exhaust the bounded factor tuples.  This has no lower
bound hypothesis on `R`, so in particular it covers the empty unbalanced
range at `R = 0`. -/
theorem dyadicFactorTuples_eq_balanced_union_unbalanced (θ : ℝ) (Y R : ℕ) :
    dyadicFactorTuples θ Y =
      balancedDyadicFactorTuples θ Y R ∪ unbalancedDyadicFactorTuples θ Y R := by
  classical
  ext p
  by_cases hR : R ≤ p.2.2.2
  · simp [hR, not_lt_of_ge hR]
  · have hlt : p.2.2.2 < R := Nat.lt_of_not_ge hR
    simp [hR, hlt]

/-- The balanced and unbalanced ranges are disjoint, including at the
boundary `R = 0`. -/
theorem disjoint_balancedDyadicFactorTuples_unbalancedDyadicFactorTuples
    (θ : ℝ) (Y R : ℕ) :
    Disjoint (balancedDyadicFactorTuples θ Y R)
      (unbalancedDyadicFactorTuples θ Y R) := by
  classical
  refine Finset.disjoint_left.mpr ?_
  intro p hpBalanced hpUnbalanced
  have hBalanced := (mem_balancedDyadicFactorTuples.mp hpBalanced).2
  have hUnbalanced := (mem_unbalancedDyadicFactorTuples.mp hpUnbalanced).2
  exact (not_lt_of_ge hBalanced) hUnbalanced

/-- At the zero threshold every natural coordinate lies in the balanced
range. -/
theorem balancedDyadicFactorTuples_zero (θ : ℝ) (Y : ℕ) :
    balancedDyadicFactorTuples θ Y 0 = dyadicFactorTuples θ Y := by
  classical
  ext p
  simp

/-- At the zero threshold the unbalanced range is empty. -/
theorem unbalancedDyadicFactorTuples_zero (θ : ℝ) (Y : ℕ) :
    unbalancedDyadicFactorTuples θ Y 0 = ∅ := by
  classical
  ext p
  simp

/-- Exact cardinality additivity for the factor-range split. -/
theorem card_dyadicFactorTuples_eq_balanced_add_unbalanced (θ : ℝ) (Y R : ℕ) :
    (dyadicFactorTuples θ Y).card =
      (balancedDyadicFactorTuples θ Y R).card +
        (unbalancedDyadicFactorTuples θ Y R).card := by
  rw [dyadicFactorTuples_eq_balanced_union_unbalanced]
  exact Finset.card_union_of_disjoint
    (disjoint_balancedDyadicFactorTuples_unbalancedDyadicFactorTuples θ Y R)

/-- The weak form of the split, convenient when the two ranges are estimated
separately. -/
theorem card_dyadicFactorTuples_le_balanced_add_unbalanced (θ : ℝ) (Y R : ℕ) :
    (dyadicFactorTuples θ Y).card ≤
      (balancedDyadicFactorTuples θ Y R).card +
        (unbalancedDyadicFactorTuples θ Y R).card := by
  exact (card_dyadicFactorTuples_eq_balanced_add_unbalanced θ Y R).le

/-- Combining the finite factor reduction with the threshold split reduces
the squarefree dyadic exceptional count to the two separate ranges. -/
theorem squarefreeDyadicExceptionalCount_le_balanced_add_unbalanced {θ : ℝ} {Y R : ℕ}
    (hθ : 0 ≤ θ) :
    squarefreeDyadicExceptionalCount θ Y ≤
      (balancedDyadicFactorTuples θ Y R).card +
        (unbalancedDyadicFactorTuples θ Y R).card := by
  exact (squarefreeDyadicExceptionalCount_le_factor_card hθ).trans
    (card_dyadicFactorTuples_le_balanced_add_unbalanced θ Y R)

end PellPaper
