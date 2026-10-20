import Pell.UnbalancedShiftedSquareDyadicCover
import Pell.Main3BalancedRangeThreshold
import Mathlib.Tactic

/-!
# Exact active/direct/analytic split at the enlarged main3 Pell exponent

The finite dyadic cover at Pell exponent `theta + 1/4` deliberately contains
broad parameter indices whose source fibres may be empty.  This file filters
that family at analytic threshold `R = main3BalancedR theta Y` to the genuinely
active indices, retaining the nonempty-cell evidence needed by later pointwise
estimates.

It then partitions the active family at the manuscript endpoint threshold
corresponding to `beta_u = 1/8`:

`N <= Y^(3/2 - 1/(32*theta^2))`.

The admissible tuple cardinality is re-covered directly by the active
families before the squarefree shifted-block sums are split.  Thus no
admissibility property is inferred from membership in the broad index family
alone, and no analytic estimate is asserted.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- The manuscript `beta_u = 1/8` endpoint separating the direct and
large-analytic parts of the active unbalanced cover. -/
def main3UnbalancedEnlargedDirectNThreshold (theta : ℝ) (Y : ℕ) : ℝ :=
  (Y : ℝ) ^ ((3 : ℝ) / 2 - 1 / (32 * theta ^ 2))

/-- Broad main3 cover indices whose literal source fibre is nonempty. -/
noncomputable def main3UnbalancedEnlargedActiveDyadicCoverIndices
    (theta : ℝ) (Y : ℕ) : Finset (ℤ × ℕ × ℕ × ℕ) :=
  (unbalancedShiftedSquareDyadicCoverIndices
      (theta + 1 / 4) Y (main3BalancedR theta Y)).filter fun i =>
    (unbalancedShiftedSquareDyadicCoverCell
      (theta + 1 / 4) Y (main3BalancedR theta Y) i).Nonempty

@[simp] theorem mem_main3UnbalancedEnlargedActiveDyadicCoverIndices
    {theta : ℝ} {Y : ℕ} {i : ℤ × ℕ × ℕ × ℕ} :
    i ∈ main3UnbalancedEnlargedActiveDyadicCoverIndices theta Y ↔
      i ∈ unbalancedShiftedSquareDyadicCoverIndices
        (theta + 1 / 4) Y (main3BalancedR theta Y) ∧
      (unbalancedShiftedSquareDyadicCoverCell
        (theta + 1 / 4) Y (main3BalancedR theta Y) i).Nonempty := by
  simp [main3UnbalancedEnlargedActiveDyadicCoverIndices]

/-- Active indices retain their broad-cover membership.  The converse is
intentionally not claimed. -/
theorem main3UnbalancedEnlargedActiveDyadicCoverIndices_subset_broad
    (theta : ℝ) (Y : ℕ) :
    main3UnbalancedEnlargedActiveDyadicCoverIndices theta Y ⊆
      unbalancedShiftedSquareDyadicCoverIndices
        (theta + 1 / 4) Y (main3BalancedR theta Y) := by
  intro i hi
  exact (mem_main3UnbalancedEnlargedActiveDyadicCoverIndices.mp hi).1

/-- Active indices whose `N` endpoint is at or below the manuscript direct
threshold. -/
noncomputable def main3UnbalancedEnlargedDirectDyadicCoverIndices
    (theta : ℝ) (Y : ℕ) : Finset (ℤ × ℕ × ℕ × ℕ) :=
  (main3UnbalancedEnlargedActiveDyadicCoverIndices theta Y).filter fun i =>
    (i.2.2.2 : ℝ) ≤ main3UnbalancedEnlargedDirectNThreshold theta Y

/-- The complementary active family, reserved for a later large-`N`
analytic input. -/
noncomputable def main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices
    (theta : ℝ) (Y : ℕ) : Finset (ℤ × ℕ × ℕ × ℕ) :=
  (main3UnbalancedEnlargedActiveDyadicCoverIndices theta Y).filter fun i =>
    ¬(i.2.2.2 : ℝ) ≤ main3UnbalancedEnlargedDirectNThreshold theta Y

@[simp] theorem mem_main3UnbalancedEnlargedDirectDyadicCoverIndices
    {theta : ℝ} {Y : ℕ} {i : ℤ × ℕ × ℕ × ℕ} :
    i ∈ main3UnbalancedEnlargedDirectDyadicCoverIndices theta Y ↔
      i ∈ main3UnbalancedEnlargedActiveDyadicCoverIndices theta Y ∧
      (i.2.2.2 : ℝ) ≤ main3UnbalancedEnlargedDirectNThreshold theta Y := by
  simp [main3UnbalancedEnlargedDirectDyadicCoverIndices]

@[simp] theorem mem_main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices
    {theta : ℝ} {Y : ℕ} {i : ℤ × ℕ × ℕ × ℕ} :
    i ∈ main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y ↔
      i ∈ main3UnbalancedEnlargedActiveDyadicCoverIndices theta Y ∧
      main3UnbalancedEnlargedDirectNThreshold theta Y < (i.2.2.2 : ℝ) := by
  simp [main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices, not_le]

/-- The two endpoint ranges are disjoint. -/
theorem main3UnbalancedEnlargedDirect_disjoint_largeAnalytic
    (theta : ℝ) (Y : ℕ) :
    Disjoint (main3UnbalancedEnlargedDirectDyadicCoverIndices theta Y)
      (main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y) := by
  classical
  simpa only [main3UnbalancedEnlargedDirectDyadicCoverIndices,
    main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices] using
    (Finset.disjoint_filter_filter_not
      (main3UnbalancedEnlargedActiveDyadicCoverIndices theta Y)
      (main3UnbalancedEnlargedActiveDyadicCoverIndices theta Y)
      (fun i : ℤ × ℕ × ℕ × ℕ =>
        (i.2.2.2 : ℝ) ≤ main3UnbalancedEnlargedDirectNThreshold theta Y))

/-- The direct and large-analytic endpoint ranges exhaust the active
indices exactly. -/
theorem main3UnbalancedEnlargedDirect_union_largeAnalytic
    (theta : ℝ) (Y : ℕ) :
    main3UnbalancedEnlargedDirectDyadicCoverIndices theta Y ∪
        main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y =
      main3UnbalancedEnlargedActiveDyadicCoverIndices theta Y := by
  classical
  simpa only [main3UnbalancedEnlargedDirectDyadicCoverIndices,
    main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices] using
    (Finset.filter_union_filter_not_eq
      (p := fun i : ℤ × ℕ × ℕ × ℕ =>
        (i.2.2.2 : ℝ) ≤ main3UnbalancedEnlargedDirectNThreshold theta Y)
      (main3UnbalancedEnlargedActiveDyadicCoverIndices theta Y))

/-- Union of the genuinely active main3 source fibres. -/
noncomputable def main3UnbalancedEnlargedActiveDyadicCoverUnion
    (theta : ℝ) (Y : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  (main3UnbalancedEnlargedActiveDyadicCoverIndices theta Y).biUnion
    (unbalancedShiftedSquareDyadicCoverCell
      (theta + 1 / 4) Y (main3BalancedR theta Y))

/-- Every admissible main3 unbalanced tuple is covered by an active index.
The proof extracts its broad covering cell and promotes that index using the
tuple itself as explicit nonemptiness evidence. -/
theorem admissibleUnbalancedDyadicFactorTuples_subset_main3EnlargedActiveCoverUnion
    (theta : ℝ) (Y : ℕ) :
    admissibleUnbalancedDyadicFactorTuples
        (theta + 1 / 4) Y (main3BalancedR theta Y) ⊆
      main3UnbalancedEnlargedActiveDyadicCoverUnion theta Y := by
  classical
  intro p hp
  have hpBroad :
      p ∈ unbalancedShiftedSquareDyadicCoverUnion
        (theta + 1 / 4) Y (main3BalancedR theta Y) :=
    admissibleUnbalancedDyadicFactorTuples_subset_shiftedSquareDyadicCoverUnion
      (theta + 1 / 4) Y (main3BalancedR theta Y) hp
  obtain ⟨i, hi, hpi⟩ := Finset.mem_biUnion.mp hpBroad
  apply Finset.mem_biUnion.mpr
  refine ⟨i, ?_, hpi⟩
  exact mem_main3UnbalancedEnlargedActiveDyadicCoverIndices.mpr
    ⟨hi, ⟨p, hpi⟩⟩

/-- Overlap-safe active-cover reduction.  Empty broad cells have been
removed before the union cardinality is bounded by the sum of cell
cardinalities and then by the squarefree shifted-square blocks. -/
theorem card_admissibleUnbalancedDyadicFactorTuples_le_main3EnlargedActiveBlockSum
    (theta : ℝ) (Y : ℕ) :
    (admissibleUnbalancedDyadicFactorTuples
      (theta + 1 / 4) Y (main3BalancedR theta Y)).card ≤
      ∑ i ∈ main3UnbalancedEnlargedActiveDyadicCoverIndices theta Y,
        (squarefreeShiftedSquareBlock
          (shiftedSquareA i.1 i.2.1) i.2.2.1 Y i.2.2.2).card := by
  classical
  calc
    (admissibleUnbalancedDyadicFactorTuples
        (theta + 1 / 4) Y (main3BalancedR theta Y)).card ≤
        (main3UnbalancedEnlargedActiveDyadicCoverUnion theta Y).card :=
      Finset.card_le_card
        (admissibleUnbalancedDyadicFactorTuples_subset_main3EnlargedActiveCoverUnion
          theta Y)
    _ ≤ ∑ i ∈ main3UnbalancedEnlargedActiveDyadicCoverIndices theta Y,
          (unbalancedShiftedSquareDyadicCoverCell
            (theta + 1 / 4) Y (main3BalancedR theta Y) i).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ i ∈ main3UnbalancedEnlargedActiveDyadicCoverIndices theta Y,
          (squarefreeShiftedSquareBlock
            (shiftedSquareA i.1 i.2.1) i.2.2.1 Y i.2.2.2).card := by
      apply Finset.sum_le_sum
      intro i hi
      exact card_admissibleUnbalancedShiftedSquareFibre_le_squarefreeBlock

/-- Exact decomposition of the active shifted-block sum at the manuscript
`N` threshold. -/
theorem main3UnbalancedEnlargedActiveBlockSum_eq_direct_add_largeAnalytic
    (theta : ℝ) (Y : ℕ) :
    (∑ i ∈ main3UnbalancedEnlargedActiveDyadicCoverIndices theta Y,
        (squarefreeShiftedSquareBlock
          (shiftedSquareA i.1 i.2.1) i.2.2.1 Y i.2.2.2).card) =
      (∑ i ∈ main3UnbalancedEnlargedDirectDyadicCoverIndices theta Y,
        (squarefreeShiftedSquareBlock
          (shiftedSquareA i.1 i.2.1) i.2.2.1 Y i.2.2.2).card) +
      ∑ i ∈ main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y,
        (squarefreeShiftedSquareBlock
          (shiftedSquareA i.1 i.2.1) i.2.2.1 Y i.2.2.2).card := by
  classical
  rw [← main3UnbalancedEnlargedDirect_union_largeAnalytic theta Y,
    Finset.sum_union (main3UnbalancedEnlargedDirect_disjoint_largeAnalytic theta Y)]

/-- Final exact-finite reduction with the active block sum split into its
direct and large-analytic pieces.  No estimate for either summand is used. -/
theorem card_admissibleUnbalancedDyadicFactorTuples_le_main3EnlargedDirect_add_largeAnalytic
    (theta : ℝ) (Y : ℕ) :
    (admissibleUnbalancedDyadicFactorTuples
      (theta + 1 / 4) Y (main3BalancedR theta Y)).card ≤
      (∑ i ∈ main3UnbalancedEnlargedDirectDyadicCoverIndices theta Y,
        (squarefreeShiftedSquareBlock
          (shiftedSquareA i.1 i.2.1) i.2.2.1 Y i.2.2.2).card) +
      ∑ i ∈ main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y,
        (squarefreeShiftedSquareBlock
          (shiftedSquareA i.1 i.2.1) i.2.2.1 Y i.2.2.2).card := by
  exact (card_admissibleUnbalancedDyadicFactorTuples_le_main3EnlargedActiveBlockSum
    theta Y).trans_eq
      (main3UnbalancedEnlargedActiveBlockSum_eq_direct_add_largeAnalytic theta Y)

end

end PellPaper
