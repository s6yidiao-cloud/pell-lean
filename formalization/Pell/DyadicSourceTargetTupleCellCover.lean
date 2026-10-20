import Pell.DyadicTargetImageGeometry

/-!
# Covering a dyadic factor box by literal source-target tuple cells

Every tuple in a dyadic factor-box cell has an actual source-ratio index and
its own deterministic target right-ceiling index.  The corresponding pair is
retained by `dyadicSourceTargetCellPairs`, so the literal tuple cells cover the
whole factor-box cell.  Finite-union subadditivity then gives the exact sum of
cell cardinalities used by the later thin/full split.

This is only cover bookkeeping.  In particular, it makes no injectivity claim
about the target image of a tuple cell.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- The actual source-target tuple cells indexed by retained nonempty pairs
cover the complete dyadic factor-box cell. -/
theorem dyadicFactorBoxCell_subset_biUnion_sourceTargetTupleCells
    (theta : ℝ) (Y : ℕ) (i : ℕ × ℕ × ℕ × ℕ) {M : ℕ} (hM : 0 < M) :
    dyadicFactorBoxCell theta Y i ⊆
      (dyadicSourceTargetCellPairs theta Y i M).biUnion
        (fun p => dyadicSourceTargetTupleCell theta Y i M p.1 p.2) := by
  intro q hq
  obtain ⟨p, hp, hlocal, htarget⟩ :=
    exists_dyadicSourceTargetCellPair_covering theta Y i hM hq
  apply Finset.mem_biUnion.mpr
  refine ⟨p, hp, ?_⟩
  exact Finset.mem_filter.mpr ⟨hlocal, htarget⟩

/-- Natural-number cardinality form of finite-union subadditivity for the
literal source-target cell cover. -/
theorem card_dyadicFactorBoxCell_le_sum_card_sourceTargetTupleCells
    (theta : ℝ) (Y : ℕ) (i : ℕ × ℕ × ℕ × ℕ) {M : ℕ} (hM : 0 < M) :
    (dyadicFactorBoxCell theta Y i).card ≤
      ∑ p ∈ dyadicSourceTargetCellPairs theta Y i M,
        (dyadicSourceTargetTupleCell theta Y i M p.1 p.2).card := by
  exact
    (Finset.card_le_card
      (dyadicFactorBoxCell_subset_biUnion_sourceTargetTupleCells
        theta Y i hM)).trans
      Finset.card_biUnion_le

/-- Real-cast form of the same cover bound, ready for the real-valued local
counting estimates. -/
theorem card_dyadicFactorBoxCell_cast_le_sum_card_sourceTargetTupleCells
    (theta : ℝ) (Y : ℕ) (i : ℕ × ℕ × ℕ × ℕ) {M : ℕ} (hM : 0 < M) :
    ((dyadicFactorBoxCell theta Y i).card : ℝ) ≤
      ∑ p ∈ dyadicSourceTargetCellPairs theta Y i M,
        ((dyadicSourceTargetTupleCell theta Y i M p.1 p.2).card : ℝ) := by
  exact_mod_cast
    card_dyadicFactorBoxCell_le_sum_card_sourceTargetTupleCells theta Y i hM

end

end PellPaper
