import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Pell.DyadicBoxReduction

/-!
# Sparse-versus-heavy finite cell accounting

The dyadic and lattice arguments in `main.tex` divide a finite point family
into cell pairs.  Cells holding fewer than a threshold number of points are
discarded at cost `O(H · #cells)`; the remaining points are confined to the
heavy cells, where an auxiliary-form or sieve argument is applied.

This module isolates that finite bookkeeping.  Cells may overlap: the bounds
charge a union by the sum of its cell cardinalities, so no unproved partition
or disjointness condition is implicit.  It contains no lattice estimate,
determinant estimate, or point-counting assertion.
-/

namespace PellPaper

open scoped BigOperators

/-- The union of a finite indexed family of cells. -/
def finiteCellUnion {ι α : Type*} [DecidableEq α]
    (I : Finset ι) (cells : ι → Finset α) : Finset α :=
  I.biUnion cells

/-- The union of the cells whose occupancy is strictly below `H`. -/
def sparseCellUnion {ι α : Type*} [DecidableEq α]
    (I : Finset ι) (cells : ι → Finset α) (H : ℕ) : Finset α :=
  I.biUnion fun i => if (cells i).card < H then cells i else ∅

/-- The union of the cells whose occupancy is at least `H`. -/
def heavyCellUnion {ι α : Type*} [DecidableEq α]
    (I : Finset ι) (cells : ι → Finset α) (H : ℕ) : Finset α :=
  I.biUnion fun i => if H ≤ (cells i).card then cells i else ∅

/-- Membership in the union of all cells is witnessed by one displayed
cell. -/
theorem mem_finiteCellUnion_iff {ι α : Type*} [DecidableEq α]
    {I : Finset ι} {cells : ι → Finset α} {x : α} :
    x ∈ finiteCellUnion I cells ↔ ∃ i ∈ I, x ∈ cells i := by
  exact Finset.mem_biUnion

/-- Membership in the sparse union records both the cell witness and the
strict occupancy inequality. -/
theorem mem_sparseCellUnion_iff {ι α : Type*} [DecidableEq α]
    {I : Finset ι} {cells : ι → Finset α} {H : ℕ} {x : α} :
    x ∈ sparseCellUnion I cells H ↔
      ∃ i ∈ I, (cells i).card < H ∧ x ∈ cells i := by
  constructor
  · intro hx
    rcases Finset.mem_biUnion.mp hx with ⟨i, hi, hxi⟩
    by_cases hsmall : (cells i).card < H
    · refine ⟨i, hi, hsmall, ?_⟩
      simpa [sparseCellUnion, hsmall] using hxi
    · simp [hsmall] at hxi
  · rintro ⟨i, hi, hsmall, hxi⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨i, hi, ?_⟩
    simpa [sparseCellUnion, hsmall] using hxi

/-- Membership in the heavy union records both the cell witness and the
lower occupancy inequality. -/
theorem mem_heavyCellUnion_iff {ι α : Type*} [DecidableEq α]
    {I : Finset ι} {cells : ι → Finset α} {H : ℕ} {x : α} :
    x ∈ heavyCellUnion I cells H ↔
      ∃ i ∈ I, H ≤ (cells i).card ∧ x ∈ cells i := by
  constructor
  · intro hx
    rcases Finset.mem_biUnion.mp hx with ⟨i, hi, hxi⟩
    by_cases hheavy : H ≤ (cells i).card
    · refine ⟨i, hi, hheavy, ?_⟩
      simpa [heavyCellUnion, hheavy] using hxi
    · simp [hheavy] at hxi
  · rintro ⟨i, hi, hheavy, hxi⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨i, hi, ?_⟩
    simpa [heavyCellUnion, hheavy] using hxi

/-- Every point in a displayed cell lies either in a sparse cell or in a
heavy cell.  This is a finite occupancy dichotomy and does not require the
cells to be disjoint. -/
theorem finiteCellUnion_subset_sparseCellUnion_union_heavyCellUnion
    {ι α : Type*} [DecidableEq α] (I : Finset ι) (cells : ι → Finset α)
    (H : ℕ) :
    finiteCellUnion I cells ⊆
      sparseCellUnion I cells H ∪ heavyCellUnion I cells H := by
  intro x hx
  rcases mem_finiteCellUnion_iff.mp hx with ⟨i, hi, hxi⟩
  by_cases hsmall : (cells i).card < H
  · apply Finset.mem_union_left
    exact mem_sparseCellUnion_iff.mpr ⟨i, hi, hsmall, hxi⟩
  · apply Finset.mem_union_right
    exact mem_heavyCellUnion_iff.mpr
      ⟨i, hi, Nat.le_of_not_gt hsmall, hxi⟩

/-- The total number of points occurring in sparse cells is at most the
number of cells times the sparsity threshold.  The estimate is valid even
for `H = 0` and even when cells overlap. -/
theorem card_sparseCellUnion_le_cellCount_mul_threshold
    {ι α : Type*} [DecidableEq α] (I : Finset ι) (cells : ι → Finset α)
    (H : ℕ) :
    (sparseCellUnion I cells H).card ≤ I.card * H := by
  unfold sparseCellUnion
  apply Finset.card_biUnion_le_card_mul I
  intro i hi
  by_cases hsmall : (cells i).card < H
  · simpa [hsmall] using Nat.le_of_lt hsmall
  · simp [hsmall]

/-- If a finite point family is covered by the displayed cells, then it is
bounded by the sparse-cell budget plus the number of points lying in heavy
cells.  This is the exact finite reduction used before applying a curve or
sieve bound on the heavy cells. -/
theorem card_le_cellCount_mul_threshold_add_heavyCellUnion_of_subset
    {ι α : Type*} [DecidableEq α] {I : Finset ι} {cells : ι → Finset α}
    {H : ℕ} {S : Finset α} (hcover : S ⊆ finiteCellUnion I cells) :
    S.card ≤ I.card * H + (heavyCellUnion I cells H).card := by
  calc
    S.card ≤ (finiteCellUnion I cells).card := Finset.card_le_card hcover
    _ ≤ (sparseCellUnion I cells H ∪ heavyCellUnion I cells H).card :=
      Finset.card_le_card
        (finiteCellUnion_subset_sparseCellUnion_union_heavyCellUnion I cells H)
    _ ≤ (sparseCellUnion I cells H).card + (heavyCellUnion I cells H).card :=
      Finset.card_union_le _ _
    _ ≤ I.card * H + (heavyCellUnion I cells H).card :=
      Nat.add_le_add_right
        (card_sparseCellUnion_le_cellCount_mul_threshold I cells H) _

/-- A pointwise cell-cover hypothesis is a convenient equivalent interface
for the sparse/heavy accounting theorem. -/
theorem card_le_cellCount_mul_threshold_add_heavyCellUnion_of_cover
    {ι α : Type*} [DecidableEq α] {I : Finset ι} {cells : ι → Finset α}
    {H : ℕ} {S : Finset α}
    (hcover : ∀ x ∈ S, ∃ i ∈ I, x ∈ cells i) :
    S.card ≤ I.card * H + (heavyCellUnion I cells H).card := by
  apply card_le_cellCount_mul_threshold_add_heavyCellUnion_of_subset
  intro x hx
  exact mem_finiteCellUnion_iff.mpr (hcover x hx)

/-- The portion of `dyadicFactorTuples` lying in one displayed dyadic box.
This is the literal finite cell family to which the generic sparse/heavy
accounting can be applied before any boxwise determinant estimate. -/
noncomputable def dyadicFactorBoxCell (theta : ℝ) (Y : ℕ)
    (i : ℕ × ℕ × ℕ × ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  dyadicFactorTuples theta Y ∩ dyadicBox i

/-- The actual dyadic factor tuples are covered by their intersections with
the finite family of dyadic boxes. -/
theorem dyadicFactorTuples_subset_finiteCellUnion_dyadicFactorBoxCell
    (theta : ℝ) (Y : ℕ) :
    dyadicFactorTuples theta Y ⊆
      finiteCellUnion (dyadicFactorBoxIndices theta Y)
        (dyadicFactorBoxCell theta Y) := by
  intro p hp
  rcases Finset.mem_biUnion.mp
    (dyadicFactorTuples_subset_dyadicBoxUnion theta Y hp) with ⟨i, hi, hpi⟩
  apply mem_finiteCellUnion_iff.mpr
  exact ⟨i, hi, Finset.mem_inter.mpr ⟨hp, hpi⟩⟩

/-- The finite dyadic reduction with a sparsity threshold: all tuples in
boxes holding fewer than `H` tuples cost at most `H` times the number of
dyadic boxes, while the remaining contribution is localized to the union of
the heavy boxes.  No boxwise counting or determinant estimate is assumed. -/
theorem dyadicFactorTuples_card_le_dyadicBox_sparse_budget_add_heavy
    (theta : ℝ) (Y H : ℕ) :
    (dyadicFactorTuples theta Y).card ≤
      (dyadicFactorBoxIndices theta Y).card * H +
        (heavyCellUnion (dyadicFactorBoxIndices theta Y)
          (dyadicFactorBoxCell theta Y) H).card := by
  apply card_le_cellCount_mul_threshold_add_heavyCellUnion_of_subset
  exact dyadicFactorTuples_subset_finiteCellUnion_dyadicFactorBoxCell theta Y

end PellPaper
