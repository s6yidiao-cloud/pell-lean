import Pell.AnnularMultiplicativeCellCover
import Pell.RealSquareMapTargetCellCompatibility

/-!
# Finite real source-target cell pairs for a perturbed square map

This module combines the signed annular source cover with the nine compatible
target offsets for the perturbed square relation.  A finite family of real
pairs `(x,y)` satisfying

`F⁻² ≤ |x| ≤ F²`, `x ≠ 0`, `0 ≤ y`, and `|y/x²-1| ≤ 1/M`

is covered by a literal family of

`36 * M * dyadicScaleCount (ceil(F)^4)`

source-target cell pairs.  Each source cell has relative width `1+1/M`, and
each source cell admits exactly the same nine possible target offsets.

This is finite geometric bookkeeping only.  It makes no assertion about
number-field embeddings, determinant decay, auxiliary forms, or arithmetic
point counts.
-/

namespace PellPaper

noncomputable section

/-- One signed annular source index paired with one of the nine compatible
target offsets. -/
abbrev RealSquareMapCellPairIndex :=
  AnnularMultiplicativeCellIndex × ℤ

/-- The literal finite family of compatible real square-map cell pairs. -/
def realSquareMapCellPairIndices (F : ℝ) (M : ℕ) :
    Finset RealSquareMapCellPairIndex :=
  (annularMultiplicativeCellIndices F M).product realSquareMapTargetOffsets

/-- Pointwise membership in one source-target cell pair. -/
def InRealSquareMapCellPair
    (F : ℝ) (M : ℕ) (i : RealSquareMapCellPairIndex)
    (p : ℝ × ℝ) : Prop :=
  InAnnularMultiplicativeCell F M i.1 p.1 ∧
    realSquareMapTargetCell (M : ℝ)
      (annularMultiplicativeCenter F M i.1.2.1 i.1.2.2) i.2 p.2

/-- The portion of a finite real-pair family lying in one literal cell pair. -/
noncomputable def realSquareMapCellPair
    (S : Finset (ℝ × ℝ)) (F : ℝ) (M : ℕ)
    (i : RealSquareMapCellPairIndex) : Finset (ℝ × ℝ) := by
  classical
  exact S.filter (InRealSquareMapCellPair F M i)

/-- The exact number of source-target cell-pair indices. -/
@[simp]
theorem card_realSquareMapCellPairIndices (F : ℝ) (M : ℕ) :
    (realSquareMapCellPairIndices F M).card =
      36 * M * annularDyadicScaleCount F := by
  simp [realSquareMapCellPairIndices]
  ring

/-- Pointwise cover by one signed source cell and one of its nine compatible
target offsets. -/
theorem exists_mem_realSquareMapCellPair
    {F : ℝ} {M : ℕ} {x y : ℝ}
    (hF : 1 ≤ F) (hM : 0 < M) (hx : x ≠ 0)
    (hlower : annularLowerRadius F ≤ |x|)
    (hupper : |x| ≤ F ^ 2) (hy : 0 ≤ y)
    (herror : |y / |x| ^ 2 - 1| ≤ 1 / (M : ℝ)) :
    ∃ i ∈ realSquareMapCellPairIndices F M,
      InRealSquareMapCellPair F M i (x, y) := by
  obtain ⟨src, hsrcIndex, hsrcCell⟩ :=
    exists_mem_annularMultiplicativeCell hF hM hx hlower hupper
  let s : ℝ := annularMultiplicativeCenter F M src.2.1 src.2.2
  have hs : 0 < s := by
    dsimp only [s, annularMultiplicativeCenter]
    exact mul_pos (annularDyadicStart_pos hF src.2.1)
      (pow_pos (by
        unfold localRatioMeshStep
        positivity) _)
  have hxabs : 0 < |x| := abs_pos.mpr hx
  have hMreal : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  obtain ⟨k, hkOffset, hkCell⟩ :=
    exists_realSquareMapTargetOffset_mem_of_sourceWindow
      hMreal hs hxabs hy hsrcCell.2 herror
  refine ⟨(src, k), ?_, ?_⟩
  · exact Finset.mem_product.mpr ⟨hsrcIndex, hkOffset⟩
  · exact ⟨hsrcCell, by simpa only [s] using hkCell⟩

/-- Membership in a literal finite cell pair retains ambient membership and
exposes both exact local predicates. -/
theorem mem_realSquareMapCellPair
    {S : Finset (ℝ × ℝ)} {F : ℝ} {M : ℕ}
    {i : RealSquareMapCellPairIndex} {p : ℝ × ℝ}
    (hp : p ∈ realSquareMapCellPair S F M i) :
    p ∈ S ∧ InRealSquareMapCellPair F M i p := by
  classical
  simpa only [realSquareMapCellPair] using Finset.mem_filter.mp hp

/-- Every literal cell pair is a subfinset of the ambient pair family. -/
theorem realSquareMapCellPair_subset
    (S : Finset (ℝ × ℝ)) (F : ℝ) (M : ℕ)
    (i : RealSquareMapCellPairIndex) :
    realSquareMapCellPair S F M i ⊆ S := by
  intro p hp
  exact (mem_realSquareMapCellPair hp).1

/-- The exact local source and target windows supplied by cell-pair
membership. -/
theorem realSquareMapCellPair_commonWindows
    {S : Finset (ℝ × ℝ)} {F : ℝ} {M : ℕ}
    {i : RealSquareMapCellPairIndex} {p : ℝ × ℝ}
    (hp : p ∈ realSquareMapCellPair S F M i) :
    p.1 = (i.1.1 : ℝ) * |p.1| ∧
      annularMultiplicativeCenter F M i.1.2.1 i.1.2.2 ≤ |p.1| ∧
      |p.1| ≤ annularMultiplicativeCenter F M i.1.2.1 i.1.2.2 *
        (1 + 1 / (M : ℝ)) ∧
      realSquareMapTargetCell (M : ℝ)
        (annularMultiplicativeCenter F M i.1.2.1 i.1.2.2) i.2 p.2 := by
  have h := (mem_realSquareMapCellPair hp).2
  simpa [InRealSquareMapCellPair, InAnnularMultiplicativeCell,
    localRatioMeshStep, and_assoc] using h

/-- A finite family satisfying the annular perturbed-square hypotheses is
covered by the literal finite family of source-target cell pairs. -/
theorem realSquareMapPairFinset_subset_biUnion_cells
    (S : Finset (ℝ × ℝ)) {F : ℝ} {M : ℕ}
    (hF : 1 ≤ F) (hM : 0 < M)
    (hS : ∀ p ∈ S,
      p.1 ≠ 0 ∧ annularLowerRadius F ≤ |p.1| ∧ |p.1| ≤ F ^ 2 ∧
        0 ≤ p.2 ∧ |p.2 / |p.1| ^ 2 - 1| ≤ 1 / (M : ℝ)) :
    S ⊆ (realSquareMapCellPairIndices F M).biUnion
      (realSquareMapCellPair S F M) := by
  intro p hp
  obtain ⟨hx, hlower, hupper, hy, herror⟩ := hS p hp
  obtain ⟨i, hi, hcell⟩ :=
    exists_mem_realSquareMapCellPair hF hM hx hlower hupper hy herror
  apply Finset.mem_biUnion.mpr
  refine ⟨i, hi, ?_⟩
  classical
  simpa only [realSquareMapCellPair] using
    (Finset.mem_filter.mpr ⟨hp, hcell⟩)

/-- Overlap-safe cardinality consequence of the finite real cell-pair cover. -/
theorem card_realSquareMapPairFinset_le_sum_card_cells
    (S : Finset (ℝ × ℝ)) {F : ℝ} {M : ℕ}
    (hF : 1 ≤ F) (hM : 0 < M)
    (hS : ∀ p ∈ S,
      p.1 ≠ 0 ∧ annularLowerRadius F ≤ |p.1| ∧ |p.1| ≤ F ^ 2 ∧
        0 ≤ p.2 ∧ |p.2 / |p.1| ^ 2 - 1| ≤ 1 / (M : ℝ)) :
    S.card ≤ ∑ i ∈ realSquareMapCellPairIndices F M,
      (realSquareMapCellPair S F M i).card := by
  exact (Finset.card_le_card
    (realSquareMapPairFinset_subset_biUnion_cells S hF hM hS)).trans
      Finset.card_biUnion_le

end

end PellPaper
