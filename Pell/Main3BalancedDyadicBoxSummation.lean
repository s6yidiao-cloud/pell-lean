import Pell.FactorRangeSplit
import Pell.DyadicFactorBoxNormalization
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Summing the main3 balanced dyadic boxes

The balanced range in the manuscript is pointwise: the oriented squarefree
coordinate satisfies `R <= v`.  A tuple in the dyadic box with target lower
endpoints `U,V` therefore supplies only the honest endpoint inequalities
`R < 2U` and `R < 2V`.  This file records that fixed dyadic loss, retains only
occupied endpoint-balanced boxes, and partitions them by the literal
high-`DE` condition used by the concrete main3 local theorem.

The final real-valued summation lemmas are the insertion point for the
pointwise high-box and low-box estimates.  No analytic estimate is assumed or
proved here, and no box is silently treated as a disjoint partition cell.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- Occupied boxes which can meet the pointwise balanced range `R <= v`.
The factors two are the exact loss from the half-open dyadic coordinate
intervals. -/
def main3BalancedOccupiedBoxIndices (theta : ℝ) (Y R : ℕ) :
    Finset (ℕ × ℕ × ℕ × ℕ) :=
  (dyadicFactorBoxIndices (theta + 1 / 4) Y).filter fun i =>
    (dyadicFactorBoxCell (theta + 1 / 4) Y i).Nonempty ∧
      R < 2 * 2 ^ i.2.2.1 ∧ R < 2 * 2 ^ i.2.2.2

/-- The occupied balanced endpoint boxes in the high-`DE` alternative of
the manuscript. -/
def main3BalancedHighDEBoxIndices (theta : ℝ) (Y R : ℕ) :
    Finset (ℕ × ℕ × ℕ × ℕ) :=
  (main3BalancedOccupiedBoxIndices theta Y R).filter fun i =>
    (Y : ℝ) ^ (1 - 1 / (100 * theta ^ 2)) <
      ((2 ^ i.1 : ℕ) : ℝ) * ((2 ^ i.2.1 : ℕ) : ℝ)

/-- The complementary occupied balanced endpoint boxes in the low-`DE`
alternative. -/
def main3BalancedLowDEBoxIndices (theta : ℝ) (Y R : ℕ) :
    Finset (ℕ × ℕ × ℕ × ℕ) :=
  (main3BalancedOccupiedBoxIndices theta Y R).filter fun i =>
    ((2 ^ i.1 : ℕ) : ℝ) * ((2 ^ i.2.1 : ℕ) : ℝ) ≤
      (Y : ℝ) ^ (1 - 1 / (100 * theta ^ 2))

/-- The finite union of full actual factor cells over the high-`DE`
balanced endpoint boxes.  It may overcount the pointwise balanced family,
which is harmless for upper bounds. -/
def main3BalancedHighDEBoxUnion (theta : ℝ) (Y R : ℕ) :
    Finset (ℕ × ℕ × ℕ × ℕ) :=
  finiteCellUnion (main3BalancedHighDEBoxIndices theta Y R)
    (dyadicFactorBoxCell (theta + 1 / 4) Y)

/-- The analogous finite union over the complementary low-`DE` boxes. -/
def main3BalancedLowDEBoxUnion (theta : ℝ) (Y R : ℕ) :
    Finset (ℕ × ℕ × ℕ × ℕ) :=
  finiteCellUnion (main3BalancedLowDEBoxIndices theta Y R)
    (dyadicFactorBoxCell (theta + 1 / 4) Y)

@[simp] theorem mem_main3BalancedOccupiedBoxIndices
    {theta : ℝ} {Y R : ℕ} {i : ℕ × ℕ × ℕ × ℕ} :
    i ∈ main3BalancedOccupiedBoxIndices theta Y R ↔
      i ∈ dyadicFactorBoxIndices (theta + 1 / 4) Y ∧
        (dyadicFactorBoxCell (theta + 1 / 4) Y i).Nonempty ∧
          R < 2 * 2 ^ i.2.2.1 ∧ R < 2 * 2 ^ i.2.2.2 := by
  simp [main3BalancedOccupiedBoxIndices]

@[simp] theorem mem_main3BalancedHighDEBoxIndices
    {theta : ℝ} {Y R : ℕ} {i : ℕ × ℕ × ℕ × ℕ} :
    i ∈ main3BalancedHighDEBoxIndices theta Y R ↔
      i ∈ main3BalancedOccupiedBoxIndices theta Y R ∧
        (Y : ℝ) ^ (1 - 1 / (100 * theta ^ 2)) <
          ((2 ^ i.1 : ℕ) : ℝ) * ((2 ^ i.2.1 : ℕ) : ℝ) := by
  simp [main3BalancedHighDEBoxIndices]

@[simp] theorem mem_main3BalancedLowDEBoxIndices
    {theta : ℝ} {Y R : ℕ} {i : ℕ × ℕ × ℕ × ℕ} :
    i ∈ main3BalancedLowDEBoxIndices theta Y R ↔
      i ∈ main3BalancedOccupiedBoxIndices theta Y R ∧
        ((2 ^ i.1 : ℕ) : ℝ) * ((2 ^ i.2.1 : ℕ) : ℝ) ≤
          (Y : ℝ) ^ (1 - 1 / (100 * theta ^ 2)) := by
  simp [main3BalancedLowDEBoxIndices]

/-- Pointwise balance transfers to both target endpoint inequalities with
the unavoidable factor two. -/
theorem balancedDyadicFactorTuple_mem_main3BalancedOccupiedBoxUnion
    {theta : ℝ} {Y R : ℕ} {p : ℕ × ℕ × ℕ × ℕ}
    (hp : p ∈ balancedDyadicFactorTuples (theta + 1 / 4) Y R) :
    p ∈ finiteCellUnion (main3BalancedOccupiedBoxIndices theta Y R)
      (dyadicFactorBoxCell (theta + 1 / 4) Y) := by
  have hfactor : p ∈ dyadicFactorTuples (theta + 1 / 4) Y :=
    (mem_balancedDyadicFactorTuples.mp hp).1
  have hR : R ≤ p.2.2.2 := (mem_balancedDyadicFactorTuples.mp hp).2
  rcases mem_finiteCellUnion_iff.mp
      (dyadicFactorTuples_subset_finiteCellUnion_dyadicFactorBoxCell
        (theta + 1 / 4) Y hfactor) with ⟨i, hi, hpi⟩
  have hbox : p ∈ dyadicBox i := (Finset.mem_inter.mp hpi).2
  have hupper := dyadicBox_coordinate_strict_upper_bounds hbox
  obtain ⟨_hd, _he, _hu, _hv, _hdH, _heH, _huH, _hvH,
      _hsu, _hsv, _hcop, _hYuv, _huvY, hvu, _hvSq, _hdiff, _hheight⟩ :=
    mem_dyadicFactorTuples.mp hfactor
  have hRU : R < 2 * 2 ^ i.2.2.1 :=
    (hR.trans hvu).trans_lt hupper.2.2.1
  have hRV : R < 2 * 2 ^ i.2.2.2 := hR.trans_lt hupper.2.2.2
  apply mem_finiteCellUnion_iff.mpr
  exact ⟨i, mem_main3BalancedOccupiedBoxIndices.mpr
    ⟨hi, ⟨p, hpi⟩, hRU, hRV⟩, hpi⟩

/-- The high- and low-`DE` endpoint alternatives cover every pointwise
balanced tuple. -/
theorem balancedDyadicFactorTuples_subset_main3BalancedHighDE_union_lowDE
    (theta : ℝ) (Y R : ℕ) :
    balancedDyadicFactorTuples (theta + 1 / 4) Y R ⊆
      main3BalancedHighDEBoxUnion theta Y R ∪
        main3BalancedLowDEBoxUnion theta Y R := by
  intro p hp
  rcases mem_finiteCellUnion_iff.mp
      (balancedDyadicFactorTuple_mem_main3BalancedOccupiedBoxUnion hp) with
    ⟨i, hi, hpi⟩
  by_cases hhigh :
      (Y : ℝ) ^ (1 - 1 / (100 * theta ^ 2)) <
        ((2 ^ i.1 : ℕ) : ℝ) * ((2 ^ i.2.1 : ℕ) : ℝ)
  · apply Finset.mem_union_left
    apply mem_finiteCellUnion_iff.mpr
    exact ⟨i, mem_main3BalancedHighDEBoxIndices.mpr ⟨hi, hhigh⟩, hpi⟩
  · apply Finset.mem_union_right
    apply mem_finiteCellUnion_iff.mpr
    exact ⟨i, mem_main3BalancedLowDEBoxIndices.mpr
      ⟨hi, le_of_not_gt hhigh⟩, hpi⟩

/-- Exact finite bookkeeping before the two analytic box estimates are
inserted. -/
theorem card_balancedDyadicFactorTuples_le_main3BalancedHighDE_add_lowDE
    (theta : ℝ) (Y R : ℕ) :
    (balancedDyadicFactorTuples (theta + 1 / 4) Y R).card ≤
      (main3BalancedHighDEBoxUnion theta Y R).card +
        (main3BalancedLowDEBoxUnion theta Y R).card := by
  exact (Finset.card_le_card
    (balancedDyadicFactorTuples_subset_main3BalancedHighDE_union_lowDE
      theta Y R)).trans (Finset.card_union_le _ _)

/-- Sum arbitrary real pointwise estimates over all occupied high-`DE`
balanced boxes.  Membership in the index family exposes both actual-cell
nonemptiness and the strict high-`DE` premise needed by the concrete local
theorem. -/
theorem main3BalancedHighDEBoxUnion_card_cast_le_sum
    (theta : ℝ) (Y R : ℕ)
    (F : (ℕ × ℕ × ℕ × ℕ) → ℝ)
    (hF : ∀ i ∈ main3BalancedHighDEBoxIndices theta Y R,
      ((dyadicFactorBoxCell (theta + 1 / 4) Y i).card : ℝ) ≤ F i) :
    ((main3BalancedHighDEBoxUnion theta Y R).card : ℝ) ≤
      ∑ i ∈ main3BalancedHighDEBoxIndices theta Y R, F i := by
  have hcard :
      (main3BalancedHighDEBoxUnion theta Y R).card ≤
        ∑ i ∈ main3BalancedHighDEBoxIndices theta Y R,
          (dyadicFactorBoxCell (theta + 1 / 4) Y i).card := by
    exact Finset.card_biUnion_le
  have hcast :
      ((main3BalancedHighDEBoxUnion theta Y R).card : ℝ) ≤
        ∑ i ∈ main3BalancedHighDEBoxIndices theta Y R,
          ((dyadicFactorBoxCell (theta + 1 / 4) Y i).card : ℝ) := by
    exact_mod_cast hcard
  exact hcast.trans (Finset.sum_le_sum fun i hi => hF i hi)

/-- The matching summation interface for a future low-`DE` estimate. -/
theorem main3BalancedLowDEBoxUnion_card_cast_le_sum
    (theta : ℝ) (Y R : ℕ)
    (F : (ℕ × ℕ × ℕ × ℕ) → ℝ)
    (hF : ∀ i ∈ main3BalancedLowDEBoxIndices theta Y R,
      ((dyadicFactorBoxCell (theta + 1 / 4) Y i).card : ℝ) ≤ F i) :
    ((main3BalancedLowDEBoxUnion theta Y R).card : ℝ) ≤
      ∑ i ∈ main3BalancedLowDEBoxIndices theta Y R, F i := by
  have hcard :
      (main3BalancedLowDEBoxUnion theta Y R).card ≤
        ∑ i ∈ main3BalancedLowDEBoxIndices theta Y R,
          (dyadicFactorBoxCell (theta + 1 / 4) Y i).card := by
    exact Finset.card_biUnion_le
  have hcast :
      ((main3BalancedLowDEBoxUnion theta Y R).card : ℝ) ≤
        ∑ i ∈ main3BalancedLowDEBoxIndices theta Y R,
          ((dyadicFactorBoxCell (theta + 1 / 4) Y i).card : ℝ) := by
    exact_mod_cast hcard
  exact hcast.trans (Finset.sum_le_sum fun i hi => hF i hi)

/-- A common pointwise envelope costs at most the number of occupied
high-`DE` boxes times that envelope. -/
theorem main3BalancedHighDEBoxUnion_card_cast_le_card_mul
    (theta : ℝ) (Y R : ℕ) (A : ℝ)
    (hA : ∀ i ∈ main3BalancedHighDEBoxIndices theta Y R,
      ((dyadicFactorBoxCell (theta + 1 / 4) Y i).card : ℝ) ≤ A) :
    ((main3BalancedHighDEBoxUnion theta Y R).card : ℝ) ≤
      ((main3BalancedHighDEBoxIndices theta Y R).card : ℝ) * A := by
  calc
    ((main3BalancedHighDEBoxUnion theta Y R).card : ℝ) ≤
        ∑ _i ∈ main3BalancedHighDEBoxIndices theta Y R, A :=
      main3BalancedHighDEBoxUnion_card_cast_le_sum theta Y R (fun _ => A) hA
    _ = ((main3BalancedHighDEBoxIndices theta Y R).card : ℝ) * A := by
      simp

/-- The number of active high boxes is bounded by the exact four-coordinate
dyadic scale product already present in the global reduction. -/
theorem card_main3BalancedHighDEBoxIndices_le_scale_product
    (theta : ℝ) (Y R : ℕ) :
    (main3BalancedHighDEBoxIndices theta Y R).card ≤
      dyadicScaleCount (dyadicFactorHeight (theta + 1 / 4) Y) *
        (dyadicScaleCount (dyadicFactorHeight (theta + 1 / 4) Y) *
          (dyadicScaleCount (2 * Y) * dyadicScaleCount (2 * Y))) := by
  calc
    (main3BalancedHighDEBoxIndices theta Y R).card ≤
        (dyadicFactorBoxIndices (theta + 1 / 4) Y).card := by
      apply Finset.card_le_card
      intro i hi
      exact (mem_main3BalancedOccupiedBoxIndices.mp
        (mem_main3BalancedHighDEBoxIndices.mp hi).1).1
    _ = _ := by
      simp [dyadicFactorBoxIndices, card_dyadicBoxIndices]

end

end PellPaper
