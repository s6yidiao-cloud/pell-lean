import Pell.SmallSquarePartDyadicCover

/-!
# Budgeted small-square-part counting reduction

This module keeps the square-part root visibly canonical while restricting a
dyadic exceptional family to the explicit scale budget used by the
small-square-part argument.  It proves only a finite-set reduction: the
budgeted subfamily is covered by the images of the correspondingly budgeted
transferred squarefree fibers.  In particular, it assumes no fixed-height,
determinant, or square-sieve estimate.
-/

open scoped BigOperators

namespace PellPaper

/-- A positive square/squarefree decomposition in the nonsquare Pell range.
The positivity and squarefreeness make both factors canonical, by the unique
square-part decomposition theorem. -/
def CanonicalSquarePartDecomposition (m s w : ℕ) : Prop :=
  0 < s ∧ 1 < w ∧ m = s ^ 2 * w ∧ Squarefree w

/-- The canonical decomposition has a unique square-part root and squarefree
part.  This makes the scale-budget condition below a condition on `m`, rather
than on an arbitrary factorization of `m`. -/
theorem CanonicalSquarePartDecomposition.unique
    {m s w s' w' : ℕ}
    (h : CanonicalSquarePartDecomposition m s w)
    (h' : CanonicalSquarePartDecomposition m s' w') :
    s = s' ∧ w = w' := by
  rcases h with ⟨hs, hw, hm, hsf⟩
  rcases h' with ⟨hs', hw', hm', hsf'⟩
  exact square_part_decomposition_unique hs (by omega) hs' (by omega)
    hm hm' hsf hsf'

/-- A canonical small square-part decomposition satisfying the manuscript's
explicit dyadic scale budget. -/
def BudgetedSmallSquarePartDecomposition
    (θ : ℝ) (Y S m s w : ℕ) : Prop :=
  CanonicalSquarePartDecomposition m s w ∧ s < S ∧
    squarePartScaleBudget θ Y s

/-- The scale budget is invariant under replacing a canonical decomposition
by another presentation of the same radicand. -/
theorem BudgetedSmallSquarePartDecomposition.budget_of_canonical
    {θ : ℝ} {Y S m s w s' w' : ℕ}
    (h : BudgetedSmallSquarePartDecomposition θ Y S m s w)
    (h' : CanonicalSquarePartDecomposition m s' w') :
    squarePartScaleBudget θ Y s' := by
  rcases h with ⟨hcanonical, _, hbudget⟩
  obtain ⟨hss', _⟩ := hcanonical.unique h'
  subst s'
  exact hbudget

/-- The dyadic exceptional subfamily whose *canonical* square-part root is
below `S` and satisfies the explicit scale budget. -/
noncomputable def budgetedDyadicSmallSquarePartExceptionalSet
    (θ : ℝ) (Y S : ℕ) : Finset ℕ := by
  classical
  exact (dyadicSquarePartExceptionalSet θ Y).filter fun m ↦
    ∃ s w : ℕ, BudgetedSmallSquarePartDecomposition θ Y S m s w

/-- Its finite cardinality. -/
noncomputable def budgetedDyadicSmallSquarePartExceptionalCount
    (θ : ℝ) (Y S : ℕ) : ℕ :=
  (budgetedDyadicSmallSquarePartExceptionalSet θ Y S).card

/-- Literal membership in the budgeted small-square-part subfamily. -/
@[simp] theorem mem_budgetedDyadicSmallSquarePartExceptionalSet
    {θ : ℝ} {Y S m : ℕ} :
    m ∈ budgetedDyadicSmallSquarePartExceptionalSet θ Y S ↔
      m ∈ dyadicSquarePartExceptionalSet θ Y ∧
        ∃ s w : ℕ, BudgetedSmallSquarePartDecomposition θ Y S m s w := by
  classical
  change m ∈ (dyadicSquarePartExceptionalSet θ Y).filter
    (fun m ↦ ∃ s w : ℕ, BudgetedSmallSquarePartDecomposition θ Y S m s w) ↔ _
  constructor
  · intro hm
    exact Finset.mem_filter.mp hm
  · rintro ⟨hm, hdecomp⟩
    exact Finset.mem_filter.mpr ⟨hm, hdecomp⟩

/-- Forgetting the scale budget recovers the ordinary small-square-part
dyadic subfamily. -/
theorem budgetedDyadicSmallSquarePartExceptionalSet_subset_small
    (θ : ℝ) (Y S : ℕ) :
    budgetedDyadicSmallSquarePartExceptionalSet θ Y S ⊆
      dyadicSmallSquarePartExceptionalSet θ Y S := by
  intro m hm
  rcases mem_budgetedDyadicSmallSquarePartExceptionalSet.mp hm with
    ⟨hdyadic, s, w, hcanonical, hsS, _⟩
  rcases hcanonical with ⟨hs, hw, hdecomp, hsf⟩
  exact mem_dyadicSmallSquarePartExceptionalSet.mpr
    ⟨hdyadic, s, w, hs, hsS, hw, hdecomp, hsf⟩

/-- Every budgeted small-square-part dyadic exception is the image of the
budgeted transferred fiber at its canonical square-part root. -/
theorem budgetedDyadicSmallSquarePartExceptionalSet_subset_budgetedTransferred_union
    (θ : ℝ) (Y S : ℕ) :
    budgetedDyadicSmallSquarePartExceptionalSet θ Y S ⊆
      (Finset.Ico 1 S).biUnion fun s ↦
        (budgetedDyadicTransferredSquarefreeSet θ Y s).image
          fun w ↦ s ^ 2 * w := by
  classical
  intro m hm
  rcases mem_budgetedDyadicSmallSquarePartExceptionalSet.mp hm with
    ⟨hdyadic, s, w, hcanonical, hsS, hbudget⟩
  rcases hcanonical with ⟨hs, hw, hdecomp, hsf⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨s, Finset.mem_Ico.mpr ⟨by omega, hsS⟩, ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨w, ?_, hdecomp.symm⟩
  exact mem_budgetedDyadicTransferredSquarefreeSet.mpr
    ⟨mem_dyadicTransferredSquarefreeSet_of_mem_dyadicSquarePartExceptionalSet
      hdyadic hs hdecomp hsf, hbudget⟩

/-- The finite counting reduction for the budgeted small-square-part family.
Each summand is exactly the transferred fiber with the same root-scale budget;
no numerical estimate for those fibers is claimed here. -/
theorem budgetedDyadicSmallSquarePartExceptionalCount_le_sum_budgetedTransferred
    (θ : ℝ) (Y S : ℕ) :
    budgetedDyadicSmallSquarePartExceptionalCount θ Y S ≤
      ∑ s ∈ Finset.Ico 1 S,
        (budgetedDyadicTransferredSquarefreeSet θ Y s).card := by
  classical
  calc
    budgetedDyadicSmallSquarePartExceptionalCount θ Y S ≤
        ((Finset.Ico 1 S).biUnion fun s ↦
          (budgetedDyadicTransferredSquarefreeSet θ Y s).image
            fun w ↦ s ^ 2 * w).card :=
      Finset.card_le_card
        (budgetedDyadicSmallSquarePartExceptionalSet_subset_budgetedTransferred_union
          θ Y S)
    _ ≤ ∑ s ∈ Finset.Ico 1 S,
        ((budgetedDyadicTransferredSquarefreeSet θ Y s).image
          fun w ↦ s ^ 2 * w).card :=
      Finset.card_biUnion_le
    _ ≤ _ := Finset.sum_le_sum fun _ _ ↦ Finset.card_image_le

/-- The same reduction stated directly for the subfamily's cardinality. -/
theorem budgetedDyadicSmallSquarePartExceptional_card_le_sum_budgetedTransferred
    (θ : ℝ) (Y S : ℕ) :
    (budgetedDyadicSmallSquarePartExceptionalSet θ Y S).card ≤
      ∑ s ∈ Finset.Ico 1 S,
        (budgetedDyadicTransferredSquarefreeSet θ Y s).card := by
  exact budgetedDyadicSmallSquarePartExceptionalCount_le_sum_budgetedTransferred
    θ Y S

end PellPaper
