import Pell.BudgetedSmallSquarePartReduction

/-!
# Reconciliation of ordinary and budgeted small-square-part families

If every root in the exact half-open interval `1 ≤ s < S` satisfies the
scale budget, the budgeted family is the entire small-square-part family.
The comparison retains the original dyadic interval and the same canonical
decomposition `m = s ^ 2 * w`; only its already valid budget is supplied.

The resulting cover and cardinality bounds still sum the budgeted
transferred fibers.  No estimate for those fibers or power saving is claimed.
-/

open scoped BigOperators

namespace PellPaper

/-- On a root range covered by the scale budget, adding the budget preserves
exactly the same canonical square-part decomposition and strict root cutoff. -/
theorem budgetedSmallSquarePartDecomposition_iff_of_root_budgets
    {theta : ℝ} {Y S m s w : ℕ}
    (hbudget : ∀ r : ℕ, 1 ≤ r → r < S → squarePartScaleBudget theta Y r) :
    BudgetedSmallSquarePartDecomposition theta Y S m s w ↔
      CanonicalSquarePartDecomposition m s w ∧ s < S := by
  constructor
  · rintro ⟨hcanonical, hsS, _⟩
    exact ⟨hcanonical, hsS⟩
  · rintro ⟨hcanonical, hsS⟩
    exact ⟨hcanonical, hsS, hbudget s hcanonical.1 hsS⟩

/-- Every ordinary small-square-part exception is budgeted when all
admissible roots satisfy the scale budget.  Its witnesses are unchanged. -/
theorem dyadicSmallSquarePartExceptionalSet_subset_budgeted_of_root_budgets
    {theta : ℝ} {Y S : ℕ}
    (hbudget : ∀ s : ℕ, 1 ≤ s → s < S → squarePartScaleBudget theta Y s) :
    dyadicSmallSquarePartExceptionalSet theta Y S ⊆
      budgetedDyadicSmallSquarePartExceptionalSet theta Y S := by
  intro m hm
  rcases mem_dyadicSmallSquarePartExceptionalSet.mp hm with
    ⟨hdyadic, s, w, hs, hsS, hw, hdecomp, hsf⟩
  apply mem_budgetedDyadicSmallSquarePartExceptionalSet.mpr
  refine ⟨hdyadic, s, w, ?_⟩
  exact (budgetedSmallSquarePartDecomposition_iff_of_root_budgets hbudget).mpr
    ⟨⟨hs, hw, hdecomp, hsf⟩, hsS⟩

/-- Exact reconciliation of the two exceptional families under the explicit
budget for every root in `Finset.Ico 1 S`.  No positivity assumption on the
dyadic scale or nonemptiness assumption on the root range is needed. -/
theorem dyadicSmallSquarePartExceptionalSet_eq_budgeted_of_root_budgets
    {theta : ℝ} {Y S : ℕ}
    (hbudget : ∀ s : ℕ, 1 ≤ s → s < S → squarePartScaleBudget theta Y s) :
    dyadicSmallSquarePartExceptionalSet theta Y S =
      budgetedDyadicSmallSquarePartExceptionalSet theta Y S := by
  exact Finset.Subset.antisymm
    (dyadicSmallSquarePartExceptionalSet_subset_budgeted_of_root_budgets hbudget)
    (budgetedDyadicSmallSquarePartExceptionalSet_subset_small theta Y S)

/-- The budgeted count is exactly the ordinary family's cardinality on a
root range where every scale budget holds. -/
theorem dyadicSmallSquarePartExceptional_card_eq_budgetedCount_of_root_budgets
    {theta : ℝ} {Y S : ℕ}
    (hbudget : ∀ s : ℕ, 1 ≤ s → s < S → squarePartScaleBudget theta Y s) :
    (dyadicSmallSquarePartExceptionalSet theta Y S).card =
      budgetedDyadicSmallSquarePartExceptionalCount theta Y S := by
  rw [dyadicSmallSquarePartExceptionalSet_eq_budgeted_of_root_budgets hbudget]
  rfl

/-- The ordinary small-square-part family is covered by budgeted transferred
fibers, with the same root indices and reconstruction map `w ↦ s ^ 2 * w`. -/
theorem dyadicSmallSquarePartExceptionalSet_subset_budgetedTransferred_union_of_root_budgets
    {theta : ℝ} {Y S : ℕ}
    (hbudget : ∀ s : ℕ, 1 ≤ s → s < S → squarePartScaleBudget theta Y s) :
    dyadicSmallSquarePartExceptionalSet theta Y S ⊆
      (Finset.Ico 1 S).biUnion fun s ↦
        (budgetedDyadicTransferredSquarefreeSet theta Y s).image
          fun w ↦ s ^ 2 * w := by
  rw [dyadicSmallSquarePartExceptionalSet_eq_budgeted_of_root_budgets hbudget]
  exact budgetedDyadicSmallSquarePartExceptionalSet_subset_budgetedTransferred_union
    theta Y S

/-- Finite counting reduction for the entire ordinary small-square-part
family under the root budgets.  The right side retains each budgeted fiber. -/
theorem dyadicSmallSquarePartExceptional_card_le_sum_budgetedTransferred_of_root_budgets
    {theta : ℝ} {Y S : ℕ}
    (hbudget : ∀ s : ℕ, 1 ≤ s → s < S → squarePartScaleBudget theta Y s) :
    (dyadicSmallSquarePartExceptionalSet theta Y S).card ≤
      ∑ s ∈ Finset.Ico 1 S,
        (budgetedDyadicTransferredSquarefreeSet theta Y s).card := by
  rw [dyadicSmallSquarePartExceptionalSet_eq_budgeted_of_root_budgets hbudget]
  exact budgetedDyadicSmallSquarePartExceptional_card_le_sum_budgetedTransferred
    theta Y S

/-- Composing with the existing finite dyadic cover gives the corresponding
double sum of fixed-height blocks.  Neither sum has been estimated. -/
theorem dyadicSmallSquarePartExceptional_card_le_sum_dyadicBlocks_of_root_budgets
    {theta : ℝ} {Y S : ℕ}
    (hbudget : ∀ s : ℕ, 1 ≤ s → s < S → squarePartScaleBudget theta Y s) :
    (dyadicSmallSquarePartExceptionalSet theta Y S).card ≤
      ∑ _s ∈ Finset.Ico 1 S,
        ∑ k ∈ Finset.range (Nat.log 2 (2 * Y) + 1),
          squarefreeDyadicExceptionalCount (theta + (1 : ℝ) / 4) (2 ^ k) := by
  apply (dyadicSmallSquarePartExceptional_card_le_sum_budgetedTransferred_of_root_budgets
    hbudget).trans
  apply Finset.sum_le_sum
  intro s hs
  exact budgetedDyadicTransferredSquarefreeSet_card_le_sum_dyadicBlocks
    (Finset.mem_Ico.mp hs).1

end PellPaper
