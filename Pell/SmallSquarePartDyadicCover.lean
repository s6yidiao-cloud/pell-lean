import Pell.SquarePartExponentSlack
import Pell.SquarefreeDyadicCover

/-!
# Budgeted small-square-part transfer to squarefree dyadic blocks

For a fixed square-part root `s`, the transferred dyadic squarefree family
retains the original unit cutoff.  If the manuscript's explicit scale budget
holds, `SquarePartExponentSlack` improves that cutoff to a genuine
fixed-height bound at the squarefree radicand, with the deliberate exponent
loss `1 / 4`.

This file makes the resulting finite dyadic cover exact.  It contains no
estimate for the cardinalities of its blocks: it only records the pointwise
transfer, the finite union, and cardinality subadditivity.
-/

open scoped BigOperators

namespace PellPaper

/-- The small-square-part scale condition used to obtain the exponent slack.
It is intentionally a separate predicate so subsequent counting arguments
must retain the manuscript's budget rather than silently applying the
fixed-height transfer to every square-part root. -/
def squarePartScaleBudget (θ : ℝ) (Y s : ℕ) : Prop :=
  (s : ℝ) ^ (2 * θ + (1 : ℝ) / 2) ≤ (Y : ℝ) ^ ((1 : ℝ) / 4)

/-- The fixed-root transferred squarefree family after imposing the explicit
scale budget.  The filter is constant in `w`, but writing it as a filter keeps
the budget visibly attached to this particular family. -/
noncomputable def budgetedDyadicTransferredSquarefreeSet
    (θ : ℝ) (Y s : ℕ) : Finset ℕ := by
  classical
  exact (dyadicTransferredSquarefreeSet θ Y s).filter
    (fun _ ↦ squarePartScaleBudget θ Y s)

/-- Literal membership description of the budgeted transferred family. -/
@[simp] theorem mem_budgetedDyadicTransferredSquarefreeSet
    {θ : ℝ} {Y s w : ℕ} :
    w ∈ budgetedDyadicTransferredSquarefreeSet θ Y s ↔
      w ∈ dyadicTransferredSquarefreeSet θ Y s ∧
        squarePartScaleBudget θ Y s := by
  classical
  change w ∈ (dyadicTransferredSquarefreeSet θ Y s).filter
    (fun _ ↦ squarePartScaleBudget θ Y s) ↔ _
  constructor
  · intro hw
    exact Finset.mem_filter.mp hw
  · rintro ⟨hw, hbudget⟩
    exact Finset.mem_filter.mpr ⟨hw, hbudget⟩

/-- The finite union of squarefree fixed-height dyadic blocks which can
contain the budgeted transferred family.  The upper index is chosen from the
ambient bound `w < 2Y`; it is not a quantitative assertion. -/
noncomputable def budgetedTransferredDyadicCover
    (θ : ℝ) (Y _s : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (Nat.log 2 (2 * Y) + 1)).biUnion
    (fun k ↦ squarefreeDyadicExceptionalSet (θ + (1 : ℝ) / 4) (2 ^ k))

/-- A budgeted transferred squarefree radicand lies in its canonical dyadic
fixed-height block, indexed by `⌊log₂ w⌋`. -/
theorem mem_squarefreeDyadicExceptionalSet_at_log_of_mem_budgetedTransferred
    {θ : ℝ} {Y s w : ℕ} (hs : 0 < s)
    (hw : w ∈ budgetedDyadicTransferredSquarefreeSet θ Y s) :
    w ∈ squarefreeDyadicExceptionalSet (θ + (1 : ℝ) / 4)
      (2 ^ Nat.log 2 w) := by
  obtain ⟨htransferred, hbudget⟩ :=
    mem_budgetedDyadicTransferredSquarefreeSet.mp hw
  obtain ⟨hwlo, _, _, _, hsf, _, _, _⟩ :=
    mem_dyadicTransferredSquarefreeSet.mp htransferred
  have hwpos : 0 < w := lt_of_lt_of_le Nat.zero_lt_two hwlo
  refine mem_squarefreeDyadicExceptionalSet.mpr ⟨?_, ?_, hsf, ?_⟩
  · exact Nat.pow_log_le_self 2 (Nat.ne_of_gt hwpos)
  · simpa [pow_succ, Nat.mul_comm] using
      (Nat.lt_pow_succ_log_self Nat.one_lt_two w)
  · exact smallFundamentalSolution_add_quarter_of_mem_dyadicTransferredSquarefreeSet_of_budget
      hs htransferred hbudget

/-- Pointwise membership in the finite cover of budgeted transferred
squarefree radicands. -/
theorem mem_budgetedTransferredDyadicCover_of_mem_budgetedTransferred
    {θ : ℝ} {Y s w : ℕ} (hs : 0 < s)
    (hw : w ∈ budgetedDyadicTransferredSquarefreeSet θ Y s) :
    w ∈ budgetedTransferredDyadicCover θ Y s := by
  obtain ⟨htransferred, _⟩ :=
    mem_budgetedDyadicTransferredSquarefreeSet.mp hw
  obtain ⟨_, hwupper, _, _, _, _, _, _⟩ :=
    mem_dyadicTransferredSquarefreeSet.mp htransferred
  apply Finset.mem_biUnion.mpr
  refine ⟨Nat.log 2 w, Finset.mem_range.mpr ?_,
    mem_squarefreeDyadicExceptionalSet_at_log_of_mem_budgetedTransferred hs hw⟩
  have hlog : Nat.log 2 w ≤ Nat.log 2 (2 * Y) :=
    Nat.log_mono_right (Nat.le_of_lt hwupper)
  omega

/-- Set-theoretic finite reduction from the budgeted transferred family to
squarefree fixed-height dyadic blocks. -/
theorem budgetedDyadicTransferredSquarefreeSet_subset_dyadicCover
    {θ : ℝ} {Y s : ℕ} (hs : 0 < s) :
    budgetedDyadicTransferredSquarefreeSet θ Y s ⊆
      budgetedTransferredDyadicCover θ Y s := by
  intro w hw
  exact mem_budgetedTransferredDyadicCover_of_mem_budgetedTransferred hs hw

/-- Cardinality subadditivity for the finite fixed-height cover.  This is a
pure reduction; in particular, it does not bound any summand on the right. -/
theorem budgetedDyadicTransferredSquarefreeSet_card_le_sum_dyadicBlocks
    {θ : ℝ} {Y s : ℕ} (hs : 0 < s) :
    (budgetedDyadicTransferredSquarefreeSet θ Y s).card ≤
      ∑ k ∈ Finset.range (Nat.log 2 (2 * Y) + 1),
        squarefreeDyadicExceptionalCount (θ + (1 : ℝ) / 4) (2 ^ k) := by
  calc
    (budgetedDyadicTransferredSquarefreeSet θ Y s).card ≤
        (budgetedTransferredDyadicCover θ Y s).card :=
      Finset.card_le_card
        (budgetedDyadicTransferredSquarefreeSet_subset_dyadicCover hs)
    _ ≤ ∑ k ∈ Finset.range (Nat.log 2 (2 * Y) + 1),
        squarefreeDyadicExceptionalCount (θ + (1 : ℝ) / 4) (2 ^ k) := by
      change ((Finset.range (Nat.log 2 (2 * Y) + 1)).biUnion
        (fun k ↦ squarefreeDyadicExceptionalSet
          (θ + (1 : ℝ) / 4) (2 ^ k))).card ≤ _
      simpa [squarefreeDyadicExceptionalCount] using
        (Finset.card_biUnion_le :
          ((Finset.range (Nat.log 2 (2 * Y) + 1)).biUnion
            (fun k ↦ squarefreeDyadicExceptionalSet
              (θ + (1 : ℝ) / 4) (2 ^ k))).card ≤
            ∑ k ∈ Finset.range (Nat.log 2 (2 * Y) + 1),
              (squarefreeDyadicExceptionalSet
                (θ + (1 : ℝ) / 4) (2 ^ k)).card)

end PellPaper
