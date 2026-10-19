import Pell.SmallSquarePartDyadicCover

/-!
# The square-part-scaled cutoff for one transferred fiber

The fixed-root transferred family retains the strict bound `s ^ 2 * w < 2 * Y`.
For a positive root, its squarefree radicands therefore lie below the closed
natural cutoff `(2 * Y - 1) / s ^ 2`.  The scale budget supplies the fixed-height
condition at exponent `theta + 1/4` independently of this sharper cutoff.

The power-of-two rounding below is the least power strictly above that closed
cutoff, including when the cutoff is zero.  All statements concern one fiber;
no summation over square-part roots or power-saving estimate is asserted.
-/

namespace PellPaper

/-- The original strict dyadic endpoint gives the exact closed integer cutoff
after dividing by the square of a positive square-part root. -/
theorem le_scaledCutoff_of_mem_dyadicTransferredSquarefreeSet
    {theta : ℝ} {Y s w : ℕ} (hs : 0 < s)
    (hw : w ∈ dyadicTransferredSquarefreeSet theta Y s) :
    w ≤ (2 * Y - 1) / s ^ 2 := by
  obtain ⟨_, _, _, hwupper, _, _, _, _⟩ :=
    mem_dyadicTransferredSquarefreeSet.mp hw
  apply (Nat.le_div_iff_mul_le (pow_pos hs 2)).mpr
  have hclosed : s ^ 2 * w ≤ 2 * Y - 1 := by omega
  simpa only [Nat.mul_comm] using hclosed

/-- A budgeted transferred fiber is contained in the squarefree fixed-height
exceptional set at its square-part-scaled cutoff.  This includes `Y = 0` and
cutoffs smaller than two, when the fiber is empty. -/
theorem budgetedDyadicTransferredSquarefreeSet_subset_squarefreeExceptionalSet_scaledCutoff
    {theta : ℝ} {Y s : ℕ} (hs : 0 < s) :
    budgetedDyadicTransferredSquarefreeSet theta Y s ⊆
      squarefreeExceptionalSet (theta + (1 : ℝ) / 4) ((2 * Y - 1) / s ^ 2) := by
  intro w hw
  obtain ⟨htransferred, hbudget⟩ :=
    mem_budgetedDyadicTransferredSquarefreeSet.mp hw
  obtain ⟨hwlo, _, _, _, hsf, _, _, _⟩ :=
    mem_dyadicTransferredSquarefreeSet.mp htransferred
  refine mem_squarefreeExceptionalSet.mpr ⟨by omega, ?_, hsf, ?_⟩
  · exact le_scaledCutoff_of_mem_dyadicTransferredSquarefreeSet hs htransferred
  · exact smallFundamentalSolution_add_quarter_of_mem_dyadicTransferredSquarefreeSet_of_budget
      hs htransferred hbudget

/-- The cardinality bound retains the square-part divisor in the cutoff. -/
theorem budgetedDyadicTransferredSquarefreeSet_card_le_squarefreeExceptionalCount_scaledCutoff
    {theta : ℝ} {Y s : ℕ} (hs : 0 < s) :
    (budgetedDyadicTransferredSquarefreeSet theta Y s).card ≤
      squarefreeExceptionalCount (theta + (1 : ℝ) / 4) ((2 * Y - 1) / s ^ 2) := by
  exact Finset.card_le_card
    (budgetedDyadicTransferredSquarefreeSet_subset_squarefreeExceptionalSet_scaledCutoff hs)

/-- A scaled cutoff below the least possible squarefree radicand leaves no
members in the transferred fiber. -/
theorem budgetedDyadicTransferredSquarefreeSet_eq_empty_of_scaledCutoff_lt_two
    {theta : ℝ} {Y s : ℕ} (hs : 0 < s)
    (hcutoff : (2 * Y - 1) / s ^ 2 < 2) :
    budgetedDyadicTransferredSquarefreeSet theta Y s = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  have htransferred := (mem_budgetedDyadicTransferredSquarefreeSet.mp hw).1
  have hwlo := (mem_dyadicTransferredSquarefreeSet.mp htransferred).1
  have hwupper := le_scaledCutoff_of_mem_dyadicTransferredSquarefreeSet hs htransferred
  omega

/-- The least power of two strictly above the closed scaled cutoff. -/
def budgetedTransferredScaledRoundingScale (Y s : ℕ) : ℕ :=
  2 ^ Nat.clog 2 ((2 * Y - 1) / s ^ 2 + 1)

/-- Strict containment of the scaled closed cutoff in its rounded scale,
without any positivity assumption on the cutoff. -/
theorem budgetedTransferred_scaledCutoff_lt_roundingScale (Y s : ℕ) :
    (2 * Y - 1) / s ^ 2 < budgetedTransferredScaledRoundingScale Y s := by
  exact Nat.lt_of_succ_le (Nat.le_pow_clog Nat.one_lt_two _)

/-- The rounding is exact: a power of two bounds the rounded scale if and
only if it lies strictly above the original closed cutoff. -/
theorem budgetedTransferredScaledRoundingScale_le_pow_iff (Y s K : ℕ) :
    budgetedTransferredScaledRoundingScale Y s ≤ 2 ^ K ↔
      (2 * Y - 1) / s ^ 2 < 2 ^ K := by
  unfold budgetedTransferredScaledRoundingScale
  rw [Nat.pow_le_pow_iff_right Nat.one_lt_two,
    Nat.clog_le_iff_le_pow Nat.one_lt_two]
  omega

/-- At a zero cutoff the exact strict rounding scale is one. -/
theorem budgetedTransferredScaledRoundingScale_eq_one_of_scaledCutoff_eq_zero
    {Y s : ℕ} (hcutoff : (2 * Y - 1) / s ^ 2 = 0) :
    budgetedTransferredScaledRoundingScale Y s = 1 := by
  simp [budgetedTransferredScaledRoundingScale, hcutoff]

/-- At a positive cutoff, exact dyadic rounding costs at most a factor of two. -/
theorem budgetedTransferredScaledRoundingScale_le_two_mul_scaledCutoff
    {Y s : ℕ} (hcutoff : 0 < (2 * Y - 1) / s ^ 2) :
    budgetedTransferredScaledRoundingScale Y s ≤ 2 * ((2 * Y - 1) / s ^ 2) := by
  let X := (2 * Y - 1) / s ^ 2
  have hX : 1 < X + 1 := by dsimp [X]; omega
  have hprev : 2 ^ (Nat.clog 2 (X + 1) - 1) ≤ X := by
    simpa only [Nat.pred_eq_sub_one] using
      (Nat.le_of_lt_succ (Nat.pow_pred_clog_lt_self Nat.one_lt_two hX))
  have hlogpos : 0 < Nat.clog 2 (X + 1) := by
    apply (Nat.lt_clog_iff_pow_lt Nat.one_lt_two).mpr
    simpa using hX
  change 2 ^ Nat.clog 2 (X + 1) ≤ 2 * X
  calc
    2 ^ Nat.clog 2 (X + 1) = 2 ^ (Nat.clog 2 (X + 1) - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      omega
    _ ≤ X * 2 := Nat.mul_le_mul_right 2 hprev
    _ = 2 * X := Nat.mul_comm _ _

end PellPaper
