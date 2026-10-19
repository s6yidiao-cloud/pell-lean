import Pell.GeneralSquarePartHeightTransfer
import Pell.BudgetedTransferredScaledCutoff
import Pell.SquarefreeGlobalPowerBound

/-!
# General fixed-height bounds at the scaled one-fiber cutoff

A positive square-part root retains the exact closed cutoff
`(2 * Y - 1) / s ^ 2` coming from the strict dyadic endpoint.  The scale
budget upgrades every member of the ordinary transferred fiber to height
`phi`, so a global squarefree bound applies at this smaller cutoff.

The conditional power-bound constant depends only on the target height and
the saving exponent.  It is uniform in the original height, the dyadic scale,
and the square-part root whenever the stated height budget holds.  The scale
may be zero; cutoffs below two give empty fibers.
-/

namespace PellPaper

/-- Under the general height budget, an ordinary transferred fiber lies in
the squarefree exceptional set at the exact square-part-scaled cutoff. -/
theorem dyadicTransferredSquarefreeSet_subset_squarefreeExceptionalSet_scaledCutoff_of_height_budget
    {theta phi : ℝ} {Y s : ℕ} (hs : 0 < s) (htheta_phi : theta ≤ phi)
    (hbudget : (s : ℝ) ^ (2 * phi) ≤ (Y : ℝ) ^ (phi - theta)) :
    dyadicTransferredSquarefreeSet theta Y s ⊆
      squarefreeExceptionalSet phi ((2 * Y - 1) / s ^ 2) := by
  intro w hw
  obtain ⟨hwlo, _, _, _, hsf, _, _, _⟩ :=
    mem_dyadicTransferredSquarefreeSet.mp hw
  refine mem_squarefreeExceptionalSet.mpr ⟨by omega, ?_, hsf, ?_⟩
  · exact le_scaledCutoff_of_mem_dyadicTransferredSquarefreeSet hs hw
  · exact smallFundamentalSolution_of_mem_dyadicTransferredSquarefreeSet_of_height_budget
      hs htheta_phi hw hbudget

/-- Cardinality form of the exact general-height scaled-cutoff containment. -/
theorem dyadicTransferredSquarefreeSet_card_le_squarefreeExceptionalCount_scaledCutoff_of_height_budget
    {theta phi : ℝ} {Y s : ℕ} (hs : 0 < s) (htheta_phi : theta ≤ phi)
    (hbudget : (s : ℝ) ^ (2 * phi) ≤ (Y : ℝ) ^ (phi - theta)) :
    (dyadicTransferredSquarefreeSet theta Y s).card ≤
      squarefreeExceptionalCount phi ((2 * Y - 1) / s ^ 2) := by
  exact Finset.card_le_card
    (dyadicTransferredSquarefreeSet_subset_squarefreeExceptionalSet_scaledCutoff_of_height_budget
      hs htheta_phi hbudget)

/-- A cutoff smaller than the least possible radicand forces the ordinary
transferred fiber to be empty, independently of a height budget. -/
theorem dyadicTransferredSquarefreeSet_eq_empty_of_scaledCutoff_lt_two
    {theta : ℝ} {Y s : ℕ} (hs : 0 < s)
    (hcutoff : (2 * Y - 1) / s ^ 2 < 2) :
    dyadicTransferredSquarefreeSet theta Y s = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  have hwlo := (mem_dyadicTransferredSquarefreeSet.mp hw).1
  have hwupper := le_scaledCutoff_of_mem_dyadicTransferredSquarefreeSet hs hw
  omega

/-- Conditional scale-sensitive power bound for an ordinary transferred
fiber.  One constant works for all original heights `theta ≤ phi`, scales
`Y`, and positive roots `s` satisfying the scale budget.  Natural division
and the strict dyadic endpoint are retained exactly, including cutoff zero. -/
theorem exists_dyadicTransferredSquarefreeSet_scaled_power_bound_of_FixedHeightSquarefree
    (hfixed : FixedHeightSquarefree) {phi d : ℝ}
    (hphi : 3 ≤ phi) (hdpos : 0 < d) (hd : d < Delta phi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ theta : ℝ, theta ≤ phi → ∀ Y s : ℕ, 0 < s →
      (s : ℝ) ^ (2 * phi) ≤ (Y : ℝ) ^ (phi - theta) →
      ((dyadicTransferredSquarefreeSet theta Y s).card : ℝ) ≤
        C * (((2 * Y - 1) / s ^ 2 : ℕ) : ℝ) ^ (1 - d) := by
  obtain ⟨C, hC, hglobal⟩ :=
    exists_squarefree_global_power_bound_of_fixedHeightSquarefree hfixed hphi hdpos hd
  refine ⟨C, hC, ?_⟩
  intro theta htheta_phi Y s hs hbudget
  calc
    ((dyadicTransferredSquarefreeSet theta Y s).card : ℝ) ≤
        (squarefreeExceptionalCount phi ((2 * Y - 1) / s ^ 2) : ℝ) := by
      exact_mod_cast
        dyadicTransferredSquarefreeSet_card_le_squarefreeExceptionalCount_scaledCutoff_of_height_budget
          hs htheta_phi hbudget
    _ ≤ C * (((2 * Y - 1) / s ^ 2 : ℕ) : ℝ) ^ (1 - d) := hglobal _

end PellPaper
