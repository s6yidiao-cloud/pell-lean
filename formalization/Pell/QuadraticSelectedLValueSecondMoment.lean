import Pell.QuadraticSelectedLValueFiniteMoment
import Pell.SelectedMomentLogAbsorption
import Pell.SelectedMomentCubicCutoffTransfer

/-!
# An unconditional second moment of the actual selected L-values

The proved finite cubic estimate and explicit logarithmic absorption yield
the natural-cube bound with constant `65`. The proved integer-cube-root
transfer then gives constant `520` for every sufficiently large real cutoff.
The family remains the literal positive fundamental discriminants with
strict cutoff `D < X`. No analytic or arithmetic estimate is a hypothesis.
-/

namespace PellPaper

open Filter
open scoped BigOperators

/-- The actual selected L-values have an eventual linear second moment at
natural-cube cutoffs, with the explicit constant `65`. -/
theorem eventually_sum_selectedKroneckerLValue_sq_le_cubic :
    ∀ᶠ Y : ℕ in atTop,
      (∑ D ∈ fundamentalDiscriminantsBelow ((Y : ℝ) ^ 3),
        (selectedKroneckerLValue D) ^ 2) ≤ 65 * (Y : ℝ) ^ 3 := by
  filter_upwards [eventually_selectedMomentLogError_le_cube,
    eventually_gt_atTop (0 : ℕ)] with Y herror hY
  have hfinite := sum_selectedKroneckerLValue_sq_le_cubic_moment Y hY
  linarith

/-- The actual selected L-values have an eventual linear second moment at
all real cutoffs, with the explicit constant `520`. -/
theorem eventually_sum_selectedKroneckerLValue_sq_le :
    ∀ᶠ X : ℝ in atTop,
      (∑ D ∈ fundamentalDiscriminantsBelow X,
        (selectedKroneckerLValue D) ^ 2) ≤ 520 * X :=
  eventually_sum_selectedKroneckerLValue_sq_le_of_cubic_bound
    eventually_sum_selectedKroneckerLValue_sq_le_cubic

end PellPaper
