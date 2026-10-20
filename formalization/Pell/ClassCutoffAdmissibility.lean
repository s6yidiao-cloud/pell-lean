import Pell.RegulatorAdmissibility
import Pell.ClassAverageCutoff

/-!
# Admissibility on the class-average cutoff interval

The reparameterized class-side argument only needs the uniform Pell estimate
for regulator parameters in the interval from a nonnegative lower endpoint to
the class-average cutoff.  This file packages the elementary monotonicity
step: a sufficient admissibility inequality at the upper endpoint implies the
same condition throughout that interval.  The numerical upper-endpoint
inequality itself remains an explicit hypothesis.
-/

namespace PellPaper

open Set

noncomputable section

/-- A cutoff condition at the upper endpoint implies uniform Pell
admissibility for one regulator parameter in the class-average interval. -/
theorem uniformAdmissible_regulatorPellExponent_of_mem_Icc_classAverageCutoff
    {cExc r₀ c X t : ℝ} (hr₀ : 0 ≤ r₀)
    (ht : t ∈ Icc r₀ (classAverageCutoff c X))
    (hcutoff : 4 * (classAverageCutoff c X + 1) ≤
      cExc * Real.sqrt (Real.log X / Real.log (Real.log X))) :
    UniformAdmissible cExc (regulatorPellExponent t) X := by
  apply uniformAdmissible_regulatorPellExponent_of_four_mul_add_one_le
    (hr₀.trans ht.1)
  calc
    4 * (t + 1) ≤ 4 * (classAverageCutoff c X + 1) := by
      nlinarith [ht.2]
    _ ≤ cExc * Real.sqrt (Real.log X / Real.log (Real.log X)) := hcutoff

/-- The preceding endpoint condition supplies admissibility uniformly on the
entire class-average cutoff interval. -/
theorem uniformAdmissible_regulatorPellExponent_on_Icc_classAverageCutoff
    {cExc r₀ c X : ℝ} (hr₀ : 0 ≤ r₀)
    (hcutoff : 4 * (classAverageCutoff c X + 1) ≤
      cExc * Real.sqrt (Real.log X / Real.log (Real.log X))) :
    ∀ t ∈ Icc r₀ (classAverageCutoff c X),
      UniformAdmissible cExc (regulatorPellExponent t) X := by
  intro t ht
  exact uniformAdmissible_regulatorPellExponent_of_mem_Icc_classAverageCutoff
    hr₀ ht hcutoff

end

end PellPaper
