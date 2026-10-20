import Pell.ClassAverage
import Pell.ClassRegulatorReparam

/-!
# Fundamental-discriminant cutoff bookkeeping

The class-average family uses the strict real cutoff `D < X`, whereas the
Pell regulator-exception API uses the natural cutoff `D ≤ floor X`.  This file
checks the elementary compatibility of those two conventions.  It makes no
claim about fields, units, or class numbers.
-/

namespace PellPaper

noncomputable section

/-- A positive fundamental discriminant in the strict class-average cutoff is
already below the natural cutoff used by the Pell exceptional-set API. -/
theorem fundamentalDiscriminant_le_floor_of_mem {D : ℕ} {X : ℝ}
    (hX : 0 ≤ X) (hD : D ∈ fundamentalDiscriminantsBelow X) :
    D ≤ ⌊X⌋₊ := by
  obtain ⟨_, hDX⟩ := mem_fundamentalDiscriminantsBelow.mp hD
  exact (Nat.le_floor_iff hX).mpr hDX.le

/-- On the actual fundamental-discriminant family, the Pell-side discriminant
cutoff is automatic.  Thus the regulator-exception set is exactly the
regulator-small filter. -/
theorem classRegulatorExceptionalSet_fundamentalDiscriminantsBelow_eq_regulatorFilter
    (X t : ℝ) (r : ℕ → ℝ) (hX : 0 ≤ X) :
    classRegulatorExceptionalSet (fundamentalDiscriminantsBelow X) id r ⌊X⌋₊ t =
      (fundamentalDiscriminantsBelow X).filter (fun D ↦ r D < t) := by
  apply classRegulatorExceptionalSet_eq_regulatorFilter_of_cutoff
  intro D hD
  simpa using fundamentalDiscriminant_le_floor_of_mem hX hD

end

end PellPaper
