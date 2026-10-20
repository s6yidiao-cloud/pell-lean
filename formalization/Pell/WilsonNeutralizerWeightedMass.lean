import Pell.WilsonNeutralizerTotalMassExpansion

/-!
# Bounding Wilson's original weighted mass by a neutralizer mass

The same upper-Moebius neutralizer used for the quadratic second moment also
majorizes the first Cauchy factor.  This short finite bridge lets the final
Selberg application use a single total-mass estimate for both factors.
-/

namespace PellPaper

noncomputable section

/-- Any coefficient sequence bounded by one has reciprocal-divisor mass at
most the total mass of an upper-Moebius neutralizer. -/
theorem wilsonWeightedMass_reciprocalDivisor_le_neutralizerTotalMass
    (b : ℕ → ℝ) (P M : ℕ) (lambdaPlus : ℕ → ℝ)
    (hP : Squarefree P)
    (hUpper : BoundingSieve.IsUpperMoebius lambdaPlus)
    (hb : ∀ m : ℕ, |b m| ≤ 1) :
    wilsonWeightedMass b main4WilsonReciprocalDivisorWeight M ≤
      main4WilsonNeutralizerTotalMass P M lambdaPlus := by
  unfold wilsonWeightedMass main4WilsonNeutralizerTotalMass
  apply Finset.sum_le_sum
  intro m hm
  exact
    abs_mul_main4WilsonReciprocalDivisorWeight_le_neutralizerMajorant
      P m hP (Nat.ne_of_gt (Finset.mem_Icc.mp hm).1)
        lambdaPlus hUpper (hb m)

end

end PellPaper
