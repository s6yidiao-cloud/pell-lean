import Pell.SourceNormalizedDeterminantStrictness
import Pell.ShearedLocalCoordinateRateAbsorption

/-!
# Scalar rate absorption for the source-normalized determinant endpoint

The source-normalized determinant endpoint asks for a strict comparison
between the logarithmic clearing cost and its finite mesh cubic gain.  In the
paper this comparison is made after separating a common leading cost: the
leading `B^3 L` centre/denominator term occurs on both sides, a positive
cubic surplus remains on the gain side, and all residual terms have a
quadratic budget.

This module formalizes just that scalar cancellation and domination step.
It does not establish the leading-cost bound, the finite-mesh surplus, or
the geometric local-coordinate hypotheses from `main.tex`; those are the
remaining non-scalar interfaces.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- The leading centre-and-denominator cost coefficient displayed in the
source-normalized proof of `L:sheared`, before its lower-order residual terms
are charged. -/
noncomputable def sourceNormalizedLeadingCost
    (B : ℕ) (rho alphaDE alphaUV L : ℝ) : ℝ :=
  (alphaDE * rho ^ 2 + alphaUV * rho) / 2 * (B : ℝ) ^ 3 * L

/-- The logarithmic comparison loss in the local-coordinate cost is at most
a chosen positive slack times `log Y` under its explicit exponential
threshold.  This isolates the scalar fact used implicitly inside the older
strict-rate convenience lemma. -/
theorem shearedComparableCoordinateLogLoss_le_slack_mul_log_of_threshold
    (A B : ℕ) (c k slack Y : ℝ)
    (hslack : 0 < slack)
    (hthreshold :
      Real.exp (shearedComparableCoordinateLogLoss A B c k / slack) ≤ Y) :
    shearedComparableCoordinateLogLoss A B c k ≤ slack * Real.log Y := by
  have hYpos : 0 < Y := lt_of_lt_of_le (Real.exp_pos _) hthreshold
  have hratio : shearedComparableCoordinateLogLoss A B c k / slack ≤
      Real.log Y := by
    apply (Real.exp_le_exp).mp
    rw [Real.exp_log hYpos]
    exact hthreshold
  calc
    shearedComparableCoordinateLogLoss A B c k ≤ Real.log Y * slack :=
      (div_le_iff₀ hslack).mp hratio
    _ = slack * Real.log Y := by ring

/-- A common leading cost cancels between a logarithmic budget and a cubic
gain.  Once a positive cubic surplus dominates a quadratic residual term,
the resulting determinant rate is strict. -/
theorem strict_logarithmic_rate_lt_of_absorbedLoss_leadingCubicSurplus
    {n : Type*} [Fintype n]
    (baseCost loss slack tail leadingCost gainCoeff quadCoeff degree L W : ℝ)
    (hgain : 0 < gainCoeff) (_hquad : 0 ≤ quadCoeff)
    (hdegree : 0 < degree) (hL : 0 < L) (_hslack : 0 < slack)
    (hloss : loss ≤ slack * L)
    (hbudget : baseCost + slack * L +
      Real.log (Nat.factorial (Fintype.card n) : ℝ) +
        tail * (Fintype.card n : ℝ) ≤
      leadingCost + quadCoeff * degree ^ 2 * L)
    (hdominates : quadCoeff * degree ^ 2 ≤
      (gainCoeff / 2) * degree ^ 3)
    (hsurplus : leadingCost + gainCoeff * degree ^ 3 * L ≤ W) :
    (baseCost + loss) + Real.log (Nat.factorial (Fintype.card n) : ℝ) +
        tail * (Fintype.card n : ℝ) < W := by
  have hquadratic : quadCoeff * degree ^ 2 * L ≤
      (gainCoeff / 2) * degree ^ 3 * L :=
    mul_le_mul_of_nonneg_right hdominates hL.le
  have hhalf_pos : 0 < (gainCoeff / 2) * degree ^ 3 * L := by
    positivity
  have hbudget' : (baseCost + loss) +
      Real.log (Nat.factorial (Fintype.card n) : ℝ) +
        tail * (Fintype.card n : ℝ) ≤
      leadingCost + (gainCoeff / 2) * degree ^ 3 * L := by
    calc
      (baseCost + loss) + Real.log (Nat.factorial (Fintype.card n) : ℝ) +
          tail * (Fintype.card n : ℝ) ≤
        baseCost + slack * L + Real.log
          (Nat.factorial (Fintype.card n) : ℝ) +
            tail * (Fintype.card n : ℝ) := by linarith
      _ ≤ leadingCost + quadCoeff * degree ^ 2 * L := hbudget
      _ ≤ leadingCost + (gainCoeff / 2) * degree ^ 3 * L := by
        linarith
  have hstrict : leadingCost + (gainCoeff / 2) * degree ^ 3 * L <
      leadingCost + gainCoeff * degree ^ 3 * L := by
    nlinarith
  exact hbudget'.trans_lt (hstrict.trans_le hsurplus)

/-- Source-normalized specialization of the common-leading-cost rate
calculation.  Its conclusion is exactly the `hrate` premise consumed by
`standardSelectedIntegralMinor_det_eq_zero_of_sourceNormalizedFloorCubic_rate`.
The finite floor mesh gain remains explicit on the right. -/
theorem sourceNormalizedFloor_strictRate_of_absorbedLoss_leadingCubicSurplus
    (A B : ℕ) (m x L baseCost loss slack leadingCost gainCoeff quadCoeff : ℝ)
    (hB : 0 < B) (hL : 0 < L) (hgain : 0 < gainCoeff)
    (hquad : 0 ≤ quadCoeff) (hslack : 0 < slack)
    (hloss : loss ≤ slack * L)
    (hbudget : baseCost + slack * L +
      Real.log (Nat.factorial (Fintype.card (generalBidegreeGrid A B)) : ℝ) +
        shearedActualRankTaylorTail A B *
          (Fintype.card (generalBidegreeGrid A B) : ℝ) ≤
      leadingCost + quadCoeff * (B : ℝ) ^ 2 * L)
    (hdominates : quadCoeff * (B : ℝ) ^ 2 ≤
      (gainCoeff / 2) * (B : ℝ) ^ 3)
    (hsurplus : leadingCost + gainCoeff * (B : ℝ) ^ 3 * L ≤
      sourceNormalizedFloorCubicGain A B m x L) :
    (baseCost + loss) +
        Real.log (Nat.factorial (Fintype.card (generalBidegreeGrid A B)) : ℝ) +
      shearedActualRankTaylorTail A B *
        (Fintype.card (generalBidegreeGrid A B) : ℝ) <
      sourceNormalizedFloorCubicGain A B m x L := by
  have hBreal : 0 < (B : ℝ) := by exact_mod_cast hB
  exact strict_logarithmic_rate_lt_of_absorbedLoss_leadingCubicSurplus
    baseCost loss slack (shearedActualRankTaylorTail A B) leadingCost
      gainCoeff quadCoeff (B : ℝ) L
      (sourceNormalizedFloorCubicGain A B m x L)
      hgain hquad hBreal hL hslack hloss hbudget hdominates hsurplus

/-- The preceding source-normalized scalar bridge with the leading cost in
the exact notation of the paper.  This does not derive the displayed budget
or finite-mesh surplus from dyadic geometry; it only cancels their common
leading term. -/
theorem sourceNormalizedFloor_strictRate_of_sourceLeadingCost
    (A B : ℕ) (m x L baseCost loss slack rho alphaDE alphaUV gainCoeff quadCoeff : ℝ)
    (hB : 0 < B) (hL : 0 < L) (hgain : 0 < gainCoeff)
    (hquad : 0 ≤ quadCoeff) (hslack : 0 < slack)
    (hloss : loss ≤ slack * L)
    (hbudget : baseCost + slack * L +
      Real.log (Nat.factorial (Fintype.card (generalBidegreeGrid A B)) : ℝ) +
        shearedActualRankTaylorTail A B *
          (Fintype.card (generalBidegreeGrid A B) : ℝ) ≤
      sourceNormalizedLeadingCost B rho alphaDE alphaUV L +
        quadCoeff * (B : ℝ) ^ 2 * L)
    (hdominates : quadCoeff * (B : ℝ) ^ 2 ≤
      (gainCoeff / 2) * (B : ℝ) ^ 3)
    (hsurplus : sourceNormalizedLeadingCost B rho alphaDE alphaUV L +
      gainCoeff * (B : ℝ) ^ 3 * L ≤
      sourceNormalizedFloorCubicGain A B m x L) :
    (baseCost + loss) +
        Real.log (Nat.factorial (Fintype.card (generalBidegreeGrid A B)) : ℝ) +
      shearedActualRankTaylorTail A B *
        (Fintype.card (generalBidegreeGrid A B) : ℝ) <
      sourceNormalizedFloorCubicGain A B m x L := by
  exact sourceNormalizedFloor_strictRate_of_absorbedLoss_leadingCubicSurplus
    A B m x L baseCost loss slack
      (sourceNormalizedLeadingCost B rho alphaDE alphaUV L)
      gainCoeff quadCoeff hB hL hgain hquad hslack hloss hbudget hdominates hsurplus

/-- The previous source-normalized rate bridge with the comparable local
coordinate loss discharged by its explicit logarithmic threshold.  The
identity `L = log Y` is stated rather than inferred, keeping the source
normalization visible. -/
theorem sourceNormalizedFloor_strictRate_of_comparableCoordinateLoss
    (A B : ℕ) (m x L baseCost c k slack leadingCost gainCoeff quadCoeff Y : ℝ)
    (hB : 0 < B) (hL : L = Real.log Y) (hY : 1 < Y)
    (hgain : 0 < gainCoeff) (hquad : 0 ≤ quadCoeff) (hslack : 0 < slack)
    (hthreshold :
      Real.exp (shearedComparableCoordinateLogLoss A B c k / slack) ≤ Y)
    (hbudget : baseCost + slack * L +
      Real.log (Nat.factorial (Fintype.card (generalBidegreeGrid A B)) : ℝ) +
        shearedActualRankTaylorTail A B *
          (Fintype.card (generalBidegreeGrid A B) : ℝ) ≤
      leadingCost + quadCoeff * (B : ℝ) ^ 2 * L)
    (hdominates : quadCoeff * (B : ℝ) ^ 2 ≤
      (gainCoeff / 2) * (B : ℝ) ^ 3)
    (hsurplus : leadingCost + gainCoeff * (B : ℝ) ^ 3 * L ≤
      sourceNormalizedFloorCubicGain A B m x L) :
    (baseCost + shearedComparableCoordinateLogLoss A B c k) +
        Real.log (Nat.factorial (Fintype.card (generalBidegreeGrid A B)) : ℝ) +
      shearedActualRankTaylorTail A B *
        (Fintype.card (generalBidegreeGrid A B) : ℝ) <
      sourceNormalizedFloorCubicGain A B m x L := by
  have hLpos : 0 < L := by
    rw [hL]
    exact Real.log_pos hY
  have hlossLog : shearedComparableCoordinateLogLoss A B c k ≤
      slack * Real.log Y :=
    shearedComparableCoordinateLogLoss_le_slack_mul_log_of_threshold
      A B c k slack Y hslack hthreshold
  have hloss : shearedComparableCoordinateLogLoss A B c k ≤ slack * L := by
    simpa [hL] using hlossLog
  exact sourceNormalizedFloor_strictRate_of_absorbedLoss_leadingCubicSurplus
    A B m x L baseCost (shearedComparableCoordinateLogLoss A B c k) slack
      leadingCost gainCoeff quadCoeff hB hLpos hgain hquad hslack hloss
      hbudget hdominates hsurplus

end

end PellPaper
