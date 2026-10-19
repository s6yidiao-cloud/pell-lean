import Pell.DyadicLocalCenterScale
import Pell.DyadicFactorScaleComparability
import Pell.GeneralBidegreeDyadicFactorCoordinates
import Pell.ShearedLocalCoordinateLogInput
import Pell.SourceNormalizedDeterminantStrictness

/-!
# Concrete dyadic local data at the source-normalized determinant endpoint

This module removes the local-coordinate interface hypotheses from the
source-normalized determinant endpoint for a family of actual dyadic factor
tuples.  A pointwise dyadic box, localized source interval, factor condition,
and the explicit lower-endpoint comparison `32 X ≤ D² U` supply the two
reindexed logarithmic inputs.  The integral points, their nonzero
denominators, and their normalized coordinates are constructed from the
tuples themselves.

The determinant cost, mesh, rank, and strict-rate hypotheses remain explicit:
this is a local-coordinate transport, not the determinant-method counting
argument or a proof of the required source scale comparison.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- The homogeneous point of a positive dyadic factor tuple has nonzero
source and target denominators. -/
theorem dyadicFactorTupleToGeneralBidegreeFormPoint_denominators_ne_zero_of_condition
    {theta : ℝ} {Y d e u v : ℕ}
    (hcond : DyadicFactorCondition theta Y d e u v) :
    (dyadicFactorTupleToGeneralBidegreeFormPoint (d, e, u, v)).1.2 ≠ 0 ∧
      (dyadicFactorTupleToGeneralBidegreeFormPoint (d, e, u, v)).2.2 ≠ 0 := by
  rcases hcond with ⟨_hd, he, hu, _hv, _hrest⟩
  constructor
  · simp only [dyadicFactorTupleToGeneralBidegreeFormPoint]
    exact_mod_cast Nat.ne_of_gt he
  · simp only [dyadicFactorTupleToGeneralBidegreeFormPoint]
    exact_mod_cast Nat.ne_of_gt hu

/-- The normalized local ratios give the exact real affine coordinates of
the integral point attached to a dyadic factor tuple. -/
theorem dyadicFactorTupleToGeneralBidegreeFormPoint_local_coordinates
    {d e u v : ℕ} {s0 : ℝ}
    (hs0 : 0 < s0) (_he : 0 < e) (hu : 0 < u) :
    ((dyadicFactorTupleToGeneralBidegreeFormPoint (d, e, u, v)).1.1 : ℝ) /
        ((dyadicFactorTupleToGeneralBidegreeFormPoint (d, e, u, v)).1.2 : ℝ) =
          s0 * localSourceRatio s0 d e ∧
      ((dyadicFactorTupleToGeneralBidegreeFormPoint (d, e, u, v)).2.1 : ℝ) /
        ((dyadicFactorTupleToGeneralBidegreeFormPoint (d, e, u, v)).2.2 : ℝ) =
          s0 ^ 2 * localTargetRatio s0 u v := by
  constructor
  · unfold dyadicFactorTupleToGeneralBidegreeFormPoint localSourceRatio
    field_simp [hs0.ne']
    push_cast
    ring
  · unfold dyadicFactorTupleToGeneralBidegreeFormPoint localTargetRatio
    field_simp [hs0.ne', (by exact_mod_cast (Nat.ne_of_gt hu) : (u : ℝ) ≠ 0)]
    push_cast
    ring

/-- The integral homogeneous point family associated to four coordinate
families.  Naming this family keeps the determinant endpoint visibly tied to
the actual dyadic tuples. -/
def dyadicFactorTupleFamilyPoints {ι : Type*}
    (d e u v : ι → ℕ) : ι → GeneralBidegreeFormPoint :=
  fun row => dyadicFactorTupleToGeneralBidegreeFormPoint
    (d row, e row, u row, v row)

/-- A family satisfying the dyadic factor condition has nonzero homogeneous
denominators at every associated integral point. -/
theorem dyadicFactorTupleFamilyPoints_denominators_ne_zero_of_condition
    {ι : Type*} {theta : ℝ} {Y : ℕ} (d e u v : ι → ℕ)
    (hcond : ∀ row, DyadicFactorCondition theta Y
      (d row) (e row) (u row) (v row)) :
    ∀ row, (dyadicFactorTupleFamilyPoints d e u v row).1.2 ≠ 0 ∧
      (dyadicFactorTupleFamilyPoints d e u v row).2.2 ≠ 0 := by
  intro row
  simpa [dyadicFactorTupleFamilyPoints] using
    dyadicFactorTupleToGeneralBidegreeFormPoint_denominators_ne_zero_of_condition
      (hcond row)

/-- The point family built from tuples has precisely the normalized local
coordinates used by the sheared determinant matrix. -/
theorem dyadicFactorTupleFamilyPoints_local_coordinates
    {ι : Type*} (d e u v : ι → ℕ) {s0 : ℝ}
    (hs0 : 0 < s0) (he : ∀ row, 0 < e row) (hu : ∀ row, 0 < u row) :
    ∀ row,
      ((dyadicFactorTupleFamilyPoints d e u v row).1.1 : ℝ) /
          ((dyadicFactorTupleFamilyPoints d e u v row).1.2 : ℝ) =
            s0 * localSourceRatio s0 (d row) (e row) ∧
        ((dyadicFactorTupleFamilyPoints d e u v row).2.1 : ℝ) /
          ((dyadicFactorTupleFamilyPoints d e u v row).2.2 : ℝ) =
            s0 ^ 2 * localTargetRatio s0 (u row) (v row) := by
  intro row
  simpa [dyadicFactorTupleFamilyPoints] using
    dyadicFactorTupleToGeneralBidegreeFormPoint_local_coordinates
      hs0 (he row) (hu row)

/-- **Concrete local input for the source-normalized determinant endpoint.**
For actual factor tuples, local dyadic boxes and source intervals eliminate
the endpoint's abstract denominator, coordinate, and logarithmic-input
hypotheses.  The explicit premise `32 X ≤ D² U` is the only local scale
comparison used here; the determinant cost, mesh, cubic/rank conditions, and
strict rate budget are retained exactly as source-side inputs. -/
theorem standardSelectedIntegralMinor_det_eq_zero_of_dyadicLocalizedSourceData
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : ℕ) (eRows : ι ≃ generalBidegreeGrid A B)
    (r : generalBidegreeFormIndex A B ≃ ι)
    (hr : r = (generalBidegreeGridPointEquiv A B).trans eRows.symm)
    {theta : ℝ} {Y : ℕ} (i : ι → ℕ × ℕ × ℕ × ℕ)
    (d e u v : ι → ℕ) (s0 M X sigma m x L : ℝ)
    (hbox : ∀ row, (d row, e row, u row, v row) ∈ dyadicBox (i row))
    (hcond : ∀ row, DyadicFactorCondition theta Y
      (d row) (e row) (u row) (v row))
    (hs0 : 0 < s0) (hM : 1 ≤ M)
    (hlower : ∀ row, s0 ≤ (d row : ℝ) / (e row : ℝ))
    (hupper : ∀ row,
      (d row : ℝ) / (e row : ℝ) ≤ s0 * (1 + 1 / M))
    (hsource_scale : ∀ row, 32 * X ≤
      ((2 ^ (i row).1 : ℕ) : ℝ) ^ 2 *
        ((2 ^ (i row).2.2.1 : ℕ) : ℝ))
    (hX : 2 ≤ X) (hsigma : 0 < sigma)
    (hlarge : Real.exp (Real.log 2 / sigma) ≤ X)
    (hsource_decay : m * L ≤ Real.log M)
    (hxL : x * L = (1 - sigma) * Real.log X)
    (hB : 0 < B) (hm : 0 < m) (hmx : m ≤ x) (hL : 0 < L)
    (hshear : x * ((A : ℝ) / (B : ℝ)) ≤ 2 * m)
    (cost : ℝ)
    (hcost :
      |(∏ j : generalBidegreeFormIndex A B,
          ((dyadicFactorTupleFamilyPoints d e u v (r j)).1.2 : ℝ) ^ A *
            ((dyadicFactorTupleFamilyPoints d e u v (r j)).2.2 : ℝ) ^ B) *
          s0 ^ (((A + 1) * (B + 1) * (A + 2 * B)) / 2)| ≤ Real.exp cost)
    (hrate : cost + Real.log (Nat.factorial (Fintype.card
      (generalBidegreeGrid A B)) : ℝ) +
      shearedActualRankTaylorTail A B *
        (Fintype.card (generalBidegreeGrid A B) : ℝ) <
      sourceNormalizedFloorCubicGain A B m x L) :
    ((generalBidegreeFormEvaluationMatrix A B
      (dyadicFactorTupleFamilyPoints d e u v)).submatrix r id).det = 0 := by
  have hS_one : ∀ row, 1 ≤ localSourceRatio s0 (d row) (e row) := by
    intro row
    unfold localSourceRatio
    apply (le_div_iff₀ hs0).mpr
    simpa using hlower row
  have hS : ∀ row, 0 < localSourceRatio s0 (d row) (e row) := by
    intro row
    exact lt_of_lt_of_le zero_lt_one (hS_one row)
  have hT : ∀ row, 0 < localTargetRatio s0 (u row) (v row) := by
    intro row
    unfold localTargetRatio
    have hu : 0 < (u row : ℝ) := by
      exact_mod_cast (hcond row).2.2.1
    have hv : 0 < (v row : ℝ) := by
      exact_mod_cast (hcond row).2.2.2.1
    exact div_pos (div_pos hv hu) (sq_pos_of_pos hs0)
  have hscale : ∀ row,
      2 * X ≤ s0 ^ 2 * (e row : ℝ) ^ 2 * (u row : ℝ) := by
    intro row
    exact two_mul_le_local_displacement_denominator_of_dyadicBox_localized_source
      (hbox row) hM (hupper row) (hsource_scale row)
  have halpha : ∀ row,
      |generalBidegreeReindexedLogS A B eRows
        (fun row => localSourceRatio s0 (d row) (e row)) row| ≤
          Real.exp (-(m * L)) :=
    generalBidegreeReindexedLogS_bound_of_localizedIntervals
      A B eRows s0 M m L d e hs0 hM hlower hupper hsource_decay
  have hbeta_raw : ∀ row,
      |generalBidegreeReindexedShearedLogT A B eRows
        (fun row => localSourceRatio s0 (d row) (e row))
        (fun row => localTargetRatio s0 (u row) (v row)) row| ≤
          Real.exp (-(1 - sigma) * Real.log X) :=
    generalBidegreeReindexedShearedLogT_bound_of_dyadicLocalScale
      A B eRows s0 X sigma d e u v hcond hs0 hX hS_one hscale hsigma hlarge
  have hbeta : ∀ row,
      |generalBidegreeReindexedShearedLogT A B eRows
        (fun row => localSourceRatio s0 (d row) (e row))
        (fun row => localTargetRatio s0 (u row) (v row)) row| ≤
          Real.exp (-(x * L)) := by
    intro row
    calc
      |generalBidegreeReindexedShearedLogT A B eRows
          (fun row => localSourceRatio s0 (d row) (e row))
          (fun row => localTargetRatio s0 (u row) (v row)) row| ≤
        Real.exp (-(1 - sigma) * Real.log X) := hbeta_raw row
      _ = Real.exp (-(x * L)) := by
        congr 1
        rw [hxL]
        ring
  apply standardSelectedIntegralMinor_det_eq_zero_of_sourceNormalizedFloorCubic_rate
    A B (dyadicFactorTupleFamilyPoints d e u v) eRows r hr s0
      (fun row => localSourceRatio s0 (d row) (e row))
      (fun row => localTargetRatio s0 (u row) (v row))
      (dyadicFactorTupleFamilyPoints_denominators_ne_zero_of_condition d e u v hcond)
      (dyadicFactorTupleFamilyPoints_local_coordinates d e u v hs0
        (fun row => (hcond row).2.1) (fun row => (hcond row).2.2.1))
      hS hT m x L hB hm hmx hL hshear halpha hbeta cost hcost hrate

/-- A target-endpoint version of the concrete local determinant transport.
The nontrivial factor-and-box comparison changes the explicit source lower
endpoint scale `32 X ≤ D²U` into the target-endpoint condition
`768 X ≤ E²V`; no unrescaled manuscript-scale assertion is made. -/
theorem standardSelectedIntegralMinor_det_eq_zero_of_dyadicLocalizedTargetScale
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : ℕ) (eRows : ι ≃ generalBidegreeGrid A B)
    (r : generalBidegreeFormIndex A B ≃ ι)
    (hr : r = (generalBidegreeGridPointEquiv A B).trans eRows.symm)
    {theta : ℝ} {Y : ℕ} (i : ι → ℕ × ℕ × ℕ × ℕ)
    (d e u v : ι → ℕ) (s0 M X sigma m x L : ℝ)
    (hbox : ∀ row, (d row, e row, u row, v row) ∈ dyadicBox (i row))
    (hcond : ∀ row, DyadicFactorCondition theta Y
      (d row) (e row) (u row) (v row))
    (hs0 : 0 < s0) (hM : 1 ≤ M)
    (hlower : ∀ row, s0 ≤ (d row : ℝ) / (e row : ℝ))
    (hupper : ∀ row,
      (d row : ℝ) / (e row : ℝ) ≤ s0 * (1 + 1 / M))
    (htarget_scale : ∀ row, 768 * X ≤
      ((2 ^ (i row).2.1 : ℕ) : ℝ) ^ 2 *
        ((2 ^ (i row).2.2.2 : ℕ) : ℝ))
    (hX : 2 ≤ X) (hsigma : 0 < sigma)
    (hlarge : Real.exp (Real.log 2 / sigma) ≤ X)
    (hsource_decay : m * L ≤ Real.log M)
    (hxL : x * L = (1 - sigma) * Real.log X)
    (hB : 0 < B) (hm : 0 < m) (hmx : m ≤ x) (hL : 0 < L)
    (hshear : x * ((A : ℝ) / (B : ℝ)) ≤ 2 * m)
    (cost : ℝ)
    (hcost :
      |(∏ j : generalBidegreeFormIndex A B,
          ((dyadicFactorTupleFamilyPoints d e u v (r j)).1.2 : ℝ) ^ A *
            ((dyadicFactorTupleFamilyPoints d e u v (r j)).2.2 : ℝ) ^ B) *
          s0 ^ (((A + 1) * (B + 1) * (A + 2 * B)) / 2)| ≤ Real.exp cost)
    (hrate : cost + Real.log (Nat.factorial (Fintype.card
      (generalBidegreeGrid A B)) : ℝ) +
      shearedActualRankTaylorTail A B *
        (Fintype.card (generalBidegreeGrid A B) : ℝ) <
      sourceNormalizedFloorCubicGain A B m x L) :
    ((generalBidegreeFormEvaluationMatrix A B
      (dyadicFactorTupleFamilyPoints d e u v)).submatrix r id).det = 0 := by
  exact standardSelectedIntegralMinor_det_eq_zero_of_dyadicLocalizedSourceData
    A B eRows r hr i d e u v s0 M X sigma m x L hbox hcond hs0 hM
      hlower hupper
      (fun row => dyadicFactorCondition_source_scale_lower_bound_of_dyadicBox
        (hcond row) (hbox row) (htarget_scale row))
      hX hsigma hlarge hsource_decay hxL hB hm hmx hL hshear cost hcost hrate

end

end PellPaper
