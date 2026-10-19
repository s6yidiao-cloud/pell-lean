import Pell.TwoLayerFanDeterminantStrictness
import Pell.DyadicComparableCostAdapter
import Pell.DyadicTargetScaleLogSlack

/-!
# Exact two-layer fan minors for actual dyadic tuples

This module supplies the concrete dyadic coordinate and denominator data to
the exact two-layer fan strictness theorem.  All rows lie in one dyadic box
and one localized source-ratio window.  The target endpoint scale gives the
sheared logarithmic decay, while the existing comparable-cost calculation
gives the denominator-and-centre factor with its literal fixed loss.

The sole remaining analytic obligation is the displayed exact fan rate
inequality.  No rectangular mesh, area envelope, or cubic surrogate occurs.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- **Actual dyadic exact-fan selected-minor endpoint.**  A full family of
actual factor tuples in one localized dyadic box has zero standard integral
evaluation determinant once the exact two-layer weight exceeds the clearing
cost, factorial, and Taylor tail. -/
theorem standardSelectedIntegralMinor_det_eq_zero_of_uniformDyadicTwoLayerFanRate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B k : ℕ) (eRows : ι ≃ generalBidegreeGrid 1 B)
    (r : generalBidegreeFormIndex 1 B ≃ ι)
    (hr : r = (generalBidegreeGridPointEquiv 1 B).trans eRows.symm)
    {theta : ℝ} {Y : ℕ} {i : ℕ × ℕ × ℕ × ℕ}
    (d e u v : ι → ℕ)
    (s0 M xScale sigma m xDet L baseCost : ℝ)
    (hcond : ∀ row, DyadicFactorCondition theta Y
      (d row) (e row) (u row) (v row))
    (hbox : ∀ row, (d row, e row, u row, v row) ∈ dyadicBox i)
    (hs0 : 0 < s0) (hM : 1 ≤ M)
    (hlower : ∀ row, s0 ≤ (d row : ℝ) / (e row : ℝ))
    (hupper : ∀ row,
      (d row : ℝ) / (e row : ℝ) ≤ s0 * (1 + 1 / M))
    (htargetScale : xScale ≤ ((2 ^ i.2.1 : ℕ) : ℝ) ^ 2 *
      ((2 ^ i.2.2.2 : ℕ) : ℝ))
    (hxScale : 1536 ≤ xScale) (hsigma : 0 < sigma)
    (hlocalThreshold :
      Real.exp (Real.log (1536 : ℝ) / sigma) ≤ xScale)
    (hsourceDecay : m * L ≤ Real.log M)
    (hxDetL : xDet * L = (1 - sigma) * Real.log xScale)
    (hellM : 0 < m * L)
    (hkpos : 1 ≤ k) (hkB : k ≤ B)
    (hfanLower : (2 * (k : ℝ) - 1) * (m * L) ≤ xDet * L)
    (hfanUpper : xDet * L ≤ (2 * (k : ℝ) + 1) * (m * L))
    (hbaseCost :
      ((2 * ((2 ^ i.1 : ℕ) : ℝ)) *
        (2 * ((2 ^ i.2.1 : ℕ) : ℝ))) ^
          (1 * ((1 + 1) * (B + 1)) / 2) *
        ((2 * ((2 ^ i.2.2.1 : ℕ) : ℝ)) *
          (2 * ((2 ^ i.2.2.2 : ℕ) : ℝ))) ^
            (B * ((1 + 1) * (B + 1)) / 2) ≤ Real.exp baseCost)
    (hrate :
      (baseCost + shearedComparableCoordinateLogLoss 1 B 2 24) +
          Real.log (Nat.factorial
            (Fintype.card (generalBidegreeGrid 1 B)) : ℝ) +
        twoLayerFanTaylorTail B *
          (Fintype.card (generalBidegreeGrid 1 B) : ℝ) <
      twoLayerWeight B k (m * L) (xDet * L)) :
    ((generalBidegreeFormEvaluationMatrix 1 B
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
  have hα : ∀ row,
      |generalBidegreeReindexedLogS 1 B eRows
        (fun row => localSourceRatio s0 (d row) (e row)) row| ≤
          Real.exp (-(m * L)) :=
    generalBidegreeReindexedLogS_bound_of_localizedIntervals
      1 B eRows s0 M m L d e hs0 hM hlower hupper hsourceDecay
  have hβraw : ∀ row,
      |generalBidegreeReindexedShearedLogT 1 B eRows
        (fun row => localSourceRatio s0 (d row) (e row))
        (fun row => localTargetRatio s0 (u row) (v row)) row| ≤
          Real.exp (-(1 - sigma) * Real.log xScale) :=
    generalBidegreeReindexedShearedLogT_bound_of_dyadicTargetEndpointScale
      1 B eRows (fun _ => i) d e u v s0 M xScale sigma
      hcond (fun row => hbox row) hs0 hM hlower hupper
      (fun _ => htargetScale) hxScale hsigma hlocalThreshold
  have hβ : ∀ row,
      |generalBidegreeReindexedShearedLogT 1 B eRows
        (fun row => localSourceRatio s0 (d row) (e row))
        (fun row => localTargetRatio s0 (u row) (v row)) row| ≤
          Real.exp (-(xDet * L)) := by
    intro row
    calc
      |generalBidegreeReindexedShearedLogT 1 B eRows
          (fun row => localSourceRatio s0 (d row) (e row))
          (fun row => localTargetRatio s0 (u row) (v row)) row| ≤
          Real.exp (-(1 - sigma) * Real.log xScale) := hβraw row
      _ = Real.exp (-(xDet * L)) := by
        congr 1
        rw [hxDetL]
        ring
  have hcost :
      |(∏ j : generalBidegreeFormIndex 1 B,
          ((dyadicFactorTupleFamilyPoints d e u v (r j)).1.2 : ℝ) ^ 1 *
            ((dyadicFactorTupleFamilyPoints d e u v (r j)).2.2 : ℝ) ^ B) *
          s0 ^ (((1 + 1) * (B + 1) * (1 + 2 * B)) / 2)| ≤
        Real.exp
          (baseCost + shearedComparableCoordinateLogLoss 1 B 2 24) :=
    dyadicFactorTupleFamilyPoints_hcost_logLoss_of_dyadicComparableBounds
      1 B d e u v r hcond hbox hM hlower hupper hbaseCost
  exact standardSelectedIntegralMinor_det_eq_zero_of_twoLayerFan_rate
    B k (dyadicFactorTupleFamilyPoints d e u v) eRows r hr s0
      (fun row => localSourceRatio s0 (d row) (e row))
      (fun row => localTargetRatio s0 (u row) (v row))
      (dyadicFactorTupleFamilyPoints_denominators_ne_zero_of_condition
        d e u v hcond)
      (dyadicFactorTupleFamilyPoints_local_coordinates d e u v hs0
        (fun row => (hcond row).2.1) (fun row => (hcond row).2.2.1))
      hS hT (m * L) (xDet * L) hellM hkpos hkB hfanLower hfanUpper
      hα hβ (baseCost + shearedComparableCoordinateLogLoss 1 B 2 24)
      hcost hrate

end

end PellPaper
