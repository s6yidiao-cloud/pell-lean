import Pell.DyadicTwoLayerFanFiniteCell
import Pell.DyadicTargetImageGeometry
import Pell.DyadicComparableCostPolynomialMeshActualCell
import Pell.GeneralBidegreeOneSpecialization

/-!
# Exact-fan auxiliary forms on literal source-target tuple cells

This module specializes the finite exact-fan endpoint to the literal
source-ratio/target-ceiling cells used by the balanced aggregation.  The
target-ceiling filter only restricts the row family.  All local analytic data
come from the containing source-ratio cell and dyadic box.
-/

namespace PellPaper

noncomputable section

/-- **Literal source-target-cell exact-fan auxiliary form.**  Under the one
exact logarithmic fan-rate inequality, every source-target tuple cell lies
on a nonzero integral two-layer form with the literal rank-sensitive
Hadamard height.  No occupancy hypothesis is needed. -/
theorem exists_nonzero_real_bounded_integral_twoLayerForm_of_dyadicSourceTargetTupleCell_twoLayerFanRate
    (B fanK : ℕ) {theta : ℝ} {Y : ℕ}
    {boxIndex : ℕ × ℕ × ℕ × ℕ} {M sourceIndex : ℕ}
    {targetIndex : ℤ} (hM : 0 < M)
    (xScale sigma m xDet L baseCost : ℝ)
    (htargetScale : xScale ≤ ((2 ^ boxIndex.2.1 : ℕ) : ℝ) ^ 2 *
      ((2 ^ boxIndex.2.2.2 : ℕ) : ℝ))
    (hxScale : 1536 ≤ xScale) (hsigma : 0 < sigma)
    (hlocalThreshold :
      Real.exp (Real.log (1536 : ℝ) / sigma) ≤ xScale)
    (hsourceDecay : m * L ≤ Real.log (M : ℝ))
    (hxDetL : xDet * L = (1 - sigma) * Real.log xScale)
    (hellM : 0 < m * L)
    (hfanKpos : 1 ≤ fanK) (hfanKB : fanK ≤ B)
    (hfanLower : (2 * (fanK : ℝ) - 1) * (m * L) ≤ xDet * L)
    (hfanUpper : xDet * L ≤ (2 * (fanK : ℝ) + 1) * (m * L))
    (hbaseCost :
      ((2 * ((2 ^ boxIndex.1 : ℕ) : ℝ)) *
        (2 * ((2 ^ boxIndex.2.1 : ℕ) : ℝ))) ^
          (1 * ((1 + 1) * (B + 1)) / 2) *
        ((2 * ((2 ^ boxIndex.2.2.1 : ℕ) : ℝ)) *
          (2 * ((2 ^ boxIndex.2.2.2 : ℕ) : ℝ))) ^
            (B * ((1 + 1) * (B + 1)) / 2) ≤ Real.exp baseCost)
    (hrate :
      (baseCost + shearedComparableCoordinateLogLoss 1 B 2 24) +
          Real.log (Nat.factorial
            (Fintype.card (generalBidegreeGrid 1 B)) : ℝ) +
        twoLayerFanTaylorTail B *
          (Fintype.card (generalBidegreeGrid 1 B) : ℝ) <
      twoLayerWeight B fanK (m * L) (xDet * L)) :
    ∃ r : ℕ, r < 2 * (B + 1) ∧
      ∃ f : twoLayerFormIndex B → ℤ, f ≠ 0 ∧
        (∀ q ∈ dyadicSourceTargetTupleCell theta Y boxIndex M
            sourceIndex targetIndex,
          twoLayerFormEval B f
            (dyadicFactorTupleToGeneralBidegreeFormPoint q) = 0) ∧
          ∀ ab, (|f ab| : ℝ) ≤
            (√(r : ℝ) *
              (((dyadicSourceCoordinateBound boxIndex : ℤ) ^ 1 *
                (dyadicTargetCoordinateBound boxIndex : ℤ) ^ B : ℤ) : ℝ)) ^ r := by
  let S := dyadicSourceTargetTupleCell theta Y boxIndex M
    sourceIndex targetIndex
  let cell := dyadicFactorTuplePointCell S
  let tuple : {p // p ∈ cell} → ℕ × ℕ × ℕ × ℕ := fun p =>
    dyadicFactorTuplePointCellPreimage S p
  let d : {p // p ∈ cell} → ℕ := fun p => (tuple p).1
  let e : {p // p ∈ cell} → ℕ := fun p => (tuple p).2.1
  let u : {p // p ∈ cell} → ℕ := fun p => (tuple p).2.2.1
  let v : {p // p ∈ cell} → ℕ := fun p => (tuple p).2.2.2
  have hMreal : (1 : ℝ) ≤ (M : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hM)
  have hcenterpos :
      0 < dyadicFactorBoxLocalRatioCenter boxIndex M sourceIndex := by
    unfold dyadicFactorBoxLocalRatioCenter
    exact mul_pos (dyadicFactorBoxLocalRatioStart_pos boxIndex)
      (pow_pos (by
        unfold localRatioMeshStep
        positivity) _)
  have hpoint : ∀ p : {p // p ∈ cell},
      dyadicFactorTupleFamilyPoints d e u v p = p.1 := by
    intro p
    change dyadicFactorTupleToGeneralBidegreeFormPoint
      (d p, e p, u p, v p) = p.1
    simpa [d, e, u, v, tuple, cell] using
      dyadicFactorTuplePointCellPreimage_map_eq S p
  have hcond : ∀ p : {p // p ∈ cell}, DyadicFactorCondition theta Y
      (d p) (e p) (u p) (v p) := by
    intro p
    have hpS : tuple p ∈ S := by
      simpa [tuple, cell] using dyadicFactorTuplePointCellPreimage_mem S p
    have hlocal : tuple p ∈
        dyadicFactorBoxLocalRatioCell theta Y boxIndex M sourceIndex :=
      (Finset.mem_filter.mp hpS).1
    have hambient := (mem_dyadicFactorBoxLocalRatioCell hlocal).1
    exact mem_dyadicFactorTuples.mp (Finset.mem_inter.mp hambient).1
  have hbox : ∀ p : {p // p ∈ cell},
      (d p, e p, u p, v p) ∈ dyadicBox boxIndex := by
    intro p
    have hpS : tuple p ∈ S := by
      simpa [tuple, cell] using dyadicFactorTuplePointCellPreimage_mem S p
    have hlocal : tuple p ∈
        dyadicFactorBoxLocalRatioCell theta Y boxIndex M sourceIndex :=
      (Finset.mem_filter.mp hpS).1
    have hambient := (mem_dyadicFactorBoxLocalRatioCell hlocal).1
    exact (Finset.mem_inter.mp hambient).2
  have hwindow : ∀ p : {p // p ∈ cell},
      dyadicFactorBoxLocalRatioCenter boxIndex M sourceIndex ≤
          (d p : ℝ) / (e p : ℝ) ∧
        (d p : ℝ) / (e p : ℝ) ≤
          dyadicFactorBoxLocalRatioCenter boxIndex M sourceIndex *
            (1 + 1 / (M : ℝ)) := by
    intro p
    have hpS : tuple p ∈ S := by
      simpa [tuple, cell] using dyadicFactorTuplePointCellPreimage_mem S p
    have hlocal : tuple p ∈
        dyadicFactorBoxLocalRatioCell theta Y boxIndex M sourceIndex :=
      (Finset.mem_filter.mp hpS).1
    simpa [d, e, tuple] using
      dyadicFactorBoxLocalRatioCell_commonWindow hlocal
  obtain ⟨r, hr, f, hfne, hfvanish, hfheight⟩ :=
    exists_nonzero_real_bounded_integral_generalBidegreeOneForm_of_finset_uniformDyadicTwoLayerFanRate
      B fanK cell d e u v hpoint
      (dyadicFactorBoxLocalRatioCenter boxIndex M sourceIndex)
      (M : ℝ) xScale sigma m xDet L baseCost
      hcond hbox hcenterpos hMreal
      (fun p => (hwindow p).1) (fun p => (hwindow p).2)
      htargetScale hxScale hsigma hlocalThreshold hsourceDecay hxDetL
      hellM hfanKpos hfanKB hfanLower hfanUpper hbaseCost hrate
  refine ⟨r, hr, f, hfne, ?_, hfheight⟩
  intro q hq
  have hp : dyadicFactorTupleToGeneralBidegreeFormPoint q ∈ cell := by
    exact Finset.mem_map.mpr ⟨q, by simpa [S] using hq, rfl⟩
  simpa only [generalBidegreeFormEval_one_eq_twoLayerFormEval] using
    hfvanish _ hp

end

end PellPaper
