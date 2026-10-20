import Pell.Main3LargeAnalyticFixedKeyCellArithmetic
import Pell.PrimitiveBinaryZeroCount
import Mathlib.Tactic

/-!
# Common-factor zeros in one main3 large-analytic key and cell

This file isolates the first finite counting step after the fixed-key,
fixed-cell auxiliary form has been factored.  The common-target-factor-zero
branch is partitioned by its literal target vector.  Target primitivity and
the fixed-key rectangle reduce the number of possible targets to twice the
factor degree, leaving only a uniform bound for the source fibre over one
fixed target.

No source-fibre estimate, residual square estimate, cell sum, or block sum is
assumed or proved here.
-/

namespace PellPaper

noncomputable section

/-- The exact fibre of the actual fixed-key, fixed-cell vector image over a
literal target vector.  Its cardinality is the number of retained source
vectors above that target. -/
def main3LargeAnalyticFixedKeyCellTargetFibre
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (y : Fin 2 → ℤ) :
    Finset ((Fin 2 → ℤ) × (Fin 2 → ℤ)) :=
  (main3LargeAnalyticFixedKeyCellVectorImage htheta hY hi key cell).filter
    fun p => p.2 = y

@[simp]
theorem mem_main3LargeAnalyticFixedKeyCellTargetFibre
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (y : Fin 2 → ℤ)
    (p : (Fin 2 → ℤ) × (Fin 2 → ℤ)) :
    p ∈ main3LargeAnalyticFixedKeyCellTargetFibre htheta hY hi key cell y ↔
      p ∈ main3LargeAnalyticFixedKeyCellVectorImage htheta hY hi key cell ∧
        p.2 = y := by
  simp [main3LargeAnalyticFixedKeyCellTargetFibre]

/-- Every target occurring in the common-factor-zero branch is a primitive
zero of the selected homogeneous factor inside the actual fixed-key target
rectangle. -/
theorem main3LargeAnalytic_commonFactorZero_targetImage_subset
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N B : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (data : Main3LargeAnalyticFixedKeyCellAuxiliaryFactorData
      htheta hY hi key cell B) :
    ((main3LargeAnalyticFixedKeyCellVectorImage htheta hY hi key cell).filter
        fun p => MvPolynomial.eval p.2 data.targetFactor = 0).image Prod.snd ⊆
      (main3LargeAnalyticFixedKeyTargetRectangle
        (shiftedSquareA h v) Y key).filter fun y =>
          IsCoprime (y 0) (y 1) ∧
            MvPolynomial.eval y data.targetFactor = 0 := by
  classical
  intro y hy
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨hpImage, hpZero⟩ := Finset.mem_filter.mp hp
  obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hpImage
  have hprimitive :=
    (main3LargeAnalytic_blockCellCoordinatePointImage_primitive
      htheta hY hi hz).2
  have hrectangle :=
    main3LargeAnalytic_fixedKeyCell_targetVector_mem_rectangle
      htheta hY hi hz
  have heq : main3GeneralBidegreePointVectorEquiv.toEmbedding z =
      (shiftedSquareCoordinatePointSourceVector z,
        shiftedSquareCoordinatePointTargetVector z) :=
    main3GeneralBidegreePointVectorEquiv_apply z
  refine Finset.mem_filter.mpr ⟨?_, hprimitive, ?_⟩
  · rw [heq]
    exact hrectangle
  · rw [heq]
    exact hpZero

/-- If every exact target fibre has at most `sourceFibreBound` members, then
the entire common-factor-zero branch has at most twice the factor degree times
that bound.  The hypothesis is the remaining arithmetic source-fibre
boundary; all target counting is discharged here. -/
theorem card_main3LargeAnalytic_commonFactorZero_le_two_mul_factorDegree_mul_of_targetFibre_bound
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N B : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (data : Main3LargeAnalyticFixedKeyCellAuxiliaryFactorData
      htheta hY hi key cell B)
    (sourceFibreBound : ℕ)
    (hsourceFibre : ∀ y ∈
      main3LargeAnalyticFixedKeyTargetRectangle (shiftedSquareA h v) Y key,
      (main3LargeAnalyticFixedKeyCellTargetFibre
        htheta hY hi key cell y).card ≤ sourceFibreBound) :
    ((main3LargeAnalyticFixedKeyCellVectorImage htheta hY hi key cell).filter
        fun p => MvPolynomial.eval p.2 data.targetFactor = 0).card ≤
      (2 * data.factorDegree) * sourceFibreBound := by
  classical
  let S :=
    (main3LargeAnalyticFixedKeyCellVectorImage htheta hY hi key cell).filter
      fun p => MvPolynomial.eval p.2 data.targetFactor = 0
  let T :=
    (main3LargeAnalyticFixedKeyTargetRectangle
      (shiftedSquareA h v) Y key).filter fun y =>
        IsCoprime (y 0) (y 1) ∧
          MvPolynomial.eval y data.targetFactor = 0
  have hST : S.image Prod.snd ⊆ T := by
    simpa only [S, T] using
      main3LargeAnalytic_commonFactorZero_targetImage_subset
        htheta hY hi key cell data
  have hTcard : T.card ≤ 2 * data.factorDegree := by
    apply card_primitive_homogeneous_binary_zeros_le
      data.targetFactor data.factorDegree data.targetFactor_homogeneous
        data.targetFactor_ne_zero
    intro y hy
    exact (Finset.mem_filter.mp hy).2
  have hfibre : ∀ y ∈ S.image Prod.snd,
      (S.filter fun p => p.2 = y).card ≤ sourceFibreBound := by
    intro y hy
    have hyT : y ∈ T := hST hy
    have hsub : (S.filter fun p => p.2 = y) ⊆
        main3LargeAnalyticFixedKeyCellTargetFibre
          htheta hY hi key cell y := by
      intro p hp
      obtain ⟨hpS, hpy⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hpS).1, hpy⟩
    exact (Finset.card_le_card hsub).trans
      (hsourceFibre y (Finset.mem_filter.mp hyT).1)
  calc
    ((main3LargeAnalyticFixedKeyCellVectorImage htheta hY hi key cell).filter
        fun p => MvPolynomial.eval p.2 data.targetFactor = 0).card = S.card := by rfl
    _ = ∑ y ∈ S.image Prod.snd, (S.filter fun p => p.2 = y).card :=
      Finset.card_eq_sum_card_image Prod.snd S
    _ ≤ ∑ _y ∈ S.image Prod.snd, sourceFibreBound :=
      Finset.sum_le_sum hfibre
    _ = (S.image Prod.snd).card * sourceFibreBound := by simp
    _ ≤ T.card * sourceFibreBound :=
      Nat.mul_le_mul_right sourceFibreBound (Finset.card_le_card hST)
    _ ≤ (2 * data.factorDegree) * sourceFibreBound :=
      Nat.mul_le_mul_right sourceFibreBound hTcard

end

end PellPaper
