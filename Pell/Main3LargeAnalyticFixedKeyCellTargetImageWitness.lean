import Pell.Main3LargeAnalyticFixedKeyCellIntrinsicArithmetic

/-!
# Recovering actual coordinate points from the intrinsic target image

The intrinsic arithmetic split keeps only the target-vector projection of one
fixed-key, fixed-cell point image.  This file records the exact inverse
membership statement, so every later real- or complex-place geometric fact can
be recovered from a target in that projection without replacing it by a coarse
ambient rectangle.
-/

namespace PellPaper

noncomputable section

/-- Membership in the intrinsic target image is exactly witnessed by an actual
coordinate point in the same fixed key and archimedean cell. -/
theorem mem_main3LargeAnalyticFixedKeyCellTargetVectorImage_iff
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (y : Fin 2 → ℤ) :
    y ∈ main3LargeAnalyticFixedKeyCellTargetVectorImage
        htheta hY hi key cell ↔
      ∃ z ∈
          main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
            htheta hY hi key cell,
        shiftedSquareCoordinatePointTargetVector z = y := by
  constructor
  · intro hy
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hp
    exact ⟨z, hz,
      (congrArg Prod.snd
        (main3GeneralBidegreePointVectorEquiv_apply z)).symm⟩
  · rintro ⟨z, hz, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨main3GeneralBidegreePointVectorEquiv z, ?_, ?_⟩
    · exact Finset.mem_map.mpr ⟨z, hz, rfl⟩
    · exact congrArg Prod.snd
        (main3GeneralBidegreePointVectorEquiv_apply z)

/-- Every target retained by the intrinsic projection remains primitive. -/
theorem main3LargeAnalyticFixedKeyCellTargetVectorImage_primitive
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    {y : Fin 2 → ℤ}
    (hy : y ∈ main3LargeAnalyticFixedKeyCellTargetVectorImage
      htheta hY hi key cell) :
    IsCoprime (y 0) (y 1) := by
  obtain ⟨z, hz, rfl⟩ :=
    (mem_main3LargeAnalyticFixedKeyCellTargetVectorImage_iff
      htheta hY hi key cell _).mp hy
  exact (main3LargeAnalytic_blockCellCoordinatePointImage_primitive
    htheta hY hi hz).2

end

end PellPaper
