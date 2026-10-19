import Pell.Main3LargeAnalyticBlockArchimedeanCellPartition

/-!
# Empty main3 archimedean fibres with the wrong sign

The literal real-cell predicate contains a witness that the fixed shift is
negative, while the literal complex-cell predicate contains a witness that
it is positive.  These witnesses pass directly through membership in the
fixed-key cell fibre.  Consequently every cell from the branch incompatible
with the shift sign has cardinality zero.
-/

namespace PellPaper

noncomputable section

/-! ## Real-cell fibres -/

/-- Membership in a real archimedean cell fibre exposes the negative-shift
witness stored in its literal cell predicate. -/
theorem main3LargeAnalytic_shift_neg_of_mem_realArchimedeanCellPointFiber
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : RealSquareMapCellPairIndex)
    {p : Main3LargeAnalyticSquarefreeBlockPoint h v D Y N}
    (hp : p ∈ main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
      htheta hY hi key (Sum.inl cell)) :
    shiftedSquareA h v < 0 := by
  have hgeometry :=
    (main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber_spec
      htheta hY hi hp).2.2
  simp only [Main3LargeAnalyticBlockPointInArchimedeanCell,
    InMain3LargeAnalyticArchimedeanCell] at hgeometry
  exact hgeometry.choose

/-- A nonempty real archimedean cell fibre forces the fixed shift to be
negative. -/
theorem main3LargeAnalytic_shift_neg_of_realArchimedeanCellPointFiber_nonempty
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : RealSquareMapCellPairIndex)
    (hnonempty :
      (main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
        htheta hY hi key (Sum.inl cell)).Nonempty) :
    shiftedSquareA h v < 0 := by
  obtain ⟨p, hp⟩ := hnonempty
  exact
    main3LargeAnalytic_shift_neg_of_mem_realArchimedeanCellPointFiber
      htheta hY hi key cell hp

/-- Under a positive fixed shift, every real archimedean cell fibre has
cardinality zero. -/
theorem card_main3LargeAnalytic_realArchimedeanCellPointFiber_eq_zero_of_shift_pos
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : RealSquareMapCellPairIndex)
    (ha : 0 < shiftedSquareA h v) :
    (main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
      htheta hY hi key (Sum.inl cell)).card = 0 := by
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  exact (not_lt_of_ge ha.le)
    (main3LargeAnalytic_shift_neg_of_mem_realArchimedeanCellPointFiber
      htheta hY hi key cell hp)

/-! ## Complex-cell fibres -/

/-- Membership in a complex archimedean cell fibre exposes the positive-shift
witness stored in its literal cell predicate. -/
theorem main3LargeAnalytic_shift_pos_of_mem_complexArchimedeanCellPointFiber
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : ComplexUnitCircleSlopeCellIndex)
    {p : Main3LargeAnalyticSquarefreeBlockPoint h v D Y N}
    (hp : p ∈ main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
      htheta hY hi key (Sum.inr cell)) :
    0 < shiftedSquareA h v := by
  have hgeometry :=
    (main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber_spec
      htheta hY hi hp).2.2
  simp only [Main3LargeAnalyticBlockPointInArchimedeanCell,
    InMain3LargeAnalyticArchimedeanCell] at hgeometry
  exact hgeometry.choose

/-- A nonempty complex archimedean cell fibre forces the fixed shift to be
positive. -/
theorem main3LargeAnalytic_shift_pos_of_complexArchimedeanCellPointFiber_nonempty
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : ComplexUnitCircleSlopeCellIndex)
    (hnonempty :
      (main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
        htheta hY hi key (Sum.inr cell)).Nonempty) :
    0 < shiftedSquareA h v := by
  obtain ⟨p, hp⟩ := hnonempty
  exact
    main3LargeAnalytic_shift_pos_of_mem_complexArchimedeanCellPointFiber
      htheta hY hi key cell hp

/-- Under a negative fixed shift, every complex archimedean cell fibre has
cardinality zero. -/
theorem card_main3LargeAnalytic_complexArchimedeanCellPointFiber_eq_zero_of_shift_neg
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : ComplexUnitCircleSlopeCellIndex)
    (ha : shiftedSquareA h v < 0) :
    (main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
      htheta hY hi key (Sum.inr cell)).card = 0 := by
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  exact (not_lt_of_ge ha.le)
    (main3LargeAnalytic_shift_pos_of_mem_complexArchimedeanCellPointFiber
      htheta hY hi key cell hp)

end

end PellPaper
