import Pell.Main3LargeAnalyticBlockKeyCellAggregation
import Pell.Main3LargeAnalyticWrongSignCellEmpty
import Pell.Main3LargeAnalyticRealCellCoverSelection
import Pell.Main3LargeAnalyticComplexCellCoverSelection
import Mathlib.Tactic

/-!
# Active-cell form of the exact Main3 block partition

The exact block partition initially sums over every mesh cell.  The sieve
aggregates naturally sum only over cells whose intrinsic target image is
nonempty.  This workspace proves that the discarded cells have empty point
fibres and then removes the branch incompatible with the sign of the shift.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- A nonempty fixed-key/cell point fibre has a nonempty intrinsic target
projection. -/
theorem main3LargeAnalytic_targetVectorImage_nonempty_of_pointFiber_nonempty
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (hnonempty :
      (main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
        htheta hY hi key cell).Nonempty) :
    (main3LargeAnalyticFixedKeyCellTargetVectorImage
      htheta hY hi key cell).Nonempty := by
  obtain ⟨p, hp⟩ := hnonempty
  let z := main3LargeAnalytic_blockCellCoordinatePoint htheta hY hi p
  have hz : z ∈
      main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
        htheta hY hi key cell := by
    exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
  refine ⟨shiftedSquareCoordinatePointTargetVector z, ?_⟩
  exact (mem_main3LargeAnalyticFixedKeyCellTargetVectorImage_iff
    htheta hY hi key cell _).mpr ⟨z, hz, rfl⟩

/-- A real mesh cell omitted from the active-cell filter has empty literal
point fibre. -/
theorem card_main3LargeAnalytic_realCellPointFiber_eq_zero_of_not_mem_nonempty
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : RealSquareMapCellPairIndex)
    (hcell : cell ∈ realSquareMapCellPairIndices
      (shiftedSquareEmbeddingScaleLoss (shiftedSquareA h v))
      (main3UnbalancedM theta Y))
    (hnot : cell ∉
      main3LargeAnalytic_nonemptyRealCellIndices htheta hY hi key) :
    (main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
      htheta hY hi key (Sum.inl cell)).card = 0 := by
  rw [Finset.card_eq_zero]
  apply Finset.not_nonempty_iff_eq_empty.mp
  intro hnonempty
  apply hnot
  exact (mem_main3LargeAnalytic_nonemptyRealCellIndices
    htheta hY hi key cell).mpr
      ⟨hcell,
        main3LargeAnalytic_targetVectorImage_nonempty_of_pointFiber_nonempty
          htheta hY hi key (Sum.inl cell) hnonempty⟩

/-- A complex mesh cell omitted from the active-cell filter has empty literal
point fibre. -/
theorem card_main3LargeAnalytic_complexCellPointFiber_eq_zero_of_not_mem_nonempty
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : ComplexUnitCircleSlopeCellIndex)
    (hcell : cell ∈ complexUnitCircleSlopeCellIndices
      (main3UnbalancedM theta Y))
    (hnot : cell ∉
      main3LargeAnalytic_nonemptyComplexCellIndices htheta hY hi key) :
    (main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
      htheta hY hi key (Sum.inr cell)).card = 0 := by
  rw [Finset.card_eq_zero]
  apply Finset.not_nonempty_iff_eq_empty.mp
  intro hnonempty
  apply hnot
  exact (mem_main3LargeAnalytic_nonemptyComplexCellIndices
    htheta hY hi key cell).mpr
      ⟨hcell,
        main3LargeAnalytic_targetVectorImage_nonempty_of_pointFiber_nonempty
          htheta hY hi key (Sum.inr cell) hnonempty⟩

/-- Summing over the ambient real mesh equals summing over the subtype of
active real cells. -/
theorem sum_main3LargeAnalytic_realCellPointFibers_eq_sum_nonemptyRealCells
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey) :
    (∑ cell ∈ realSquareMapCellPairIndices
        (shiftedSquareEmbeddingScaleLoss (shiftedSquareA h v))
        (main3UnbalancedM theta Y),
      (main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
        htheta hY hi key (Sum.inl cell)).card) =
      ∑ cell : ↑(main3LargeAnalytic_nonemptyRealCellIndices
          htheta hY hi key),
        (main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
          htheta hY hi key (Sum.inl cell.1)).card := by
  classical
  let ambient := realSquareMapCellPairIndices
    (shiftedSquareEmbeddingScaleLoss (shiftedSquareA h v))
    (main3UnbalancedM theta Y)
  let active := main3LargeAnalytic_nonemptyRealCellIndices htheta hY hi key
  have hsubset : active ⊆ ambient := by
    intro cell hcell
    exact (mem_main3LargeAnalytic_nonemptyRealCellIndices
      htheta hY hi key cell).mp hcell |>.1
  have hsum :
      (∑ cell ∈ active,
        (main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
          htheta hY hi key (Sum.inl cell)).card) =
      ∑ cell ∈ ambient,
        (main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
          htheta hY hi key (Sum.inl cell)).card := by
    apply Finset.sum_subset hsubset
    intro cell hcell hnot
    exact card_main3LargeAnalytic_realCellPointFiber_eq_zero_of_not_mem_nonempty
      htheta hY hi key cell hcell hnot
  rw [← hsum]
  exact Finset.sum_subtype active (fun _ => Iff.rfl) _

/-- Summing over the ambient complex mesh equals summing over the subtype of
active complex cells. -/
theorem sum_main3LargeAnalytic_complexCellPointFibers_eq_sum_nonemptyComplexCells
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey) :
    (∑ cell ∈ complexUnitCircleSlopeCellIndices
        (main3UnbalancedM theta Y),
      (main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
        htheta hY hi key (Sum.inr cell)).card) =
      ∑ cell : ↑(main3LargeAnalytic_nonemptyComplexCellIndices
          htheta hY hi key),
        (main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
          htheta hY hi key (Sum.inr cell.1)).card := by
  classical
  let ambient := complexUnitCircleSlopeCellIndices
    (main3UnbalancedM theta Y)
  let active := main3LargeAnalytic_nonemptyComplexCellIndices htheta hY hi key
  have hsubset : active ⊆ ambient := by
    intro cell hcell
    exact (mem_main3LargeAnalytic_nonemptyComplexCellIndices
      htheta hY hi key cell).mp hcell |>.1
  have hsum :
      (∑ cell ∈ active,
        (main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
          htheta hY hi key (Sum.inr cell)).card) =
      ∑ cell ∈ ambient,
        (main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
          htheta hY hi key (Sum.inr cell)).card := by
    apply Finset.sum_subset hsubset
    intro cell hcell hnot
    exact card_main3LargeAnalytic_complexCellPointFiber_eq_zero_of_not_mem_nonempty
      htheta hY hi key cell hcell hnot
  rw [← hsum]
  exact Finset.sum_subtype active (fun _ => Iff.rfl) _

/-- For a negative shift, one exact auxiliary-key fibre is precisely the sum
of its active real-cell fibres. -/
theorem card_main3LargeAnalytic_blockAuxiliaryPointFiber_eq_sum_nonemptyRealCells_of_shift_neg
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (ha : shiftedSquareA h v < 0) :
    (main3LargeAnalytic_blockAuxiliaryPointFiber htheta
        (by omega : 8 ≤ Y) hi key).card =
      ∑ cell : ↑(main3LargeAnalytic_nonemptyRealCellIndices
          htheta hY hi key),
        (main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
          htheta hY hi key (Sum.inl cell.1)).card := by
  classical
  rw [card_main3LargeAnalytic_blockAuxiliaryPointFiber_eq_sum_archimedeanCells
    htheta hY hi key]
  have hdisjoint : Disjoint
      ((realSquareMapCellPairIndices
        (shiftedSquareEmbeddingScaleLoss (shiftedSquareA h v))
        (main3UnbalancedM theta Y)).map
          main3LargeAnalytic_realArchimedeanCellEmbedding)
      ((complexUnitCircleSlopeCellIndices
        (main3UnbalancedM theta Y)).map
          main3LargeAnalytic_complexArchimedeanCellEmbedding) := by
    simp [Finset.disjoint_left,
      main3LargeAnalytic_realArchimedeanCellEmbedding,
      main3LargeAnalytic_complexArchimedeanCellEmbedding]
  rw [main3LargeAnalytic_archimedeanCellIndices,
    Finset.sum_union hdisjoint, Finset.sum_map, Finset.sum_map]
  simp only [main3LargeAnalytic_realArchimedeanCellEmbedding,
    main3LargeAnalytic_complexArchimedeanCellEmbedding,
    Function.Embedding.inl_apply, Function.Embedding.inr_apply]
  rw [sum_main3LargeAnalytic_realCellPointFibers_eq_sum_nonemptyRealCells
    htheta hY hi key]
  have hzero :
      (∑ cell ∈ complexUnitCircleSlopeCellIndices
          (main3UnbalancedM theta Y),
        (main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
          htheta hY hi key (Sum.inr cell)).card) = 0 := by
    apply Finset.sum_eq_zero
    intro cell hcell
    exact
      card_main3LargeAnalytic_complexArchimedeanCellPointFiber_eq_zero_of_shift_neg
        htheta hY hi key cell ha
  rw [hzero, add_zero]

/-- For a positive shift, one exact auxiliary-key fibre is precisely the sum
of its active complex-cell fibres. -/
theorem card_main3LargeAnalytic_blockAuxiliaryPointFiber_eq_sum_nonemptyComplexCells_of_shift_pos
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (ha : 0 < shiftedSquareA h v) :
    (main3LargeAnalytic_blockAuxiliaryPointFiber htheta
        (by omega : 8 ≤ Y) hi key).card =
      ∑ cell : ↑(main3LargeAnalytic_nonemptyComplexCellIndices
          htheta hY hi key),
        (main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
          htheta hY hi key (Sum.inr cell.1)).card := by
  classical
  rw [card_main3LargeAnalytic_blockAuxiliaryPointFiber_eq_sum_archimedeanCells
    htheta hY hi key]
  have hdisjoint : Disjoint
      ((realSquareMapCellPairIndices
        (shiftedSquareEmbeddingScaleLoss (shiftedSquareA h v))
        (main3UnbalancedM theta Y)).map
          main3LargeAnalytic_realArchimedeanCellEmbedding)
      ((complexUnitCircleSlopeCellIndices
        (main3UnbalancedM theta Y)).map
          main3LargeAnalytic_complexArchimedeanCellEmbedding) := by
    simp [Finset.disjoint_left,
      main3LargeAnalytic_realArchimedeanCellEmbedding,
      main3LargeAnalytic_complexArchimedeanCellEmbedding]
  rw [main3LargeAnalytic_archimedeanCellIndices,
    Finset.sum_union hdisjoint, Finset.sum_map, Finset.sum_map]
  simp only [main3LargeAnalytic_realArchimedeanCellEmbedding,
    main3LargeAnalytic_complexArchimedeanCellEmbedding,
    Function.Embedding.inl_apply, Function.Embedding.inr_apply]
  rw [sum_main3LargeAnalytic_complexCellPointFibers_eq_sum_nonemptyComplexCells
    htheta hY hi key]
  have hzero :
      (∑ cell ∈ realSquareMapCellPairIndices
          (shiftedSquareEmbeddingScaleLoss (shiftedSquareA h v))
          (main3UnbalancedM theta Y),
        (main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
          htheta hY hi key (Sum.inl cell)).card) = 0 := by
    apply Finset.sum_eq_zero
    intro cell hcell
    exact
      card_main3LargeAnalytic_realArchimedeanCellPointFiber_eq_zero_of_shift_pos
        htheta hY hi key cell ha
  rw [hzero, zero_add]

/-- Under a negative shift, the exact block cardinality is a key sum of the
active real-cell cardinality sums consumed by the real aggregate theorem. -/
theorem card_main3LargeAnalytic_block_eq_sum_auxiliaryKeys_nonemptyRealCells_of_shift_neg
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (ha : shiftedSquareA h v < 0) :
    (squarefreeShiftedSquareBlock
        (shiftedSquareA h v) D Y N).card =
      ∑ key ∈ main3LargeAnalytic_blockAuxiliaryKeyGate h v,
        ∑ cell : ↑(main3LargeAnalytic_nonemptyRealCellIndices
            htheta hY hi key),
          (main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
            htheta hY hi key (Sum.inl cell.1)).card := by
  rw [card_main3LargeAnalytic_block_eq_sum_auxiliaryPointFibers
    htheta (by omega : 8 ≤ Y) hi]
  apply Finset.sum_congr rfl
  intro key _hkey
  exact
    card_main3LargeAnalytic_blockAuxiliaryPointFiber_eq_sum_nonemptyRealCells_of_shift_neg
      htheta hY hi key ha

/-- Under a positive shift, the exact block cardinality is a key sum of the
active complex-cell cardinality sums consumed by the complex aggregate. -/
theorem card_main3LargeAnalytic_block_eq_sum_auxiliaryKeys_nonemptyComplexCells_of_shift_pos
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (ha : 0 < shiftedSquareA h v) :
    (squarefreeShiftedSquareBlock
        (shiftedSquareA h v) D Y N).card =
      ∑ key ∈ main3LargeAnalytic_blockAuxiliaryKeyGate h v,
        ∑ cell : ↑(main3LargeAnalytic_nonemptyComplexCellIndices
            htheta hY hi key),
          (main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
            htheta hY hi key (Sum.inr cell.1)).card := by
  rw [card_main3LargeAnalytic_block_eq_sum_auxiliaryPointFibers
    htheta (by omega : 8 ≤ Y) hi]
  apply Finset.sum_congr rfl
  intro key _hkey
  exact
    card_main3LargeAnalytic_blockAuxiliaryPointFiber_eq_sum_nonemptyComplexCells_of_shift_pos
      htheta hY hi key ha

end

end PellPaper
