import Pell.Main3LargeAnalyticBlockArchimedeanCellPartition

/-!
# Finite aggregation over large-analytic auxiliary keys and cells

This module combines the two exact deterministic partitions of one main3
large-analytic block.  It first writes the block cardinality as a literal
double sum over auxiliary scalar keys and archimedean cells, then derives the
uniform-fibre product bound.  The missing bound for one fixed-key/fixed-cell
fibre remains an explicit hypothesis.

No determinant, square-sieve, or asymptotic estimate is introduced here.
-/

namespace PellPaper

noncomputable section

open scoped BigOperators

/-- The original block is exactly the double sum of its fixed-key/fixed-cell
point fibres. -/
theorem card_main3LargeAnalytic_block_eq_sum_auxiliaryKeys_archimedeanCells
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y) :
    (squarefreeShiftedSquareBlock
        (shiftedSquareA h v) D Y N).card =
      ∑ key ∈ main3LargeAnalytic_blockAuxiliaryKeyGate h v,
        ∑ i ∈ main3LargeAnalytic_archimedeanCellIndices
            (shiftedSquareA h v) (main3UnbalancedM theta Y),
          (main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
            htheta hY hi key i).card := by
  rw [card_main3LargeAnalytic_block_eq_sum_auxiliaryPointFibers
    htheta (by omega : 8 ≤ Y) hi]
  apply Finset.sum_congr rfl
  intro key _hkey
  exact card_main3LargeAnalytic_blockAuxiliaryPointFiber_eq_sum_archimedeanCells
    htheta hY hi key

/-- A uniform bound for every literal fixed-key/fixed-cell fibre gives the
expected product bound for the whole block.  This theorem deliberately leaves
the arithmetic fibre estimate visible as `hfibre`. -/
theorem card_main3LargeAnalytic_block_le_keyCells_mul_of_uniform_fibre
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N K : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (hfibre : ∀ key ∈ main3LargeAnalytic_blockAuxiliaryKeyGate h v,
      ∀ i ∈ main3LargeAnalytic_archimedeanCellIndices
          (shiftedSquareA h v) (main3UnbalancedM theta Y),
        (main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
          htheta hY hi key i).card ≤ K) :
    (squarefreeShiftedSquareBlock
        (shiftedSquareA h v) D Y N).card ≤
      (main3LargeAnalytic_blockAuxiliaryKeyGate h v).card *
        (main3LargeAnalytic_archimedeanCellIndices
          (shiftedSquareA h v) (main3UnbalancedM theta Y)).card * K := by
  rw [card_main3LargeAnalytic_block_eq_sum_auxiliaryKeys_archimedeanCells
    htheta hY hi]
  calc
    (∑ key ∈ main3LargeAnalytic_blockAuxiliaryKeyGate h v,
        ∑ i ∈ main3LargeAnalytic_archimedeanCellIndices
            (shiftedSquareA h v) (main3UnbalancedM theta Y),
          (main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
            htheta hY hi key i).card) ≤
        ∑ _key ∈ main3LargeAnalytic_blockAuxiliaryKeyGate h v,
          ∑ _i ∈ main3LargeAnalytic_archimedeanCellIndices
              (shiftedSquareA h v) (main3UnbalancedM theta Y), K := by
      apply Finset.sum_le_sum
      intro key hkey
      apply Finset.sum_le_sum
      intro i hiCell
      exact hfibre key hkey i hiCell
    _ = (main3LargeAnalytic_blockAuxiliaryKeyGate h v).card *
          (main3LargeAnalytic_archimedeanCellIndices
            (shiftedSquareA h v) (main3UnbalancedM theta Y)).card * K := by
      simp
      ring

/-- The preceding product bound with the exact combined real/complex cell
count exposed. -/
theorem card_main3LargeAnalytic_block_le_explicit_keyCells_mul_of_uniform_fibre
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N K : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (hfibre : ∀ key ∈ main3LargeAnalytic_blockAuxiliaryKeyGate h v,
      ∀ i ∈ main3LargeAnalytic_archimedeanCellIndices
          (shiftedSquareA h v) (main3UnbalancedM theta Y),
        (main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
          htheta hY hi key i).card ≤ K) :
    (squarefreeShiftedSquareBlock
        (shiftedSquareA h v) D Y N).card ≤
      (main3LargeAnalytic_blockAuxiliaryKeyGate h v).card *
        (36 * main3UnbalancedM theta Y *
            annularDyadicScaleCount
              (shiftedSquareEmbeddingScaleLoss (shiftedSquareA h v)) +
          (8 * main3UnbalancedM theta Y + 4)) * K := by
  simpa only [card_main3LargeAnalytic_archimedeanCellIndices] using
    card_main3LargeAnalytic_block_le_keyCells_mul_of_uniform_fibre
      htheta hY hi hfibre

end

end PellPaper
