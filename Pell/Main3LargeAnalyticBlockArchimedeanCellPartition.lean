import Pell.Main3LargeAnalyticBlockAuxiliaryPartition
import Pell.Main3LargeAnalyticMeshErrorAbsorption
import Pell.ShiftedSquareRealPlaceCellPairAdapter
import Pell.ShiftedSquareImaginaryPlaceCellPairAdapter

/-!
# Archimedean cell partition of one auxiliary-key fibre

For every point of a fixed main3 large-analytic squarefree block, the
deterministic fixed-basis certificate already contains one literal package
`C.P`.  According to the sign of the fixed shift, this module sends that
same package either to the explicit real-place square-map cover or to the
explicit imaginary-place unit-circle cover.

The two index families are embedded into a disjoint sum.  Their combined
cardinality is exactly the sum of the real and complex counts.  A classical
selector then partitions each fixed auxiliary-key point fibre exactly by
its selected archimedean cell.  No determinant estimate, individual-fibre
bound, or arithmetic point count is asserted.
-/

namespace PellPaper

noncomputable section

open scoped BigOperators

/-- A disjoint tag for the real-place and imaginary-place square-map cells. -/
abbrev Main3LargeAnalyticArchimedeanCellIndex :=
  RealSquareMapCellPairIndex ⊕ ComplexUnitCircleSlopeCellIndex

/-- The real-cell inclusion into the disjoint archimedean index type. -/
def main3LargeAnalytic_realArchimedeanCellEmbedding :
    RealSquareMapCellPairIndex ↪ Main3LargeAnalyticArchimedeanCellIndex :=
  Function.Embedding.inl

/-- The complex-cell inclusion into the disjoint archimedean index type. -/
def main3LargeAnalytic_complexArchimedeanCellEmbedding :
    ComplexUnitCircleSlopeCellIndex ↪
      Main3LargeAnalyticArchimedeanCellIndex :=
  Function.Embedding.inr

/-- The literal union of the real and complex cell-index families. -/
def main3LargeAnalytic_archimedeanCellIndices (a : ℤ) (M : ℕ) :
    Finset Main3LargeAnalyticArchimedeanCellIndex :=
  (realSquareMapCellPairIndices (shiftedSquareEmbeddingScaleLoss a) M).map
      main3LargeAnalytic_realArchimedeanCellEmbedding ∪
    (complexUnitCircleSlopeCellIndices M).map
      main3LargeAnalytic_complexArchimedeanCellEmbedding

@[simp]
theorem mem_main3LargeAnalytic_archimedeanCellIndices_inl
    {a : ℤ} {M : ℕ} {i : RealSquareMapCellPairIndex} :
    Sum.inl i ∈ main3LargeAnalytic_archimedeanCellIndices a M ↔
      i ∈ realSquareMapCellPairIndices
        (shiftedSquareEmbeddingScaleLoss a) M := by
  simp [main3LargeAnalytic_archimedeanCellIndices,
    main3LargeAnalytic_realArchimedeanCellEmbedding,
    main3LargeAnalytic_complexArchimedeanCellEmbedding]

@[simp]
theorem mem_main3LargeAnalytic_archimedeanCellIndices_inr
    {a : ℤ} {M : ℕ} {i : ComplexUnitCircleSlopeCellIndex} :
    Sum.inr i ∈ main3LargeAnalytic_archimedeanCellIndices a M ↔
      i ∈ complexUnitCircleSlopeCellIndices M := by
  simp [main3LargeAnalytic_archimedeanCellIndices,
    main3LargeAnalytic_realArchimedeanCellEmbedding,
    main3LargeAnalytic_complexArchimedeanCellEmbedding]

/-- Exact combined index count.  The addition is literal because the two
families carry different `Sum` tags. -/
@[simp]
theorem card_main3LargeAnalytic_archimedeanCellIndices (a : ℤ) (M : ℕ) :
    (main3LargeAnalytic_archimedeanCellIndices a M).card =
      36 * M * annularDyadicScaleCount
          (shiftedSquareEmbeddingScaleLoss a) +
        (8 * M + 4) := by
  have hdisjoint : Disjoint
      ((realSquareMapCellPairIndices
        (shiftedSquareEmbeddingScaleLoss a) M).map
          main3LargeAnalytic_realArchimedeanCellEmbedding)
      ((complexUnitCircleSlopeCellIndices M).map
          main3LargeAnalytic_complexArchimedeanCellEmbedding) := by
    simp [Finset.disjoint_left,
      main3LargeAnalytic_realArchimedeanCellEmbedding,
      main3LargeAnalytic_complexArchimedeanCellEmbedding]
  rw [main3LargeAnalytic_archimedeanCellIndices,
    Finset.card_union_of_disjoint hdisjoint]
  simp
  ring

/-- Membership of one package in a selected archimedean cell.  The left
branch carries a proof that the shift is negative and evaluates the exact
package at the explicit positive real place.  The right branch carries a
proof that the shift is positive and evaluates the same package at the
explicit positive-imaginary place. -/
def InMain3LargeAnalyticArchimedeanCell
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (M : ℕ) (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq)
    (i : Main3LargeAnalyticArchimedeanCellIndex) : Prop :=
  match i with
  | Sum.inl realIndex =>
      ∃ ha : a < 0,
        InRealSquareMapCellPair (shiftedSquareEmbeddingScaleLoss a) M realIndex
          ((shiftedSquareSourceEmbeddingRatio P
              (shiftedSquarePositiveRealPlaceEmbedding a ha)).re,
            (shiftedSquareTargetEmbeddingRatio P
              (shiftedSquarePositiveRealPlaceEmbedding a ha)).re)
  | Sum.inr complexIndex =>
      ∃ ha : 0 < a,
        InComplexUnitCircleSquareMapCellPair M complexIndex
          (shiftedSquareSourceEmbeddingRatio P
              (shiftedSquareImaginaryPlaceEmbedding a ha),
            shiftedSquareTargetEmbeddingRatio P
              (shiftedSquareImaginaryPlaceEmbedding a ha))

private theorem main3LargeAnalytic_eight_le_of_ge_65536
    {Y : ℕ} (hY : 65536 ≤ Y) : 8 ≤ Y := by
  omega

/-- The cell predicate specialized to the deterministic certificate at one
attached block point.  This definition mentions the same literal `C.P`
used by `main3LargeAnalytic_blockCoordinateCode`. -/
def Main3LargeAnalyticBlockPointInArchimedeanCell
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (p : Main3LargeAnalyticSquarefreeBlockPoint h v D Y N)
    (i : Main3LargeAnalyticArchimedeanCellIndex) : Prop := by
  letI : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let C := main3LargeAnalytic_blockFixedBasisEncodingCertificate
    htheta (main3LargeAnalytic_eight_le_of_ge_65536 hY) hi p
  exact InMain3LargeAnalyticArchimedeanCell
    (main3UnbalancedM theta Y) C.P i

/-- Every attached point enters one literal cell, using its already selected
fixed-basis package and the common original-`theta` mesh. -/
theorem exists_main3LargeAnalytic_blockPoint_archimedeanCell
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (p : Main3LargeAnalyticSquarefreeBlockPoint h v D Y N) :
    ∃ i ∈ main3LargeAnalytic_archimedeanCellIndices
        (shiftedSquareA h v) (main3UnbalancedM theta Y),
      Main3LargeAnalyticBlockPointInArchimedeanCell
        htheta hY hi p i := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let C := main3LargeAnalytic_blockFixedBasisEncodingCertificate
    htheta (main3LargeAnalytic_eight_le_of_ge_65536 hY) hi p
  have hM : 0 < main3UnbalancedM theta Y :=
    (main3UnbalancedM_parameter_package theta Y htheta (by omega)).1
  have hmesh :
      8 * (main3UnbalancedM theta Y : ℝ) *
          Real.sqrt |(shiftedSquareA h v : ℝ)| ≤ (p.1.2.2 : ℝ) :=
    main3LargeAnalytic_unbalancedMesh_mul_sqrt_shift_le_n
      htheta hY hi p.2
  rcases lt_or_gt_of_ne C.scaled.shift_ne_zero with ha | ha
  · obtain ⟨i, hiIndex, hiCell⟩ :=
      exists_shiftedSquare_positiveRealPlace_realSquareMapCellPair
        ha C.scaled.base.source_pos C.scaled.base.target_pos
          C.scaled.base.shift_dominance hM hmesh C.P
    refine ⟨Sum.inl i, ?_, ?_⟩
    · exact mem_main3LargeAnalytic_archimedeanCellIndices_inl.mpr hiIndex
    · change InMain3LargeAnalyticArchimedeanCell
        (main3UnbalancedM theta Y) C.P (Sum.inl i)
      exact ⟨ha, hiCell⟩
  · obtain ⟨i, hiIndex, hiCell⟩ :=
      exists_shiftedSquare_imaginaryPlace_complexUnitCircleSquareMapCellPair
        ha C.scaled.base.source_pos C.scaled.base.target_pos
          C.scaled.base.shift_dominance hM hmesh C.P
    refine ⟨Sum.inr i, ?_, ?_⟩
    · exact mem_main3LargeAnalytic_archimedeanCellIndices_inr.mpr hiIndex
    · change InMain3LargeAnalyticArchimedeanCell
        (main3UnbalancedM theta Y) C.P (Sum.inr i)
      exact ⟨ha, hiCell⟩

/-- A deterministic selected archimedean cell for each attached point. -/
noncomputable def main3LargeAnalytic_blockPointArchimedeanCellSelector
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (p : Main3LargeAnalyticSquarefreeBlockPoint h v D Y N) :
    Main3LargeAnalyticArchimedeanCellIndex :=
  Classical.choose
    (exists_main3LargeAnalytic_blockPoint_archimedeanCell htheta hY hi p)

/-- The deterministic selector belongs to the literal combined index set. -/
theorem main3LargeAnalytic_blockPointArchimedeanCellSelector_mem
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (p : Main3LargeAnalyticSquarefreeBlockPoint h v D Y N) :
    main3LargeAnalytic_blockPointArchimedeanCellSelector htheta hY hi p ∈
      main3LargeAnalytic_archimedeanCellIndices
        (shiftedSquareA h v) (main3UnbalancedM theta Y) :=
  (Classical.choose_spec
    (exists_main3LargeAnalytic_blockPoint_archimedeanCell
      htheta hY hi p)).1

/-- The deterministic selector's geometry concerns the exact package from
the deterministic fixed-basis certificate. -/
theorem main3LargeAnalytic_blockPointArchimedeanCellSelector_spec
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (p : Main3LargeAnalyticSquarefreeBlockPoint h v D Y N) :
    Main3LargeAnalyticBlockPointInArchimedeanCell htheta hY hi p
      (main3LargeAnalytic_blockPointArchimedeanCellSelector
        htheta hY hi p) :=
  (Classical.choose_spec
    (exists_main3LargeAnalytic_blockPoint_archimedeanCell
      htheta hY hi p)).2

/-- Explicit same-certificate check: cell geometry uses `C.P`, while the
coordinate code is the encoded solution of that very `C`. -/
theorem main3LargeAnalytic_blockPointArchimedeanCellSelector_sameCertificate
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (p : Main3LargeAnalyticSquarefreeBlockPoint h v D Y N) :
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    let C := main3LargeAnalytic_blockFixedBasisEncodingCertificate
      htheta (main3LargeAnalytic_eight_le_of_ge_65536 hY) hi p
    InMain3LargeAnalyticArchimedeanCell
        (main3UnbalancedM theta Y) C.P
        (main3LargeAnalytic_blockPointArchimedeanCellSelector
          htheta hY hi p) ∧
      main3LargeAnalytic_blockCoordinateCode htheta
          (main3LargeAnalytic_eight_le_of_ge_65536 hY) hi p =
        C.encoded.code := by
  exact
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
        (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    by
      let C := main3LargeAnalytic_blockFixedBasisEncodingCertificate
        htheta (main3LargeAnalytic_eight_le_of_ge_65536 hY) hi p
      constructor
      · exact main3LargeAnalytic_blockPointArchimedeanCellSelector_spec
          htheta hY hi p
      · rfl

/-- The part of one fixed auxiliary-key point fibre assigned to a selected
archimedean cell. -/
noncomputable def main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (i : Main3LargeAnalyticArchimedeanCellIndex) :
    Finset (Main3LargeAnalyticSquarefreeBlockPoint h v D Y N) :=
  (main3LargeAnalytic_blockAuxiliaryPointFiber htheta
      (main3LargeAnalytic_eight_le_of_ge_65536 hY) hi key).filter fun p =>
    main3LargeAnalytic_blockPointArchimedeanCellSelector htheta hY hi p = i

@[simp]
theorem mem_main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber_iff
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    {key : ShiftedSquareAuxiliaryKey}
    {i : Main3LargeAnalyticArchimedeanCellIndex}
    {p : Main3LargeAnalyticSquarefreeBlockPoint h v D Y N} :
    p ∈ main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
        htheta hY hi key i ↔
      main3LargeAnalytic_blockAuxiliaryKey htheta
          (main3LargeAnalytic_eight_le_of_ge_65536 hY) hi p = key ∧
        main3LargeAnalytic_blockPointArchimedeanCellSelector
          htheta hY hi p = i := by
  simp [main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber,
    mem_main3LargeAnalytic_blockAuxiliaryPointFiber_iff]

/-- Membership exposes the fixed auxiliary key, the deterministic selected
cell, and the selected cell's geometry for the same package used by the
coordinate code. -/
theorem main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber_spec
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    {key : ShiftedSquareAuxiliaryKey}
    {i : Main3LargeAnalyticArchimedeanCellIndex}
    {p : Main3LargeAnalyticSquarefreeBlockPoint h v D Y N}
    (hp : p ∈ main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
      htheta hY hi key i) :
    main3LargeAnalytic_blockAuxiliaryKey htheta
        (main3LargeAnalytic_eight_le_of_ge_65536 hY) hi p = key ∧
      main3LargeAnalytic_blockPointArchimedeanCellSelector
          htheta hY hi p = i ∧
        Main3LargeAnalyticBlockPointInArchimedeanCell
          htheta hY hi p i := by
  have hmem :=
    (mem_main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber_iff
      htheta hY hi).mp hp
  refine ⟨hmem.1, hmem.2, ?_⟩
  simpa only [hmem.2] using
    main3LargeAnalytic_blockPointArchimedeanCellSelector_spec
      htheta hY hi p

/-- Distinct selected cells give disjoint subfibres of a fixed auxiliary-key
fibre. -/
theorem main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber_disjoint
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    {i j : Main3LargeAnalyticArchimedeanCellIndex} (hne : i ≠ j) :
    Disjoint
      (main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
        htheta hY hi key i)
      (main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
        htheta hY hi key j) := by
  classical
  apply Finset.disjoint_left.mpr
  intro p hpi hpj
  apply hne
  have hiEq :=
    (mem_main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber_iff
      htheta hY hi).mp hpi |>.2
  have hjEq :=
    (mem_main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber_iff
      htheta hY hi).mp hpj |>.2
  exact hiEq.symm.trans hjEq

/-- The selected cell subfibres cover one fixed auxiliary-key point fibre
exactly. -/
theorem main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFibers_cover
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey) :
    main3LargeAnalytic_blockAuxiliaryPointFiber htheta
        (main3LargeAnalytic_eight_le_of_ge_65536 hY) hi key =
      (main3LargeAnalytic_archimedeanCellIndices
          (shiftedSquareA h v) (main3UnbalancedM theta Y)).biUnion fun i =>
        main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
          htheta hY hi key i := by
  classical
  ext p
  constructor
  · intro hp
    apply Finset.mem_biUnion.mpr
    refine ⟨main3LargeAnalytic_blockPointArchimedeanCellSelector
      htheta hY hi p, ?_, ?_⟩
    · exact main3LargeAnalytic_blockPointArchimedeanCellSelector_mem
        htheta hY hi p
    · exact Finset.mem_filter.mpr ⟨hp, rfl⟩
  · intro hp
    obtain ⟨i, _hiIndex, hpCell⟩ := Finset.mem_biUnion.mp hp
    exact (Finset.mem_filter.mp hpCell).1

/-- Exact fibrewise cardinal decomposition.  This is a partition identity,
not an estimate for any summand. -/
theorem card_main3LargeAnalytic_blockAuxiliaryPointFiber_eq_sum_archimedeanCells
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey) :
    (main3LargeAnalytic_blockAuxiliaryPointFiber htheta
        (main3LargeAnalytic_eight_le_of_ge_65536 hY) hi key).card =
      ∑ i ∈ main3LargeAnalytic_archimedeanCellIndices
          (shiftedSquareA h v) (main3UnbalancedM theta Y),
        (main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
          htheta hY hi key i).card := by
  classical
  have hmap :
      (main3LargeAnalytic_blockAuxiliaryPointFiber htheta
          (main3LargeAnalytic_eight_le_of_ge_65536 hY) hi key :
        Set (Main3LargeAnalyticSquarefreeBlockPoint h v D Y N)).MapsTo
          (main3LargeAnalytic_blockPointArchimedeanCellSelector
            htheta hY hi)
          (main3LargeAnalytic_archimedeanCellIndices
            (shiftedSquareA h v) (main3UnbalancedM theta Y)) := by
    intro p _hp
    exact main3LargeAnalytic_blockPointArchimedeanCellSelector_mem
      htheta hY hi p
  simpa only
    [main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber] using
      Finset.card_eq_sum_card_fiberwise hmap

end

end PellPaper
