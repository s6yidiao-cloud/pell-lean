import Pell.Main3LargeAnalyticFixedKeyCellCoordinateBounds
import Pell.GeneralBidegreeOneSpecialization
import Pell.ShiftedSquareCoordinateSurfaceAdapter
import Mathlib.Tactic

/-!
# Bounded auxiliary-factor data and the exact fixed-cell arithmetic split

The bounded common integral auxiliary form on a literal fixed-key and
archimedean-cell image is factored into its homogeneous common target factor
and a primitive-target residual pair.  The original point image is converted
cardinality-preservingly to the generic vector convention, every target is
placed in one explicit symmetric integer rectangle, and the exact surface
projection theorem splits the image into the common-factor-zero branch and
twice the nonzero residual-eliminant square branch.

No estimate for either retained branch is asserted here.
-/

namespace PellPaper

noncomputable section

def main3LargeAnalyticFixedKeyAuxiliaryHeight
    (B r : ℕ) (a : ℤ) (D Y : ℕ) (key : ShiftedSquareAuxiliaryKey) : ℝ :=
  (Real.sqrt (r : ℝ) *
      (((main3LargeAnalyticFixedKeySourceCoordinateBound a D key) *
        (main3LargeAnalyticFixedKeyTargetCoordinateBound a Y key) ^ B : ℤ) : ℝ)) ^ r

def main3LargeAnalyticFixedKeyFactorHeight
    (B r : ℕ) (a : ℤ) (D Y : ℕ) (key : ShiftedSquareAuxiliaryKey) : ℝ :=
  (2 : ℝ) ^ B * ((B : ℝ) + 1) *
    main3LargeAnalyticFixedKeyAuxiliaryHeight B r a D Y key

theorem main3LargeAnalyticFixedKeyAuxiliaryHeight_nonneg
    (B r : ℕ) (a : ℤ) (D Y : ℕ) (key : ShiftedSquareAuxiliaryKey) :
    0 ≤ main3LargeAnalyticFixedKeyAuxiliaryHeight B r a D Y key := by
  have hs : 0 ≤ main3LargeAnalyticFixedKeySourceCoordinateBound a D key :=
    main3LargeAnalyticFixedKeySourceCoordinateBound_nonneg a D key
  have ht : 0 ≤ main3LargeAnalyticFixedKeyTargetCoordinateBound a Y key :=
    main3LargeAnalyticFixedKeyTargetCoordinateBound_nonneg a Y key
  have hp : 0 ≤ (main3LargeAnalyticFixedKeyTargetCoordinateBound a Y key) ^ B :=
    pow_nonneg ht B
  have hsp : 0 ≤ (main3LargeAnalyticFixedKeySourceCoordinateBound a D key) *
      (main3LargeAnalyticFixedKeyTargetCoordinateBound a Y key) ^ B :=
    mul_nonneg hs hp
  have hcast : 0 ≤
      (((main3LargeAnalyticFixedKeySourceCoordinateBound a D key) *
        (main3LargeAnalyticFixedKeyTargetCoordinateBound a Y key) ^ B : ℤ) : ℝ) := by
    exact_mod_cast hsp
  unfold main3LargeAnalyticFixedKeyAuxiliaryHeight
  exact pow_nonneg (mul_nonneg (Real.sqrt_nonneg _) hcast) r

theorem main3LargeAnalyticFixedKeyFactorHeight_nonneg
    (B r : ℕ) (a : ℤ) (D Y : ℕ) (key : ShiftedSquareAuxiliaryKey) :
    0 ≤ main3LargeAnalyticFixedKeyFactorHeight B r a D Y key := by
  unfold main3LargeAnalyticFixedKeyFactorHeight
  exact mul_nonneg
    (mul_nonneg (by positivity) (by positivity))
    (main3LargeAnalyticFixedKeyAuxiliaryHeight_nonneg B r a D Y key)

/-- The literal pair/vector equivalence used by the surface-projection API. -/
def main3GeneralBidegreePointVectorEquiv :
    GeneralBidegreeFormPoint ≃ ((Fin 2 → ℤ) × (Fin 2 → ℤ)) :=
  Equiv.prodCongr (finTwoArrowEquiv ℤ).symm (finTwoArrowEquiv ℤ).symm

@[simp]
theorem main3GeneralBidegreePointVectorEquiv_apply
    (z : GeneralBidegreeFormPoint) :
    main3GeneralBidegreePointVectorEquiv z =
      (shiftedSquareCoordinatePointSourceVector z,
        shiftedSquareCoordinatePointTargetVector z) := by
  rcases z with ⟨⟨x0, x1⟩, ⟨y0, y1⟩⟩
  rfl

def main3LargeAnalyticFixedKeyCellVectorImage
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex) :
    Finset ((Fin 2 → ℤ) × (Fin 2 → ℤ)) :=
  (main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
    htheta hY hi key cell).map
      main3GeneralBidegreePointVectorEquiv.toEmbedding

@[simp]
theorem card_main3LargeAnalyticFixedKeyCellVectorImage
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex) :
    (main3LargeAnalyticFixedKeyCellVectorImage htheta hY hi key cell).card =
      (main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
        htheta hY hi key cell).card := by
  exact Finset.card_map _

def main3LargeAnalyticFixedKeyTargetRectangle
    (a : ℤ) (Y : ℕ) (key : ShiftedSquareAuxiliaryKey) :
    Finset (Fin 2 → ℤ) :=
  integerSymmetricRectangle
    (main3LargeAnalyticFixedKeyTargetCoordinateRadius a Y key)
    (main3LargeAnalyticFixedKeyTargetCoordinateRadius a Y key)

theorem main3LargeAnalytic_fixedKeyCell_targetVector_mem_rectangle
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    {key : ShiftedSquareAuxiliaryKey}
    {cell : Main3LargeAnalyticArchimedeanCellIndex}
    {z : GeneralBidegreeFormPoint}
    (hz : z ∈
      main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
        htheta hY hi key cell) :
    shiftedSquareCoordinatePointTargetVector z ∈
      main3LargeAnalyticFixedKeyTargetRectangle
        (shiftedSquareA h v) Y key := by
  rw [main3LargeAnalyticFixedKeyTargetRectangle,
    mem_integerSymmetricRectangle]
  exact (main3LargeAnalytic_fixedKeyCellCoordinatePointImage_abs_bounds
    htheta hY hi hz).2

structure Main3LargeAnalyticFixedKeyCellAuxiliaryFactorData
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (B : ℕ) where
  rank : ℕ
  rank_lt : rank < 2 * (B + 1)
  form : twoLayerFormIndex B → ℤ
  form_ne_zero : form ≠ 0
  form_vanish : ∀ z ∈
    main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
      htheta hY hi key cell,
    twoLayerFormEval B form z = 0
  form_coeff_bound : ∀ j, (|form j| : ℝ) ≤
    main3LargeAnalyticFixedKeyAuxiliaryHeight B rank
      (shiftedSquareA h v) D Y key
  factorDegree : ℕ
  residualDegree : ℕ
  degree_split : factorDegree + residualDegree = B
  targetFactor : MvPolynomial (Fin 2) ℤ
  targetFactor_ne_zero : targetFactor ≠ 0
  targetFactor_homogeneous : targetFactor.IsHomogeneous factorDegree
  residualForm : twoLayerFormIndex residualDegree → ℤ
  residualForm_ne_zero : residualForm ≠ 0
  factorization : ∀ i : Fin 2, twoLayerBinaryPolynomial B form i =
    targetFactor * twoLayerBinaryPolynomial residualDegree residualForm i
  targetFactor_coeff_bound : ∀ e,
    |((targetFactor.coeff e : ℤ) : ℝ)| ≤
      main3LargeAnalyticFixedKeyFactorHeight B rank
        (shiftedSquareA h v) D Y key
  residualForm_coeff_bound : ∀ ab,
    |((residualForm ab : ℤ) : ℝ)| ≤
      main3LargeAnalyticFixedKeyFactorHeight B rank
        (shiftedSquareA h v) D Y key
  residual_components_nonvanishing :
    ∀ y : Fin 2 → ℤ, IsCoprime (y 0) (y 1) →
      MvPolynomial.eval y
          (twoLayerBinaryPolynomial residualDegree residualForm 0) ≠ 0 ∨
        MvPolynomial.eval y
          (twoLayerBinaryPolynomial residualDegree residualForm 1) ≠ 0
  surfaceLevel_ne_zero : shiftedSquareAuxiliaryKeySurfaceLevel key ≠ 0

theorem exists_main3LargeAnalyticFixedKeyCellAuxiliaryFactorData
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N B : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (hnonempty :
      (main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
        htheta hY hi key cell).Nonempty)
    (hminor : ∀ s : generalBidegreeFormIndex 1 B ↪
        {z // z ∈
          main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
            htheta hY hi key cell},
      ((generalBidegreeFormEvaluationMatrix 1 B
        (fun z : {z // z ∈
          main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
            htheta hY hi key cell} => z.1)).submatrix s id).det = 0) :
    Nonempty (Main3LargeAnalyticFixedKeyCellAuxiliaryFactorData
      htheta hY hi key cell B) := by
  obtain ⟨r, hr, f, hf0, hfvanish, hfbound⟩ :=
    exists_nonzero_bounded_integral_twoLayerForm_on_main3LargeAnalytic_fixedKeyCellImage
      htheta hY hi key cell hminor
  let H := main3LargeAnalyticFixedKeyAuxiliaryHeight B r
    (shiftedSquareA h v) D Y key
  have hH : 0 ≤ H :=
    main3LargeAnalyticFixedKeyAuxiliaryHeight_nonneg B r
      (shiftedSquareA h v) D Y key
  have hfbound' : ∀ ab, |((f ab : ℤ) : ℝ)| ≤ H := by
    intro ab
    simpa only [H, main3LargeAnalyticFixedKeyAuxiliaryHeight] using hfbound ab
  obtain ⟨d, b, D0, f', hdb, hD0, hDhom, hf'0, hfactor,
      hDbound, hf'bound, hcomponents, _heval⟩ :=
    exists_bounded_twoLayer_common_factor B f hf0 H hH hfbound'
  obtain ⟨z0, hz0⟩ := hnonempty
  have hc := (main3LargeAnalytic_blockCellCoordinatePointImage_surfaceData
    htheta hY hi hz0).2
  refine ⟨{
    rank := r
    rank_lt := hr
    form := f
    form_ne_zero := hf0
    form_vanish := hfvanish
    form_coeff_bound := ?_
    factorDegree := d
    residualDegree := b
    degree_split := hdb
    targetFactor := D0
    targetFactor_ne_zero := hD0
    targetFactor_homogeneous := hDhom
    residualForm := f'
    residualForm_ne_zero := hf'0
    factorization := hfactor
    targetFactor_coeff_bound := ?_
    residualForm_coeff_bound := ?_
    residual_components_nonvanishing := hcomponents
    surfaceLevel_ne_zero := hc
  }⟩
  · intro j
    exact hfbound j
  · intro e
    simpa only [main3LargeAnalyticFixedKeyFactorHeight, H] using hDbound e
  · intro ab
    simpa only [main3LargeAnalyticFixedKeyFactorHeight, H] using hf'bound ab

theorem card_main3LargeAnalytic_fixedKeyCellImage_le_factorZeros_add_residualSquares
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N B : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (data : Main3LargeAnalyticFixedKeyCellAuxiliaryFactorData
      htheta hY hi key cell B) :
    (main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
        htheta hY hi key cell).card ≤
      ((main3LargeAnalyticFixedKeyCellVectorImage htheta hY hi key cell).filter
        fun p => MvPolynomial.eval p.2 data.targetFactor = 0).card +
      2 * ((main3LargeAnalyticFixedKeyTargetRectangle
        (shiftedSquareA h v) Y key).filter fun y =>
          IsSquare (MvPolynomial.eval y
            (twoLayerEliminant data.residualDegree data.residualForm
              (main3LargeAnalytic_blockCoordinateSurfaceCoefficients hi)
              (shiftedSquareAuxiliaryKeySurfaceLevel key))) ∧
          MvPolynomial.eval y
            (twoLayerEliminant data.residualDegree data.residualForm
              (main3LargeAnalytic_blockCoordinateSurfaceCoefficients hi)
              (shiftedSquareAuxiliaryKeySurfaceLevel key)) ≠ 0).card := by
  rw [← card_main3LargeAnalyticFixedKeyCellVectorImage htheta hY hi key cell]
  apply card_shiftedSquareCoordinateSurface_le_targetFactorZeros_add_twiceSquares
    B data.residualDegree data.form data.residualForm data.targetFactor
    data.factorization data.residual_components_nonvanishing
    (main3LargeAnalytic_blockCoordinateSurfaceCoefficients hi)
    (shiftedSquareAuxiliaryKeySurfaceLevel key) data.surfaceLevel_ne_zero
    (main3LargeAnalyticFixedKeyCellVectorImage htheta hY hi key cell)
    (main3LargeAnalyticFixedKeyTargetRectangle (shiftedSquareA h v) Y key)
  · intro p hp
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hp
    exact (main3LargeAnalytic_blockCellCoordinatePointImage_primitive
      htheta hY hi hz).1
  · intro p hp
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hp
    exact (main3LargeAnalytic_blockCellCoordinatePointImage_primitive
      htheta hY hi hz).2
  · intro p hp
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hp
    have heq : main3GeneralBidegreePointVectorEquiv.toEmbedding z =
        (shiftedSquareCoordinatePointSourceVector z,
          shiftedSquareCoordinatePointTargetVector z) :=
      main3GeneralBidegreePointVectorEquiv_apply z
    rw [heq]
    simpa only [
      shiftedSquareCoordinatePoint,
      shiftedSquareCoordinatePointSourceVector,
      shiftedSquareCoordinatePointTargetVector,
      Matrix.cons_val_zero, Matrix.cons_val_one] using data.form_vanish z hz
  · intro p hp
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hp
    exact (main3LargeAnalytic_blockCellCoordinatePointImage_surfaceData
      htheta hY hi hz).1
  · intro p hp
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hp
    exact main3LargeAnalytic_fixedKeyCell_targetVector_mem_rectangle
      htheta hY hi hz

end

end PellPaper
