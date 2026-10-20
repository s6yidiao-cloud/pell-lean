import Pell.Main3LargeAnalyticFixedKeyCellArithmetic
import Pell.BinaryLinearSubstitutionNatHeight
import Mathlib.Tactic

/-!
# Substitution height of the intrinsic main3 eliminant

For one fixed auxiliary key and archimedean cell, the selected residual
two-layer form and the fixed quadratic-linear surface determine a literal
odd-degree homogeneous target eliminant.  This module packages a positive
natural coefficient height for that eliminant and, after an arbitrary
integral two-by-two substitution with a supplied entry bound, the exact
positive natural height consumed by the intrinsic square sieve.

No target-lattice geometry, matrix-entry estimate, logarithmic budget, or
character-sum input is asserted here.
-/

namespace PellPaper

noncomputable section

/-- The literal residual eliminant attached to one fixed main3 key/cell
factorization. -/
def main3LargeAnalyticIntrinsicEliminant
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N B : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (data : Main3LargeAnalyticFixedKeyCellAuxiliaryFactorData
      htheta hY hi key cell B) : MvPolynomial (Fin 2) ℤ :=
  twoLayerEliminant data.residualDegree data.residualForm
    (main3LargeAnalytic_blockCoordinateSurfaceCoefficients hi)
    (shiftedSquareAuxiliaryKeySurfaceLevel key)

/-- The odd homogeneous degree of the literal residual eliminant. -/
def main3LargeAnalyticIntrinsicEliminantDegree
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N B : ℕ}
    {htheta : 3 ≤ theta} {hY : 65536 ≤ Y}
    {hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y}
    {key : ShiftedSquareAuxiliaryKey}
    {cell : Main3LargeAnalyticArchimedeanCellIndex}
    (data : Main3LargeAnalyticFixedKeyCellAuxiliaryFactorData
      htheta hY hi key cell B) : ℕ :=
  2 * data.residualDegree + 1

/-- A positive natural coefficient height for the literal eliminant before
the target-coordinate substitution.  The positive ceiling absorbs the real
height in the auxiliary-factor package; the other factors are the exact
six-term eliminant cost, surface level, and fixed surface coefficient bound. -/
def main3LargeAnalyticIntrinsicEliminantRawHeight
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N B : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (data : Main3LargeAnalyticFixedKeyCellAuxiliaryFactorData
      htheta hY hi key cell B) : ℕ :=
  6 * (data.residualDegree + 1) *
    (shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs *
    (positiveNatCeil
      (main3LargeAnalyticFixedKeyFactorHeight B data.rank
        (shiftedSquareA h v) D Y key)) ^ 2 *
    (8 * (shiftedSquareA h v).natAbs + 4)

/-- The positive natural height after substituting a two-by-two integral
matrix whose real entry height is bounded by `L`. -/
def main3LargeAnalyticIntrinsicEliminantSubstitutionHeight
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N B : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (data : Main3LargeAnalyticFixedKeyCellAuxiliaryFactorData
      htheta hY hi key cell B) (L : ℝ) : ℕ :=
  binaryLinearSubstitutionNatHeight
    (main3LargeAnalyticIntrinsicEliminantDegree data)
    (main3LargeAnalyticIntrinsicEliminantRawHeight
      htheta hY hi key cell data : ℝ) L

/-- The literal residual eliminant is homogeneous of its displayed odd
degree, including in the degenerate case in which the polynomial is zero. -/
theorem main3LargeAnalyticIntrinsicEliminant_isHomogeneous
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N B : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (data : Main3LargeAnalyticFixedKeyCellAuxiliaryFactorData
      htheta hY hi key cell B) :
    (main3LargeAnalyticIntrinsicEliminant
      htheta hY hi key cell data).IsHomogeneous
        (main3LargeAnalyticIntrinsicEliminantDegree data) := by
  exact twoLayerEliminant_isHomogeneous data.residualDegree data.residualForm
    (main3LargeAnalytic_blockCoordinateSurfaceCoefficients hi)
    (shiftedSquareAuxiliaryKeySurfaceLevel key)

/-- The displayed eliminant degree is odd. -/
theorem main3LargeAnalyticIntrinsicEliminantDegree_odd
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N B : ℕ}
    {htheta : 3 ≤ theta} {hY : 65536 ≤ Y}
    {hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y}
    {key : ShiftedSquareAuxiliaryKey}
    {cell : Main3LargeAnalyticArchimedeanCellIndex}
    (data : Main3LargeAnalyticFixedKeyCellAuxiliaryFactorData
      htheta hY hi key cell B) :
    Odd (main3LargeAnalyticIntrinsicEliminantDegree data) := by
  exact ⟨data.residualDegree, rfl⟩

/-- The pre-substitution natural height is positive. -/
theorem main3LargeAnalyticIntrinsicEliminantRawHeight_pos
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N B : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (data : Main3LargeAnalyticFixedKeyCellAuxiliaryFactorData
      htheta hY hi key cell B) :
    0 < main3LargeAnalyticIntrinsicEliminantRawHeight
      htheta hY hi key cell data := by
  have hlevel : 0 < (shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs :=
    Int.natAbs_pos.mpr data.surfaceLevel_ne_zero
  unfold main3LargeAnalyticIntrinsicEliminantRawHeight
  apply Nat.mul_pos
  · apply Nat.mul_pos
    · apply Nat.mul_pos
      · exact Nat.mul_pos (by norm_num) (Nat.succ_pos _)
      · exact hlevel
    · exact pow_pos (positiveNatCeil_pos _) _
  · omega

/-- Every coefficient of the literal eliminant is bounded by the packaged
pre-substitution natural height. -/
theorem abs_coeff_main3LargeAnalyticIntrinsicEliminant_le_rawHeight
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N B : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (data : Main3LargeAnalyticFixedKeyCellAuxiliaryFactorData
      htheta hY hi key cell B) (e : Fin 2 →₀ ℕ) :
    |(main3LargeAnalyticIntrinsicEliminant
      htheta hY hi key cell data).coeff e| ≤
      (main3LargeAnalyticIntrinsicEliminantRawHeight
        htheta hY hi key cell data : ℤ) := by
  let H : ℝ := main3LargeAnalyticFixedKeyFactorHeight B data.rank
    (shiftedSquareA h v) D Y key
  let HF : ℕ := positiveNatCeil H
  let HG : ℕ := 8 * (shiftedSquareA h v).natAbs + 4
  have hf : ∀ ab, |data.residualForm ab| ≤ (HF : ℤ) := by
    intro ab
    have hab : |((data.residualForm ab : ℤ) : ℝ)| ≤ (HF : ℝ) :=
      (data.residualForm_coeff_bound ab).trans (le_positiveNatCeil H)
    exact_mod_cast hab
  have hg : ∀ i j,
      |main3LargeAnalytic_blockCoordinateSurfaceCoefficients hi i j| ≤
        (HG : ℤ) := by
    intro i j
    simpa only [HG] using
      main3LargeAnalytic_blockCoordinateSurfaceCoefficients_abs_le hi i j
  have hcoeff := abs_coeff_twoLayerEliminant_le data.residualDegree
    data.residualForm (main3LargeAnalytic_blockCoordinateSurfaceCoefficients hi)
    (shiftedSquareAuxiliaryKeySurfaceLevel key) (HF : ℤ) (HG : ℤ)
    (by positivity) (by positivity) hf hg e
  simpa only [main3LargeAnalyticIntrinsicEliminant,
    main3LargeAnalyticIntrinsicEliminantRawHeight, H, HF, HG,
    Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat,
    Nat.cast_one, Int.natCast_natAbs] using hcoeff

/-- The post-substitution natural height is positive for every real entry
bound, including vacuous negative bounds. -/
theorem main3LargeAnalyticIntrinsicEliminantSubstitutionHeight_pos
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N B : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (data : Main3LargeAnalyticFixedKeyCellAuxiliaryFactorData
      htheta hY hi key cell B) (L : ℝ) :
    0 < main3LargeAnalyticIntrinsicEliminantSubstitutionHeight
      htheta hY hi key cell data L := by
  exact binaryLinearSubstitutionNatHeight_pos
    (main3LargeAnalyticIntrinsicEliminantDegree data)
    (main3LargeAnalyticIntrinsicEliminantRawHeight
      htheta hY hi key cell data : ℝ) L

/-- A supplied real entry bound for an arbitrary integral matrix gives the
exact transformed coefficient inequality required by the intrinsic square
sieve.  No determinant or lattice-geometric property of `W` is used. -/
theorem abs_coeff_binaryLinearSubstitution_main3LargeAnalyticIntrinsicEliminant_le
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N B : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (data : Main3LargeAnalyticFixedKeyCellAuxiliaryFactorData
      htheta hY hi key cell B)
    (W : Matrix (Fin 2) (Fin 2) ℤ) (L : ℝ)
    (hW : ∀ i j, |((W i j : ℤ) : ℝ)| ≤ L)
    (e : Fin 2 →₀ ℕ) :
    |(binaryLinearSubstitution W
      (main3LargeAnalyticIntrinsicEliminant
        htheta hY hi key cell data)).coeff e| ≤
      (main3LargeAnalyticIntrinsicEliminantSubstitutionHeight
        htheta hY hi key cell data L : ℤ) := by
  apply abs_coeff_binaryLinearSubstitution_le_natHeight W
    (main3LargeAnalyticIntrinsicEliminant htheta hY hi key cell data)
    (main3LargeAnalyticIntrinsicEliminantDegree data)
    (main3LargeAnalyticIntrinsicEliminantRawHeight
      htheta hY hi key cell data : ℝ) L
    (main3LargeAnalyticIntrinsicEliminant_isHomogeneous
      htheta hY hi key cell data)
  · intro f
    have hf := abs_coeff_main3LargeAnalyticIntrinsicEliminant_le_rawHeight
      htheta hY hi key cell data f
    exact_mod_cast hf
  · exact hW

end

end PellPaper
