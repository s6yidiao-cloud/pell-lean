import Pell.Main3LargeAnalyticCommonFactorFiberReduction
import Pell.Main3LargeAnalyticTargetFibreThetaCount
import Mathlib.Tactic

/-!
# Real-valued common-factor target-fibre aggregation

The existing exact common-factor reduction is stated for a natural-number
uniform fibre bound.  The literal main3 unit-orbit estimate is naturally a
real inequality, since its bound contains `theta`.  This module performs the
same finite fibre sum after casting cardinalities to `ℝ`, avoiding a ceiling
and its artificial additive loss.
-/

namespace PellPaper

noncomputable section

/-- If every exact target fibre has real cardinality at most `sourceFibreBound`,
then the common-factor-zero branch has real cardinality at most twice the
factor degree times that bound. -/
theorem card_main3LargeAnalytic_commonFactorZero_cast_le_two_mul_factorDegree_mul_of_targetFibre_cast_bound
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N B : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (data : Main3LargeAnalyticFixedKeyCellAuxiliaryFactorData
      htheta hY hi key cell B)
    (sourceFibreBound : ℝ) (hsourceFibreBound : 0 ≤ sourceFibreBound)
    (hsourceFibre : ∀ y ∈
      main3LargeAnalyticFixedKeyTargetRectangle (shiftedSquareA h v) Y key,
      ((main3LargeAnalyticFixedKeyCellTargetFibre
        htheta hY hi key cell y).card : ℝ) ≤ sourceFibreBound) :
    (((main3LargeAnalyticFixedKeyCellVectorImage htheta hY hi key cell).filter
        fun p => MvPolynomial.eval p.2 data.targetFactor = 0).card : ℝ) ≤
      ((2 * data.factorDegree : ℕ) : ℝ) * sourceFibreBound := by
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
      ((S.filter fun p => p.2 = y).card : ℝ) ≤ sourceFibreBound := by
    intro y hy
    have hyT : y ∈ T := hST hy
    have hsub : (S.filter fun p => p.2 = y) ⊆
        main3LargeAnalyticFixedKeyCellTargetFibre
          htheta hY hi key cell y := by
      intro p hp
      obtain ⟨hpS, hpy⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hpS).1, hpy⟩
    have hcard : (S.filter fun p => p.2 = y).card ≤
        (main3LargeAnalyticFixedKeyCellTargetFibre
          htheta hY hi key cell y).card := Finset.card_le_card hsub
    have hcardReal : ((S.filter fun p => p.2 = y).card : ℝ) ≤
        ((main3LargeAnalyticFixedKeyCellTargetFibre
          htheta hY hi key cell y).card : ℝ) := by
      exact_mod_cast hcard
    exact hcardReal.trans
      (hsourceFibre y (Finset.mem_filter.mp hyT).1)
  calc
    (((main3LargeAnalyticFixedKeyCellVectorImage htheta hY hi key cell).filter
        fun p => MvPolynomial.eval p.2 data.targetFactor = 0).card : ℝ) =
        (S.card : ℝ) := by rfl
    _ = ∑ y ∈ S.image Prod.snd,
        ((S.filter fun p => p.2 = y).card : ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_image Prod.snd S
    _ ≤ ∑ _y ∈ S.image Prod.snd, sourceFibreBound :=
      Finset.sum_le_sum hfibre
    _ = ((S.image Prod.snd).card : ℝ) * sourceFibreBound := by simp
    _ ≤ (T.card : ℝ) * sourceFibreBound := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card hST)
        hsourceFibreBound
    _ ≤ ((2 * data.factorDegree : ℕ) : ℝ) * sourceFibreBound := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hTcard)
        hsourceFibreBound

/-- The literal target-fibre theta bound closes the common-factor-zero branch
with the manuscript's factor-degree loss.  The displayed degree budget `B`
comes directly from the exact factorization data. -/
theorem card_main3LargeAnalytic_commonFactorZero_cast_le_2048_mul_degreeBudget_mul_theta_mul_key_divisors
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N B : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (data : Main3LargeAnalyticFixedKeyCellAuxiliaryFactorData
      htheta hY hi key cell B) :
    (((main3LargeAnalyticFixedKeyCellVectorImage htheta hY hi key cell).filter
        fun p => MvPolynomial.eval p.2 data.targetFactor = 0).card : ℝ) ≤
      2048 * (B : ℝ) * theta *
        ((shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs.divisors.card : ℝ) := by
  let sourceFibreBound : ℝ :=
    1024 * theta *
      ((shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs.divisors.card : ℝ)
  have hsourceFibreBound : 0 ≤ sourceFibreBound := by
    dsimp only [sourceFibreBound]
    positivity
  have hsourceFibre : ∀ y ∈
      main3LargeAnalyticFixedKeyTargetRectangle (shiftedSquareA h v) Y key,
      ((main3LargeAnalyticFixedKeyCellTargetFibre
        htheta hY hi key cell y).card : ℝ) ≤ sourceFibreBound := by
    intro y _hy
    dsimp only [sourceFibreBound]
    exact
      card_main3LargeAnalyticFixedKeyCellTargetFibre_le_1024_mul_theta_mul_key_divisors
        htheta hY hi key cell y
  have hcommon :=
    card_main3LargeAnalytic_commonFactorZero_cast_le_two_mul_factorDegree_mul_of_targetFibre_cast_bound
      htheta hY hi key cell data sourceFibreBound hsourceFibreBound hsourceFibre
  have hdegree : data.factorDegree ≤ B := by
    have hsplit := data.degree_split
    omega
  have hdegreeReal : ((2 * data.factorDegree : ℕ) : ℝ) ≤ 2 * (B : ℝ) := by
    exact_mod_cast Nat.mul_le_mul_left 2 hdegree
  calc
    (((main3LargeAnalyticFixedKeyCellVectorImage htheta hY hi key cell).filter
        fun p => MvPolynomial.eval p.2 data.targetFactor = 0).card : ℝ) ≤
        ((2 * data.factorDegree : ℕ) : ℝ) * sourceFibreBound := hcommon
    _ ≤ (2 * (B : ℝ)) * sourceFibreBound :=
      mul_le_mul_of_nonneg_right hdegreeReal hsourceFibreBound
    _ = 2048 * (B : ℝ) * theta *
        ((shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs.divisors.card : ℝ) := by
      dsimp only [sourceFibreBound]
      ring

end

end PellPaper
