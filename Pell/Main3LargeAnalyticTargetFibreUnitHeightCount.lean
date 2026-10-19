import Pell.Main3LargeAnalyticTargetFibreIdealPartition
import Pell.Main3LargeAnalyticFixedKeyCellCoordinateBounds
import Pell.QuadraticFormRepresentationRealHeightWindow
import Pell.QuadraticFormRepresentationUnitHeightCount
import Pell.SquarefreeQuadraticFundamentalUnitTransport
import Pell.SquarefreeQuadraticPositiveEmbeddingTransport

/-!
# Literal one-ideal height count in a main3 target fibre

This file specializes the generic quadratic-form unit-orbit count to the
actual source-pair image of one fixed key, archimedean cell, and target.  The
literal source-coordinate radius supplies an explicit reciprocal real-height
window after passage from the square-multiple discriminant to its oriented
fundamental presentation.

The resulting bound keeps the exact logarithmic quotient.  In particular it
does not yet use the regulator lower bound or simplify the result to an
`O(theta)` estimate.
-/

namespace PellPaper

open NumberField

noncomputable section

/-- The source pairs in one literal target fibre that map to one fixed
quotient ideal. -/
noncomputable def main3LargeAnalyticTargetFibreSourcePairsInQuotientIdeal
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (y : Fin 2 → ℤ) (w s : ℕ)
    (hdisc :
      (main3LargeAnalyticFixedTargetPrimitiveSurfaceForm hi y).discriminant =
        ((w * s ^ 2 : ℕ) : ℤ))
    [Fact (rationalQuadraticAlgebraNoRationalRoot
      ((w * s ^ 2 : ℕ) : ℤ))]
    (J : Ideal (NumberField.RingOfIntegers
      (rationalQuadraticAlgebra ((w * s ^ 2 : ℕ) : ℤ)))) :
    Finset (ℤ × ℤ) :=
  (main3LargeAnalyticFixedKeyCellTargetFibreSourcePairs
    htheta hY hi key cell y).filter fun z =>
      IntegralBinaryQuadraticForm.formRepresentationQuotientIdeal
        ((w * s ^ 2 : ℕ) : ℤ)
        (main3LargeAnalyticFixedTargetPrimitiveSurfaceForm hi y)
        hdisc z.1 z.2 = J

/-- Every projected source pair lies in the same literal source-coordinate
box as the fixed key-and-cell coordinate image from which it was obtained. -/
theorem main3LargeAnalytic_targetFibreSourcePair_abs_bounds
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (y : Fin 2 → ℤ) {z : ℤ × ℤ}
    (hz : z ∈ main3LargeAnalyticFixedKeyCellTargetFibreSourcePairs
      htheta hY hi key cell y) :
    |(z.1 : ℝ)| ≤
        main3LargeAnalyticFixedKeySourceCoordinateRadius
          (shiftedSquareA h v) D key ∧
      |(z.2 : ℝ)| ≤
        main3LargeAnalyticFixedKeySourceCoordinateRadius
          (shiftedSquareA h v) D key := by
  classical
  rw [main3LargeAnalyticFixedKeyCellTargetFibreSourcePairs] at hz
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
  have hpImage :=
    (mem_main3LargeAnalyticFixedKeyCellTargetFibre
      htheta hY hi key cell y p).mp hp |>.1
  rw [main3LargeAnalyticFixedKeyCellVectorImage] at hpImage
  obtain ⟨q, hq, hqp⟩ := Finset.mem_map.mp hpImage
  have hbounds :=
    main3LargeAnalytic_fixedKeyCellCoordinatePointImage_abs_bounds
      htheta hY hi hq
  change main3GeneralBidegreePointVectorEquiv q = p at hqp
  rw [main3GeneralBidegreePointVectorEquiv_apply] at hqp
  subst p
  simpa [shiftedSquareCoordinatePointSourceVector] using hbounds.1

/-- Inside one fixed quotient ideal, the actual main3 source pairs satisfy
the exact logarithmic signed-unit count obtained from their literal coordinate
radius.  This is the unsimplified height-count endpoint: no regulator lower
bound or `O(theta)` estimate has yet been applied. -/
theorem card_main3LargeAnalyticTargetFibreSourcePairsInQuotientIdeal_le_log_height
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (y : Fin 2 → ℤ)
    (p₀ : Main3LargeAnalyticFixedKeyCellTargetFibrePoint
      htheta hY hi key cell y)
    (w s : ℕ) (hw : Squarefree w) (hwone : 1 < w) (hs : 0 < s)
    (hdisc :
      (main3LargeAnalyticFixedTargetPrimitiveSurfaceForm hi y).discriminant =
        ((w * s ^ 2 : ℕ) : ℤ))
    [Fact (rationalQuadraticAlgebraNoRationalRoot
      ((w * s ^ 2 : ℕ) : ℤ))]
    [Fact (rationalQuadraticAlgebraNoRationalRoot
      ((squarefreeQuadraticFundamentalIndex w : ℕ) : ℤ))]
    (J : Ideal (NumberField.RingOfIntegers
      (rationalQuadraticAlgebra ((w * s ^ 2 : ℕ) : ℤ)))) :
    let Q := main3LargeAnalyticFixedTargetPrimitiveSurfaceForm hi y
    let g := main3LargeAnalyticFixedTargetSurfaceContent hi y
    let m₀ := shiftedSquareAuxiliaryKeySurfaceLevel key / (g : ℤ)
    let X := main3LargeAnalyticFixedKeySourceCoordinateRadius
      (shiftedSquareA h v) D key
    let H := IntegralBinaryQuadraticForm.formIdealVectorRealHeightMajorant
      ((w * s ^ 2 : ℕ) : ℤ) Q X
    let L := |(Q.a : ℝ) * (m₀ : ℝ)| / H
    let Dfund := squarefreeQuadraticFundamentalIndex w
    let hDfund : PositiveFundamentalDiscriminant Dfund :=
      squarefreeQuadraticFundamentalIndex_positiveFundamentalDiscriminant
        w hw hwone
    ((main3LargeAnalyticTargetFibreSourcePairsInQuotientIdeal
        htheta hY hi key cell y w s hdisc J).card : ℝ) ≤
      2 * (1 + Real.log (H / L) /
        Real.log (concreteFundamentalUnitRealModel Dfund hDfund).eta) := by
  let Q := main3LargeAnalyticFixedTargetPrimitiveSurfaceForm hi y
  let g := main3LargeAnalyticFixedTargetSurfaceContent hi y
  let m₀ := shiftedSquareAuxiliaryKeySurfaceLevel key / (g : ℤ)
  let X := main3LargeAnalyticFixedKeySourceCoordinateRadius
    (shiftedSquareA h v) D key
  let H := IntegralBinaryQuadraticForm.formIdealVectorRealHeightMajorant
    ((w * s ^ 2 : ℕ) : ℤ) Q X
  let L := |(Q.a : ℝ) * (m₀ : ℝ)| / H
  let Dfund := squarefreeQuadraticFundamentalIndex w
  let hDfund : PositiveFundamentalDiscriminant Dfund :=
    squarefreeQuadraticFundamentalIndex_positiveFundamentalDiscriminant
      w hw hwone
  let S := main3LargeAnalyticTargetFibreSourcePairsInQuotientIdeal
    htheta hY hi key cell y w s hdisc J
  dsimp only
  have hparameters :=
    main3LargeAnalytic_targetFibreLeadingPell_parameters
      htheta hY hi key cell y p₀
  change 0 < Q.discriminant ∧ ¬ IsSquare Q.discriminant ∧ Q.a ≠ 0 ∧
    4 * Q.a * m₀ ≠ 0 at hparameters
  have ha : Q.a ≠ 0 := hparameters.2.2.1
  have hm₀ : m₀ ≠ 0 := by
    intro hm
    apply hparameters.2.2.2
    rw [hm]
    ring
  have hX : 0 ≤ X :=
    main3LargeAnalyticFixedKeySourceCoordinateRadius_nonneg
      (shiftedSquareA h v) D key
  have hvalue : ∀ z ∈ S, Q.eval z.1 z.2 = m₀ := by
    intro z hz
    exact
      (main3LargeAnalytic_targetFibreSourcePair_primitivePart_representation
        htheta hY hi key cell y (Finset.mem_filter.mp hz).1).1
  have hideal : ∀ z ∈ S,
      IntegralBinaryQuadraticForm.formRepresentationQuotientIdeal
        ((w * s ^ 2 : ℕ) : ℤ) Q hdisc z.1 z.2 = J := by
    intro z hz
    exact (Finset.mem_filter.mp hz).2
  have hL : 0 < L := by
    apply div_pos
    · apply abs_pos.mpr
      exact mul_ne_zero (by exact_mod_cast ha) (by exact_mod_cast hm₀)
    · exact IntegralBinaryQuadraticForm.formIdealVectorRealHeightMajorant_pos
        ((w * s ^ 2 : ℕ) : ℤ) (by positivity) Q hX
  have hp₀pair : (p₀.1.1 0, p₀.1.1 1) ∈
      main3LargeAnalyticFixedKeyCellTargetFibreSourcePairs
        htheta hY hi key cell y := by
    rw [main3LargeAnalyticFixedKeyCellTargetFibreSourcePairs]
    exact Finset.mem_image.mpr ⟨p₀.1, p₀.property, rfl⟩
  have hp₀bounds := main3LargeAnalytic_targetFibreSourcePair_abs_bounds
    htheta hY hi key cell y hp₀pair
  have hp₀value :=
    (main3LargeAnalytic_targetFibreSourcePair_primitivePart_representation
      htheta hY hi key cell y hp₀pair).1
  have hp₀window :=
    IntegralBinaryQuadraticForm.abs_rationalQuadraticAlgebraRealEmbedding_formIdealVector_mem_reciprocal_heightWindow
      ((w * s ^ 2 : ℕ) : ℤ) (by positivity) Q hdisc ha m₀ hm₀
        hp₀value hX hp₀bounds.1 hp₀bounds.2
  change 0 < L ∧ L ≤
      |rationalQuadraticAlgebraRealEmbedding ((w * s ^ 2 : ℕ) : ℤ)
        (by positivity)
        (IntegralBinaryQuadraticForm.formIdealVector
          ((w * s ^ 2 : ℕ) : ℤ) Q hdisc (p₀.1.1 0) (p₀.1.1 1) :
          rationalQuadraticAlgebra ((w * s ^ 2 : ℕ) : ℤ))| ∧
      |rationalQuadraticAlgebraRealEmbedding ((w * s ^ 2 : ℕ) : ℤ)
        (by positivity)
        (IntegralBinaryQuadraticForm.formIdealVector
          ((w * s ^ 2 : ℕ) : ℤ) Q hdisc (p₀.1.1 0) (p₀.1.1 1) :
          rationalQuadraticAlgebra ((w * s ^ 2 : ℕ) : ℤ))| ≤ H at hp₀window
  have hLH : L ≤ H := hp₀window.2.1.trans hp₀window.2.2
  have hheight : ∀ z ∈ S,
      L ≤
          |quadraticOrderPellRealEval (Dfund : ℤ)
            (int_pos_of_positiveFundamentalDiscriminant hDfund).le
            (squarefreeMulSqFundamentalRingOfIntegersEquiv w s hs
              (IntegralBinaryQuadraticForm.formIdealVector
                ((w * s ^ 2 : ℕ) : ℤ) Q hdisc z.1 z.2))| ∧
        |quadraticOrderPellRealEval (Dfund : ℤ)
            (int_pos_of_positiveFundamentalDiscriminant hDfund).le
            (squarefreeMulSqFundamentalRingOfIntegersEquiv w s hs
              (IntegralBinaryQuadraticForm.formIdealVector
                ((w * s ^ 2 : ℕ) : ℤ) Q hdisc z.1 z.2))| ≤ H := by
    intro z hz
    have hbounds := main3LargeAnalytic_targetFibreSourcePair_abs_bounds
      htheta hY hi key cell y (Finset.mem_filter.mp hz).1
    have hwindow :=
      IntegralBinaryQuadraticForm.abs_rationalQuadraticAlgebraRealEmbedding_formIdealVector_mem_reciprocal_heightWindow
        ((w * s ^ 2 : ℕ) : ℤ) (by positivity) Q hdisc ha m₀ hm₀
          (hvalue z hz) hX hbounds.1 hbounds.2
    change 0 < L ∧ L ≤
        |rationalQuadraticAlgebraRealEmbedding ((w * s ^ 2 : ℕ) : ℤ)
          (by positivity)
          (IntegralBinaryQuadraticForm.formIdealVector
            ((w * s ^ 2 : ℕ) : ℤ) Q hdisc z.1 z.2 :
            rationalQuadraticAlgebra ((w * s ^ 2 : ℕ) : ℤ))| ∧
        |rationalQuadraticAlgebraRealEmbedding ((w * s ^ 2 : ℕ) : ℤ)
          (by positivity)
          (IntegralBinaryQuadraticForm.formIdealVector
            ((w * s ^ 2 : ℕ) : ℤ) Q hdisc z.1 z.2 :
            rationalQuadraticAlgebra ((w * s ^ 2 : ℕ) : ℤ))| ≤ H at hwindow
    let beta := IntegralBinaryQuadraticForm.formIdealVector
      ((w * s ^ 2 : ℕ) : ℤ) Q hdisc z.1 z.2
    have heval :
        quadraticOrderPellRealEval (Dfund : ℤ)
            (int_pos_of_positiveFundamentalDiscriminant hDfund).le
            (squarefreeMulSqFundamentalRingOfIntegersEquiv w s hs beta) =
          rationalQuadraticAlgebraRealEmbedding
            ((w * s ^ 2 : ℕ) : ℤ) (by positivity)
            (beta : rationalQuadraticAlgebra ((w * s ^ 2 : ℕ) : ℤ)) := by
      unfold quadraticOrderPellRealEval
      change rationalQuadraticAlgebraRealEmbedding (Dfund : ℤ)
          (int_pos_of_positiveFundamentalDiscriminant hDfund).le
          (((squarefreeMulSqFundamentalRingOfIntegersEquiv w s hs beta :
              NumberField.RingOfIntegers
                (rationalQuadraticAlgebra (Dfund : ℤ))) :
            rationalQuadraticAlgebra (Dfund : ℤ))) = _
      exact
        rationalQuadraticAlgebraRealEmbedding_squarefreeMulSqFundamentalRingOfIntegersEquiv
          w s hs beta
    change L ≤
        |quadraticOrderPellRealEval (Dfund : ℤ)
          (int_pos_of_positiveFundamentalDiscriminant hDfund).le
          (squarefreeMulSqFundamentalRingOfIntegersEquiv w s hs beta)| ∧
      |quadraticOrderPellRealEval (Dfund : ℤ)
          (int_pos_of_positiveFundamentalDiscriminant hDfund).le
          (squarefreeMulSqFundamentalRingOfIntegersEquiv w s hs beta)| ≤ H
    rw [heval]
    exact hwindow.2
  exact
    IntegralBinaryQuadraticForm.card_formRepresentationQuotientIdeal_fibre_le_two_mul_log_height
      ((w * s ^ 2 : ℕ) : ℤ) (by positivity) Q hdisc ha m₀ hm₀ J S
      (squarefreeMulSqFundamentalRingOfIntegersEquiv w s hs)
      (quadraticOrderPellRealEval (Dfund : ℤ)
        (int_pos_of_positiveFundamentalDiscriminant hDfund).le)
      (concreteFundamentalUnitRealModel Dfund hDfund)
      L H hL hLH hvalue hideal hheight

end

end PellPaper
