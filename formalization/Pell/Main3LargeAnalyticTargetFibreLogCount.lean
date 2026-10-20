import Pell.Main3LargeAnalyticTargetFibreUnitHeightCount
import Pell.Main3LargeAnalyticTargetFibreIdealCount

/-!
# Literal logarithmic count for one main3 target fibre

The exact quotient-ideal partition of a fixed-key, fixed-cell target fibre is
combined with the logarithmic signed-unit count inside each ideal fibre.  The
number of occurring quotient ideals is charged to the divisor count of the
auxiliary-key surface level.

The resulting estimate retains the exact real-height logarithm and concrete
fundamental-unit generator.  In particular, no regulator lower bound or
`O(theta)` simplification is used here.
-/

namespace PellPaper

open NumberField

noncomputable section

/-- A literal nonempty main3 target fibre has cardinality at most the divisor
count of the auxiliary-key level times the exact logarithmic signed-unit
capacity. -/
theorem card_main3LargeAnalyticFixedKeyCellTargetFibre_le_key_divisors_mul_log_height
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
        ((w * s ^ 2 : ℕ) : ℤ)) :
    let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
        ((w * s ^ 2 : ℕ) : ℤ)) :=
      ⟨rationalQuadraticAlgebraNoRationalRoot_of_not_isSquare
        ((w * s ^ 2 : ℕ) : ℤ) (by
          simpa only [Int.isSquare_natCast_iff] using
            not_isSquare_squarefree_mul_sq hw hwone hs)⟩
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
    let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (Dfund : ℤ)) :=
      ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant
        hDfund⟩
    ((main3LargeAnalyticFixedKeyCellTargetFibre
        htheta hY hi key cell y).card : ℝ) ≤
      ((shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs.divisors.card : ℝ) *
        (2 * (1 + Real.log (H / L) /
          Real.log (concreteFundamentalUnitRealModel Dfund hDfund).eta)) := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      ((w * s ^ 2 : ℕ) : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_not_isSquare
      ((w * s ^ 2 : ℕ) : ℤ) (by
        simpa only [Int.isSquare_natCast_iff] using
          not_isSquare_squarefree_mul_sq hw hwone hs)⟩
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
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (Dfund : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant
      hDfund⟩
  let S := main3LargeAnalyticFixedKeyCellTargetFibreSourcePairs
    htheta hY hi key cell y
  let image := IntegralBinaryQuadraticForm.formRepresentationQuotientIdealImage
    ((w * s ^ 2 : ℕ) : ℤ) Q hdisc S
  let capacity : ℝ := 2 * (1 + Real.log (H / L) /
    Real.log (concreteFundamentalUnitRealModel Dfund hDfund).eta)
  dsimp only
  have hpartition :=
    IntegralBinaryQuadraticForm.card_eq_sum_card_formRepresentationQuotientIdeal_fibres
      ((w * s ^ 2 : ℕ) : ℤ) Q hdisc S
  change S.card = ∑ J ∈ image,
      (S.filter fun z =>
        IntegralBinaryQuadraticForm.formRepresentationQuotientIdeal
          ((w * s ^ 2 : ℕ) : ℤ) Q hdisc z.1 z.2 = J).card at hpartition
  have hfibre : ∀ J : Ideal (NumberField.RingOfIntegers
      (rationalQuadraticAlgebra ((w * s ^ 2 : ℕ) : ℤ))),
      ((S.filter fun z =>
        IntegralBinaryQuadraticForm.formRepresentationQuotientIdeal
          ((w * s ^ 2 : ℕ) : ℤ) Q hdisc z.1 z.2 = J).card : ℝ) ≤ capacity := by
    intro J
    exact
      card_main3LargeAnalyticTargetFibreSourcePairsInQuotientIdeal_le_log_height
        htheta hY hi key cell y p₀ w s hw hwone hs hdisc J
  have hcapacity : 0 ≤ capacity := by
    let J : Ideal (NumberField.RingOfIntegers
        (rationalQuadraticAlgebra ((w * s ^ 2 : ℕ) : ℤ))) := ⊥
    have hzero : (0 : ℝ) ≤
        ((S.filter fun z =>
          IntegralBinaryQuadraticForm.formRepresentationQuotientIdeal
            ((w * s ^ 2 : ℕ) : ℤ) Q hdisc z.1 z.2 = J).card : ℝ) := by
      positivity
    exact hzero.trans (hfibre J)
  have himage : image.card ≤
      (shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs.divisors.card := by
    exact card_main3LargeAnalytic_targetFibre_quotientIdealImage_le_key_divisors
      htheta hY hi key cell y p₀ w s hw hwone hs hdisc
  rw [← card_main3LargeAnalyticFixedKeyCellTargetFibreSourcePairs_eq
    htheta hY hi key cell y]
  calc
    (S.card : ℝ) = ∑ J ∈ image,
        ((S.filter fun z =>
          IntegralBinaryQuadraticForm.formRepresentationQuotientIdeal
            ((w * s ^ 2 : ℕ) : ℤ) Q hdisc z.1 z.2 = J).card : ℝ) := by
      exact_mod_cast hpartition
    _ ≤ ∑ _J ∈ image, capacity := by
      exact Finset.sum_le_sum fun J _ => hfibre J
    _ = (image.card : ℝ) * capacity := by simp
    _ ≤ ((shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs.divisors.card : ℝ) *
        capacity := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast himage) hcapacity

end

end PellPaper
