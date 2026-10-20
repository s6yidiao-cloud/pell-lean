import Pell.Main3LargeAnalyticTargetFibreIdealPartition
import Pell.DivisorCardinalityMonotonicity

/-!
# Charging the literal target-fibre ideal image to the key level

The primitive surface form represents `m₀ = c/g`, where its positive content
`g` divides the fixed nonzero auxiliary-key level `c`.  Combining the exact
quotient-ideal image bound by `tau(|m₀|)` with monotonicity of divisor count
under divisibility gives the manuscript's uniform charge `tau(|c|)`.

This closes the last arithmetic step in the manuscript.  The number of
representations inside one quotient-ideal fibre is handled separately.
-/

namespace PellPaper

noncomputable section

/-- At most `tau(|c|)` maximal-order quotient ideals occur in a literal
fixed-target source fibre, where `c` is the fixed auxiliary-key surface
level. -/
theorem card_main3LargeAnalytic_targetFibre_quotientIdealImage_le_key_divisors
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
    (IntegralBinaryQuadraticForm.formRepresentationQuotientIdealImage
        ((w * s ^ 2 : ℕ) : ℤ) Q hdisc
        (main3LargeAnalyticFixedKeyCellTargetFibreSourcePairs
          htheta hY hi key cell y)).card ≤
      (shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs.divisors.card := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      ((w * s ^ 2 : ℕ) : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_not_isSquare
      ((w * s ^ 2 : ℕ) : ℤ) (by
        simpa only [Int.isSquare_natCast_iff] using
          not_isSquare_squarefree_mul_sq hw hwone hs)⟩
  let Q := main3LargeAnalyticFixedTargetPrimitiveSurfaceForm hi y
  let g := main3LargeAnalyticFixedTargetSurfaceContent hi y
  let m₀ := shiftedSquareAuxiliaryKeySurfaceLevel key / (g : ℤ)
  dsimp only
  have himage :=
    card_main3LargeAnalytic_targetFibre_quotientIdealImage_le_card_divisors
      htheta hY hi key cell y p₀ w s hw hwone hs hdisc
  change
    (IntegralBinaryQuadraticForm.formRepresentationQuotientIdealImage
        ((w * s ^ 2 : ℕ) : ℤ) Q hdisc
        (main3LargeAnalyticFixedKeyCellTargetFibreSourcePairs
          htheta hY hi key cell y)).card ≤
      m₀.natAbs.divisors.card at himage
  have hrep := main3LargeAnalytic_targetFibre_primitivePart_representation
    htheta hY hi key cell y p₀.property
  change 0 < g ∧ (g = 1 ∨ g = 2) ∧
      (g : ℤ) ∣ shiftedSquareAuxiliaryKeySurfaceLevel key ∧
        Q.eval (p₀.1.1 0) (p₀.1.1 1) = m₀ ∧
          Q.eval (p₀.1.1 0) (p₀.1.1 1) ≠ 0 at hrep
  have hkey0 : shiftedSquareAuxiliaryKeySurfaceLevel key ≠ 0 := by
    intro hkey
    apply hrep.2.2.2.2
    rw [hrep.2.2.2.1]
    dsimp only [m₀]
    rw [hkey]
    exact Int.zero_ediv _
  exact himage.trans
    (card_divisors_natAbs_ediv_le_card_divisors_natAbs_of_dvd
      hkey0 hrep.2.2.1)

end

end PellPaper
