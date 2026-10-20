import Pell.Main3LargeAnalyticTargetFibreSquarefreeKernel
import Pell.QuadraticFormRepresentationIdealFibre

/-!
# Quotient-ideal partition of one literal main3 target fibre

For a fixed auxiliary key, archimedean cell, and target vector, the literal
target fibre is determined by its two source coordinates.  This file projects
the fibre bijectively to those coordinate pairs and applies the primitive-form
quotient-ideal construction.  When the primitive discriminant is `w*s^2`, the
number of quotient ideals that occur is at most `tau(|m₀|)` for the exact
nonzero represented level `m₀`.

This is the literal finite-set adapter for the manuscript.  It does not
bound the number of representations assigned to one ideal; that is the
subsequent signed-unit orbit and archimedean height-window step.
-/

namespace PellPaper

noncomputable section

/-- The two integral source coordinates occurring in one exact target fibre. -/
noncomputable def main3LargeAnalyticFixedKeyCellTargetFibreSourcePairs
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (y : Fin 2 → ℤ) : Finset (ℤ × ℤ) :=
  (main3LargeAnalyticFixedKeyCellTargetFibre
      htheta hY hi key cell y).image fun p => (p.1 0, p.1 1)

/-- Fixing the target vector makes projection to the two source coordinates
injective, so the source-pair image has exactly the cardinality of the literal
target fibre. -/
theorem card_main3LargeAnalyticFixedKeyCellTargetFibreSourcePairs_eq
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (y : Fin 2 → ℤ) :
    (main3LargeAnalyticFixedKeyCellTargetFibreSourcePairs
        htheta hY hi key cell y).card =
      (main3LargeAnalyticFixedKeyCellTargetFibre
        htheta hY hi key cell y).card := by
  classical
  rw [main3LargeAnalyticFixedKeyCellTargetFibreSourcePairs,
    Finset.card_image_iff]
  intro p hp q hq hpq
  have hpTarget : p.2 = y :=
    (mem_main3LargeAnalyticFixedKeyCellTargetFibre
      htheta hY hi key cell y p).mp hp |>.2
  have hqTarget : q.2 = y :=
    (mem_main3LargeAnalyticFixedKeyCellTargetFibre
      htheta hY hi key cell y q).mp hq |>.2
  apply Prod.ext
  · funext i
    fin_cases i
    · exact congrArg Prod.fst hpq
    · exact congrArg Prod.snd hpq
  · exact hpTarget.trans hqTarget.symm

/-- Every projected source pair represents the same nonzero primitive-form
level `m₀ = keyLevel / content`. -/
theorem main3LargeAnalytic_targetFibreSourcePair_primitivePart_representation
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (y : Fin 2 → ℤ) {z : ℤ × ℤ}
    (hz : z ∈ main3LargeAnalyticFixedKeyCellTargetFibreSourcePairs
      htheta hY hi key cell y) :
    let Q := main3LargeAnalyticFixedTargetPrimitiveSurfaceForm hi y
    let g := main3LargeAnalyticFixedTargetSurfaceContent hi y
    Q.eval z.1 z.2 =
        shiftedSquareAuxiliaryKeySurfaceLevel key / (g : ℤ) ∧
      Q.eval z.1 z.2 ≠ 0 := by
  classical
  rw [main3LargeAnalyticFixedKeyCellTargetFibreSourcePairs] at hz
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
  exact
    (main3LargeAnalytic_targetFibre_primitivePart_representation
      htheta hY hi key cell y hp).2.2.2

/-- The literal source fibre meets at most `tau(|m₀|)` quotient ideals in
the maximal order of the quadratic field attached to its primitive form. -/
theorem card_main3LargeAnalytic_targetFibre_quotientIdealImage_le_card_divisors
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
    (IntegralBinaryQuadraticForm.formRepresentationQuotientIdealImage
        ((w * s ^ 2 : ℕ) : ℤ) Q hdisc
        (main3LargeAnalyticFixedKeyCellTargetFibreSourcePairs
          htheta hY hi key cell y)).card ≤
      m₀.natAbs.divisors.card := by
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
  have hdata := main3LargeAnalytic_targetFibre_surfacePrimitivePart_discriminantData
    htheta hY hi key cell y p₀.property
  change Q.Primitive ∧ 0 < Q.discriminant ∧ ¬ IsSquare Q.discriminant ∧
      ∃ w s : ℕ, Squarefree w ∧ 1 < w ∧ 0 < s ∧
        Q.discriminant = ((w * s ^ 2 : ℕ) : ℤ) at hdata
  have ha : Q.a ≠ 0 :=
    IntegralBinaryQuadraticForm.leadingCoefficient_ne_zero_of_discriminant_not_isSquare
      Q hdata.2.2.1
  have hrep : ∀ z ∈
      main3LargeAnalyticFixedKeyCellTargetFibreSourcePairs
        htheta hY hi key cell y,
      Q.eval z.1 z.2 = m₀ := by
    intro z hz
    exact (main3LargeAnalytic_targetFibreSourcePair_primitivePart_representation
      htheta hY hi key cell y hz).1
  have hm₀ : m₀ ≠ 0 := by
    have hpRep := main3LargeAnalytic_targetFibre_primitivePart_representation
      htheta hY hi key cell y p₀.property
    change 0 < g ∧ (g = 1 ∨ g = 2) ∧
      (g : ℤ) ∣ shiftedSquareAuxiliaryKeySurfaceLevel key ∧
        Q.eval (p₀.1.1 0) (p₀.1.1 1) = m₀ ∧
          Q.eval (p₀.1.1 0) (p₀.1.1 1) ≠ 0 at hpRep
    rw [← hpRep.2.2.2.1]
    exact hpRep.2.2.2.2
  exact
    IntegralBinaryQuadraticForm.card_formRepresentationQuotientIdealImage_le_card_divisors
      w s hw hwone hs Q hdisc hdata.1 ha m₀ hm₀
        (main3LargeAnalyticFixedKeyCellTargetFibreSourcePairs
          htheta hY hi key cell y) hrep

end

end PellPaper
