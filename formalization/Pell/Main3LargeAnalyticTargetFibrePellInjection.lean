import Pell.Main3LargeAnalyticPrimitiveFormPellReduction

/-!
# Injecting one fixed target fibre into a generalized Pell fibre

For one fixed shift, auxiliary key, archimedean cell, and target vector, this
file applies the leading-coefficient completion of the square to every source
point in the exact target fibre.  The image lies on one generalized Pell
equation, retains the congruence that recovers the leading source coordinate,
and has exactly the cardinality of the original target fibre.

No height-window or representation-number estimate is asserted here.
-/

namespace PellPaper

noncomputable section

/-- The leading completion-of-the-square image of a target-fibre point lies
on the generalized Pell fibre whose level is the represented primitive-form
level multiplied by `4 Q.a`. -/
theorem main3LargeAnalytic_targetFibreLeadingPellMap_mem_generalizedPellSolutionFibre
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (y : Fin 2 → ℤ)
    (p : Main3LargeAnalyticFixedKeyCellTargetFibrePoint
      htheta hY hi key cell y) :
    let Q := main3LargeAnalyticFixedTargetPrimitiveSurfaceForm hi y
    let g := main3LargeAnalyticFixedTargetSurfaceContent hi y
    main3LargeAnalyticTargetFibreLeadingPellMap
        htheta hY hi key cell y p ∈
      generalizedPellSolutionFibre Q.discriminant
        (4 * Q.a *
          (shiftedSquareAuxiliaryKeySurfaceLevel key / (g : ℤ))) := by
  let Q := main3LargeAnalyticFixedTargetPrimitiveSurfaceForm hi y
  let g := main3LargeAnalyticFixedTargetSurfaceContent hi y
  have hrepresentation :=
    main3LargeAnalytic_targetFibre_primitivePart_representation
      htheta hY hi key cell y p.property
  change 0 < g ∧ (g = 1 ∨ g = 2) ∧
      (g : ℤ) ∣ shiftedSquareAuxiliaryKeySurfaceLevel key ∧
        Q.eval (p.1.1 0) (p.1.1 1) =
            shiftedSquareAuxiliaryKeySurfaceLevel key / (g : ℤ) ∧
          Q.eval (p.1.1 0) (p.1.1 1) ≠ 0 at hrepresentation
  change
    (Q.leadingPellMap (p.1.1 0, p.1.1 1)).1 ^ 2 -
          Q.discriminant *
            (Q.leadingPellMap (p.1.1 0, p.1.1 1)).2 ^ 2 =
      4 * Q.a *
        (shiftedSquareAuxiliaryKeySurfaceLevel key / (g : ℤ))
  calc
    (Q.leadingPellMap (p.1.1 0, p.1.1 1)).1 ^ 2 -
          Q.discriminant *
            (Q.leadingPellMap (p.1.1 0, p.1.1 1)).2 ^ 2 =
        4 * Q.a * Q.eval (p.1.1 0) (p.1.1 1) :=
      IntegralBinaryQuadraticForm.leadingPellMap_spec
        Q (p.1.1 0, p.1.1 1)
    _ = 4 * Q.a *
        (shiftedSquareAuxiliaryKeySurfaceLevel key / (g : ℤ)) := by
      rw [hrepresentation.2.2.2.1]

/-- The image retains the exact congruence needed to divide by `2 Q.a` and
recover the first source coordinate. -/
theorem main3LargeAnalytic_targetFibreLeadingPellMap_leadingCoefficient_dvd
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (y : Fin 2 → ℤ)
    (p : Main3LargeAnalyticFixedKeyCellTargetFibrePoint
      htheta hY hi key cell y) :
    let Q := main3LargeAnalyticFixedTargetPrimitiveSurfaceForm hi y
    2 * Q.a ∣
      (main3LargeAnalyticTargetFibreLeadingPellMap
          htheta hY hi key cell y p).1 -
        Q.b *
          (main3LargeAnalyticTargetFibreLeadingPellMap
            htheta hY hi key cell y p).2 := by
  let Q := main3LargeAnalyticFixedTargetPrimitiveSurfaceForm hi y
  change 2 * Q.a ∣
    (Q.leadingPellMap (p.1.1 0, p.1.1 1)).1 -
      Q.b * (Q.leadingPellMap (p.1.1 0, p.1.1 1)).2
  exact IntegralBinaryQuadraticForm.leadingCoefficient_dvd_pellMap_fst_sub
    Q (p.1.1 0, p.1.1 1)

/-- On the exact target-fibre subtype, the leading Pell map is injective.
The nonsquare discriminant makes `Q.a` nonzero, while target-fibre membership
fixes the second vector to be `y`. -/
theorem main3LargeAnalytic_targetFibreLeadingPellMap_injective
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (y : Fin 2 → ℤ) :
    Function.Injective
      (main3LargeAnalyticTargetFibreLeadingPellMap
        htheta hY hi key cell y) := by
  intro p q hpq
  let Q := main3LargeAnalyticFixedTargetPrimitiveSurfaceForm hi y
  have hdiscriminantData :=
    main3LargeAnalytic_targetFibre_surfacePrimitivePart_discriminantData
      htheta hY hi key cell y p.property
  change Q.Primitive ∧ 0 < Q.discriminant ∧
      ¬ IsSquare Q.discriminant ∧
        ∃ w s : ℕ, Squarefree w ∧ 1 < w ∧ 0 < s ∧
          Q.discriminant = ((w * s ^ 2 : ℕ) : ℤ) at hdiscriminantData
  have hsource :
      (p.1.1 0, p.1.1 1) = (q.1.1 0, q.1.1 1) := by
    apply IntegralBinaryQuadraticForm.leadingPellMap_injective Q
      (IntegralBinaryQuadraticForm.leadingCoefficient_ne_zero_of_discriminant_not_isSquare
        Q hdiscriminantData.2.2.1)
    exact hpq
  have hx0 : p.1.1 0 = q.1.1 0 := congrArg Prod.fst hsource
  have hx1 : p.1.1 1 = q.1.1 1 := congrArg Prod.snd hsource
  have hpTarget : p.1.2 = y :=
    (mem_main3LargeAnalyticFixedKeyCellTargetFibre
      htheta hY hi key cell y p.1).mp p.property |>.2
  have hqTarget : q.1.2 = y :=
    (mem_main3LargeAnalyticFixedKeyCellTargetFibre
      htheta hY hi key cell y q.1).mp q.property |>.2
  apply Subtype.ext
  apply Prod.ext
  · funext i
    fin_cases i
    · exact hx0
    · exact hx1
  · exact hpTarget.trans hqTarget.symm

/-- The Pell parameters attached to an inhabited target fibre are genuinely
indefinite and nondegenerate: the discriminant is positive and nonsquare,
the chosen leading coefficient is nonzero, and so is the resulting Pell
level. -/
theorem main3LargeAnalytic_targetFibreLeadingPell_parameters
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (y : Fin 2 → ℤ)
    (p : Main3LargeAnalyticFixedKeyCellTargetFibrePoint
      htheta hY hi key cell y) :
    let Q := main3LargeAnalyticFixedTargetPrimitiveSurfaceForm hi y
    let g := main3LargeAnalyticFixedTargetSurfaceContent hi y
    0 < Q.discriminant ∧ ¬ IsSquare Q.discriminant ∧ Q.a ≠ 0 ∧
      4 * Q.a *
        (shiftedSquareAuxiliaryKeySurfaceLevel key / (g : ℤ)) ≠ 0 := by
  let Q := main3LargeAnalyticFixedTargetPrimitiveSurfaceForm hi y
  let g := main3LargeAnalyticFixedTargetSurfaceContent hi y
  have hdiscriminantData :=
    main3LargeAnalytic_targetFibre_surfacePrimitivePart_discriminantData
      htheta hY hi key cell y p.property
  change Q.Primitive ∧ 0 < Q.discriminant ∧
      ¬ IsSquare Q.discriminant ∧
        ∃ w s : ℕ, Squarefree w ∧ 1 < w ∧ 0 < s ∧
          Q.discriminant = ((w * s ^ 2 : ℕ) : ℤ) at hdiscriminantData
  have hrepresentation :=
    main3LargeAnalytic_targetFibre_primitivePart_representation
      htheta hY hi key cell y p.property
  change 0 < g ∧ (g = 1 ∨ g = 2) ∧
      (g : ℤ) ∣ shiftedSquareAuxiliaryKeySurfaceLevel key ∧
        Q.eval (p.1.1 0) (p.1.1 1) =
            shiftedSquareAuxiliaryKeySurfaceLevel key / (g : ℤ) ∧
          Q.eval (p.1.1 0) (p.1.1 1) ≠ 0 at hrepresentation
  have ha : Q.a ≠ 0 :=
    IntegralBinaryQuadraticForm.leadingCoefficient_ne_zero_of_discriminant_not_isSquare
      Q hdiscriminantData.2.2.1
  have hquotient :
      shiftedSquareAuxiliaryKeySurfaceLevel key / (g : ℤ) ≠ 0 := by
    rw [← hrepresentation.2.2.2.1]
    exact hrepresentation.2.2.2.2
  exact ⟨hdiscriminantData.2.1, hdiscriminantData.2.2.1, ha,
    mul_ne_zero (mul_ne_zero (by norm_num) ha) hquotient⟩

/-- The finite leading-Pell image of the exact fixed-key, fixed-cell target
fibre. -/
noncomputable def main3LargeAnalyticTargetFibreLeadingPellImage
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (y : Fin 2 → ℤ) : Finset (ℤ × ℤ) :=
  (main3LargeAnalyticFixedKeyCellTargetFibre
      htheta hY hi key cell y).attach.image
    (main3LargeAnalyticTargetFibreLeadingPellMap
      htheta hY hi key cell y)

/-- The finite Pell image has exactly the cardinality of the target fibre. -/
theorem card_main3LargeAnalyticTargetFibreLeadingPellImage_eq
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (y : Fin 2 → ℤ) :
    (main3LargeAnalyticTargetFibreLeadingPellImage
        htheta hY hi key cell y).card =
      (main3LargeAnalyticFixedKeyCellTargetFibre
        htheta hY hi key cell y).card := by
  classical
  rw [main3LargeAnalyticTargetFibreLeadingPellImage,
    Finset.card_image_of_injective _
      (main3LargeAnalytic_targetFibreLeadingPellMap_injective
        htheta hY hi key cell y),
    Finset.card_attach]

/-- Every point of the finite image satisfies both the fixed generalized
Pell equation and the leading-coefficient recovery congruence. -/
theorem main3LargeAnalytic_targetFibreLeadingPellImage_pellEquation_and_congruence
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (y : Fin 2 → ℤ)
    {z : ℤ × ℤ}
    (hz : z ∈ main3LargeAnalyticTargetFibreLeadingPellImage
      htheta hY hi key cell y) :
    let Q := main3LargeAnalyticFixedTargetPrimitiveSurfaceForm hi y
    let g := main3LargeAnalyticFixedTargetSurfaceContent hi y
    z ∈ generalizedPellSolutionFibre Q.discriminant
        (4 * Q.a *
          (shiftedSquareAuxiliaryKeySurfaceLevel key / (g : ℤ))) ∧
      2 * Q.a ∣ z.1 - Q.b * z.2 := by
  classical
  obtain ⟨p, _hp, rfl⟩ := Finset.mem_image.mp hz
  exact ⟨
    main3LargeAnalytic_targetFibreLeadingPellMap_mem_generalizedPellSolutionFibre
      htheta hY hi key cell y p,
    main3LargeAnalytic_targetFibreLeadingPellMap_leadingCoefficient_dvd
      htheta hY hi key cell y p⟩

end

end PellPaper
