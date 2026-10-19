import Pell.IntrinsicOddHomogeneousPolynomialSquareSieveElementary
import Pell.Main3LargeAnalyticFixedKeyCellIntrinsicSieve
import Mathlib.Tactic

/-! Fixed-parameter Main3 specialization of the elementary intrinsic sieve. -/

namespace PellPaper

open Filter
open scoped MatrixGroups

noncomputable section

def FullCellElementaryOddHomogeneousPolynomialSieveAt (sieveN : ℕ) : Prop :=
  ∀ (U V M mu delta A B : ℝ) (W : SL(2, ℤ))
    (T : Finset (Fin 2 → ℤ))
    (K : MvPolynomial (Fin 2) ℤ) (d HK : ℕ),
    0 < U → 0 < V → 0 < M → 0 < mu → 0 < delta →
    mu ^ 2 ≤ delta →
    K.IsHomogeneous d → Odd d → 0 < HK →
    (∀ e, |(binaryLinearSubstitution
      (W : Matrix (Fin 2) (Fin 2) ℤ) K).coeff e| ≤ (HK : ℤ)) →
    sl2InverseTargetImage W T ⊆ integerSymmetricRectangle A B →
    ((integerSymmetricRectangle A B).card : ℝ) ≤ 144 * U * V / M →
    ((integerSymmetricInterval A).card : ℝ) ≤ 12 / mu →
    ((integerSymmetricInterval B).card : ℝ) ≤ 12 * mu / delta →
    A ≤ 4 * (U + V) → B ≤ 4 * (U + V) →
    let HJ : ℕ := 2 ^ d * (d + 1) * HK
    let Wval : ℝ :=
      ((d : ℝ) + 1) * (HK : ℝ) * (4 * (U + V)) ^ d
    Real.log Wval ≤ (Real.log 2 / 16) * (sieveN : ℝ) →
    (∀ j : ℕ, Odd j → 0 < j → j ≤ d →
      fullCellCertificateLogMajorant d HK j +
          2 * Real.log (HJ : ℝ) ≤
        (Real.log 2 / 8) * (sieveN : ℝ)) →
    (((T.filter fun y =>
      IsSquare (MvPolynomial.eval y K) ∧
        MvPolynomial.eval y K ≠ 0).card : ℝ)) ≤
      fullCellElementarySieveEnvelope sieveN d U V M mu

theorem eventually_fullCellElementaryOddHomogeneousPolynomialSieveAt :
    ∀ᶠ sieveN : ℕ in atTop,
      FullCellElementaryOddHomogeneousPolynomialSieveAt sieveN := by
  simpa only [FullCellElementaryOddHomogeneousPolynomialSieveAt] using
    eventually_fullCell_oddHomogeneousPolynomial_filter_le_elementary

theorem FullCellElementaryOddHomogeneousPolynomialSieveAt.card_main3LargeAnalyticFixedKeyCell_intrinsicResidual_filter_le_fullCellEnvelope_of_entryBoundSpec
    {sieveN : ℕ}
    (hsieve : FullCellElementaryOddHomogeneousPolynomialSieveAt sieveN)
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N B : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (hcoordinateNonempty :
      (main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
        htheta hY hi key cell).Nonempty)
    (hkeyGate : key ∈ main3LargeAnalytic_blockAuxiliaryKeyGate h v)
    (data : Main3LargeAnalyticFixedKeyCellAuxiliaryFactorData
      htheta hY hi key cell B)
    {R K C : ℝ}
    (cert : PrimitiveWedgeReducedTargetCoverCertificate
      (main3LargeAnalyticFixedKeyCellTargetVectorImage
        htheta hY hi key cell) R K C)
    (G H : SL(2, ℤ))
    (hspec : PrimitiveWedgeReducedTargetCoverEntryBoundSpec
      (main3LargeAnalyticFixedKeyCellTargetVectorImage
        htheta hY hi key cell)
      cert.ell cert.anchor R K C
      (main3LargeAnalyticFixedKeyTargetCoordinateRadius
        (shiftedSquareA h v) Y key) G H) :
    let T := main3LargeAnalyticFixedKeyCellTargetVectorImage
      htheta hY hi key cell
    let T₀ := main3LargeAnalyticFixedKeyTargetCoordinateRadius
      (shiftedSquareA h v) Y key
    let rho := cert.ell cert.anchor
    let U := K / 2
    let V := 1 + C / 2
    let M₀ := 2 * rho * V / R
    let beta := cert.ell (fun i ↦ G i 1)
    let z := -K * beta / R
    let mu := firstSlopeSupNorm U V M₀ z
    let delta := M₀ / (U * V)
    let Brect := 4 * mu / delta
    let L := 2 * (T₀ + 1) * reducedSlopeMatrixEntryBound U V M₀ z
    let P := main3LargeAnalyticIntrinsicEliminant
      htheta hY hi key cell data
    let d := main3LargeAnalyticIntrinsicEliminantDegree data
    1 ≤ Brect →
      main3LargeAnalyticIntrinsicEliminantSieveBudgetThreshold
          data L U V ≤ (sieveN : ℝ) →
        (((T.filter fun y ↦
          IsSquare (MvPolynomial.eval y P) ∧
            MvPolynomial.eval y P ≠ 0).card : ℝ)) ≤
          fullCellElementarySieveEnvelope sieveN d U V M₀ mu := by
  dsimp only
  intro hBrect hthreshold
  let T := main3LargeAnalyticFixedKeyCellTargetVectorImage
    htheta hY hi key cell
  let T₀ := main3LargeAnalyticFixedKeyTargetCoordinateRadius
    (shiftedSquareA h v) Y key
  let rho := cert.ell cert.anchor
  let U := K / 2
  let V := 1 + C / 2
  let M₀ := 2 * rho * V / R
  let beta := cert.ell (fun i ↦ G i 1)
  let z := -K * beta / R
  let mu := firstSlopeSupNorm U V M₀ z
  let delta := M₀ / (U * V)
  let A := 4 / mu
  let Brect := 4 * mu / delta
  let W := G * H
  let L := 2 * (T₀ + 1) * reducedSlopeMatrixEntryBound U V M₀ z
  let P := main3LargeAnalyticIntrinsicEliminant
    htheta hY hi key cell data
  let d := main3LargeAnalyticIntrinsicEliminantDegree data
  let HK := main3LargeAnalyticIntrinsicEliminantSubstitutionHeight
    htheta hY hi key cell data L
  have hgeometry := hspec.sieve_geometry
  dsimp only at hgeometry
  rcases hgeometry with
    ⟨hWentry, hM₀one, hmu, hdelta, hmuSq, hsubset,
      hA, hB, _hthin, hfull⟩
  rcases hfull hBrect with ⟨harea, hsideA, hsideB⟩
  have hU : 0 < U := by dsimp only [U]; linarith [cert.K_pos]
  have hV : 0 < V := by dsimp only [V]; linarith [cert.C_pos]
  have hM₀pos : 0 < M₀ := zero_lt_one.trans_le hM₀one
  have hT₀ : (1 : ℝ) ≤ T₀ := by
    dsimp only [T₀]
    exact
      one_le_main3LargeAnalyticFixedKeyTargetCoordinateRadius_of_targetImage_nonempty
        htheta hY hi key cell ⟨cert.anchor, cert.anchor_mem⟩
  have hReducedEntry : 0 ≤ reducedSlopeMatrixEntryBound U V M₀ z := by
    unfold reducedSlopeMatrixEntryBound slopeStandardBasisRadius
    positivity
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hhom : P.IsHomogeneous d := by
    dsimp only [P, d]
    exact main3LargeAnalyticIntrinsicEliminant_isHomogeneous
      htheta hY hi key cell data
  have hodd : Odd d := by
    dsimp only [d]
    exact main3LargeAnalyticIntrinsicEliminantDegree_odd data
  have hHK : 0 < HK := by
    dsimp only [HK]
    exact main3LargeAnalyticIntrinsicEliminantSubstitutionHeight_pos
      htheta hY hi key cell data L
  have hcoeff : ∀ e,
      |(binaryLinearSubstitution (W : Matrix (Fin 2) (Fin 2) ℤ) P).coeff e| ≤
        (HK : ℤ) := by
    intro e
    dsimp only [W, P, HK]
    exact
      abs_coeff_binaryLinearSubstitution_main3LargeAnalyticIntrinsicEliminant_le
        htheta hY hi key cell data (G * H) L hWentry e
  have hbudgets :=
    main3LargeAnalyticIntrinsicEliminantSieveBudgets_of_threshold_le
      htheta hY hi key cell hcoordinateNonempty hkeyGate data L U V sieveN
        hL hU hV hthreshold
  dsimp only at hbudgets
  unfold FullCellElementaryOddHomogeneousPolynomialSieveAt at hsieve
  exact hsieve U V M₀ mu delta A Brect W T P d HK
    hU hV hM₀pos hmu hdelta hmuSq hhom hodd hHK hcoeff
    hsubset harea hsideA hsideB hA hB hbudgets.1 hbudgets.2

theorem FullCellElementaryOddHomogeneousPolynomialSieveAt.card_main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber_cast_le_commonFactor_add_twice_fullCellEnvelope_of_entryBoundSpec
    {sieveN : ℕ}
    (hsieve : FullCellElementaryOddHomogeneousPolynomialSieveAt sieveN)
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N B : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
    (hcoordinateNonempty :
      (main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
        htheta hY hi key cell).Nonempty)
    (hkeyGate : key ∈ main3LargeAnalytic_blockAuxiliaryKeyGate h v)
    (data : Main3LargeAnalyticFixedKeyCellAuxiliaryFactorData
      htheta hY hi key cell B)
    {R K C : ℝ}
    (cert : PrimitiveWedgeReducedTargetCoverCertificate
      (main3LargeAnalyticFixedKeyCellTargetVectorImage
        htheta hY hi key cell) R K C)
    (G H : SL(2, ℤ))
    (hspec : PrimitiveWedgeReducedTargetCoverEntryBoundSpec
      (main3LargeAnalyticFixedKeyCellTargetVectorImage
        htheta hY hi key cell)
      cert.ell cert.anchor R K C
      (main3LargeAnalyticFixedKeyTargetCoordinateRadius
        (shiftedSquareA h v) Y key) G H) :
    let T₀ := main3LargeAnalyticFixedKeyTargetCoordinateRadius
      (shiftedSquareA h v) Y key
    let rho := cert.ell cert.anchor
    let U := K / 2
    let V := 1 + C / 2
    let M₀ := 2 * rho * V / R
    let beta := cert.ell (fun i ↦ G i 1)
    let z := -K * beta / R
    let mu := firstSlopeSupNorm U V M₀ z
    let delta := M₀ / (U * V)
    let Brect := 4 * mu / delta
    let L := 2 * (T₀ + 1) * reducedSlopeMatrixEntryBound U V M₀ z
    let d := main3LargeAnalyticIntrinsicEliminantDegree data
    1 ≤ Brect →
      main3LargeAnalyticIntrinsicEliminantSieveBudgetThreshold
          data L U V ≤ (sieveN : ℝ) →
        ((main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
          htheta hY hi key cell).card : ℝ) ≤
          2048 * (B : ℝ) * theta *
              ((shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs.divisors.card : ℝ) +
            2 * fullCellElementarySieveEnvelope sieveN d U V M₀ mu := by
  dsimp only
  intro hBrect hthreshold
  have hresidual :=
    hsieve.card_main3LargeAnalyticFixedKeyCell_intrinsicResidual_filter_le_fullCellEnvelope_of_entryBoundSpec
      htheta hY hi key cell hcoordinateNonempty hkeyGate data cert G H hspec
        hBrect hthreshold
  have hcomposition :=
    card_main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber_cast_le_commonFactor_add_twice_intrinsicResidual
      htheta hY hi key cell data
      (fullCellElementarySieveEnvelope sieveN
        (main3LargeAnalyticIntrinsicEliminantDegree data)
        (K / 2) (1 + C / 2)
        (2 * cert.ell cert.anchor * (1 + C / 2) / R)
        (firstSlopeSupNorm (K / 2) (1 + C / 2)
          (2 * cert.ell cert.anchor * (1 + C / 2) / R)
          (-K * cert.ell (fun i ↦ G i 1) / R)))
      (by exact hresidual)
  exact hcomposition

end

end PellPaper

#print axioms PellPaper.eventually_fullCellElementaryOddHomogeneousPolynomialSieveAt
