import Pell.Main3LargeAnalyticFixedKeyCellTargetEntryBoundCover
import Pell.Main3LargeAnalyticIntrinsicEliminantSieveBudget
import Pell.IntrinsicOddHomogeneousPolynomialSquareSieve
import Pell.Main3LargeAnalyticFixedKeyCellResidualComposition
import Mathlib.Tactic

/-!
# Intrinsic square sieve on one fixed main3 key and cell

The entry-bounded target cover supplies one product basis `W = G * H`, its
exact first minimum `mu`, its reduced rectangle, and the literal matrix-entry
ledger used to bound the coefficients of the intrinsic eliminant after
substitution.  The thin branch is elementary.  The full branch leaves the
one-variable quadratic Weil estimate as an explicit hypothesis.
-/

namespace PellPaper

open Filter
open scoped MatrixGroups

noncomputable section

/-! ## Sieve-facing projection of the entry-bounded cover -/

/-- The precise subset, rectangle, minimum, and matrix-entry facts needed by
the intrinsic square sieve, projected from the complete same-basis spec. -/
theorem PrimitiveWedgeReducedTargetCoverEntryBoundSpec.sieve_geometry
    {T : Finset (Fin 2 → ℤ)} {ell : (Fin 2 → ℤ) →+ ℝ}
    {y₀ : Fin 2 → ℤ} {R K C T₀ : ℝ} {G H : SL(2, ℤ)}
    (hspec : PrimitiveWedgeReducedTargetCoverEntryBoundSpec
      T ell y₀ R K C T₀ G H) :
    let rho := ell y₀
    let U := K / 2
    let V := 1 + C / 2
    let M₀ := 2 * rho * V / R
    let beta := ell (fun i ↦ G i 1)
    let z := -K * beta / R
    let mu := firstSlopeSupNorm U V M₀ z
    let delta := M₀ / (U * V)
    let A := 4 / mu
    let Brect := 4 * mu / delta
    let W := G * H
    let L := 2 * (T₀ + 1) * reducedSlopeMatrixEntryBound U V M₀ z
    (∀ i j, |((W i j : ℤ) : ℝ)| ≤ L) ∧
    1 ≤ M₀ ∧
    0 < mu ∧
    0 < delta ∧
    mu ^ 2 ≤ delta ∧
    sl2InverseTargetImage W T ⊆ integerSymmetricRectangle A Brect ∧
    A ≤ 4 * (U + V) ∧
    Brect ≤ 4 * (U + V) ∧
    (Brect < 1 → T.card ≤ 2) ∧
    (1 ≤ Brect →
      ((integerSymmetricRectangle A Brect).card : ℝ) ≤
        144 * U * V / M₀ ∧
      ((integerSymmetricInterval A).card : ℝ) ≤ 12 / mu ∧
      ((integerSymmetricInterval Brect).card : ℝ) ≤
        12 * mu / delta) := by
  unfold PrimitiveWedgeReducedTargetCoverEntryBoundSpec at hspec
  unfold PrimitiveWedgeReducedTargetCoverSpec at hspec
  dsimp only at hspec ⊢
  rcases hspec with
    ⟨⟨_hcolumn, _hshort, _hall, hM₀, hmu, hdelta, _hdeltaEq,
      hmuSq, _hratioEq, _hratioLe, _hproduct, _huniversal,
      _hcard, _hprimitive, _hrecover, hsubset, _hAtwo, hA, hB,
      hthin, hfull⟩, hentry⟩
  exact ⟨hentry, hM₀, hmu, hdelta, hmuSq, hsubset, hA, hB, hthin,
    fun hBfull ↦
      ⟨(hfull hBfull).1, (hfull hBfull).2.2.1,
        (hfull hBfull).2.2.2.1⟩⟩

/-! ## Thin intrinsic residual branch -/

/-- If the reduced target rectangle is thin, the exact intrinsic residual
square filter contains at most two target vectors. -/
theorem card_main3LargeAnalyticFixedKeyCell_intrinsicResidual_filter_le_two_of_entryBoundSpec
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N B : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
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
    let rho := cert.ell cert.anchor
    let U := K / 2
    let V := 1 + C / 2
    let M₀ := 2 * rho * V / R
    let beta := cert.ell (fun i ↦ G i 1)
    let z := -K * beta / R
    let mu := firstSlopeSupNorm U V M₀ z
    let delta := M₀ / (U * V)
    let Brect := 4 * mu / delta
    Brect < 1 →
      ((main3LargeAnalyticFixedKeyCellTargetVectorImage
        htheta hY hi key cell).filter fun y ↦
          IsSquare (MvPolynomial.eval y
            (main3LargeAnalyticIntrinsicEliminant
              htheta hY hi key cell data)) ∧
          MvPolynomial.eval y
            (main3LargeAnalyticIntrinsicEliminant
              htheta hY hi key cell data) ≠ 0).card ≤ 2 := by
  dsimp only
  intro hBrect
  have hgeometry := hspec.sieve_geometry
  dsimp only at hgeometry
  rcases hgeometry with
    ⟨_hentry, _hM₀, _hmu, _hdelta, _hmuSq, _hsubset,
      _hA, _hB, hthin, _hfull⟩
  exact (Finset.card_filter_le _ _).trans (hthin hBrect)

/-! ## Full intrinsic residual branch -/

/-- In the full-rectangle branch, the literal intrinsic eliminant satisfies
the square-sieve envelope once the explicit substitution-height threshold is
met.  `hWeil` is the only character-sum input. -/
theorem eventually_card_main3LargeAnalyticFixedKeyCell_intrinsicResidual_filter_le_fullCellEnvelope_of_entryBoundSpec
    (hWeil : OneVariableQuadraticWeilDegreeBound)
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
      ∀ᶠ sieveN : ℕ in atTop,
        main3LargeAnalyticIntrinsicEliminantSieveBudgetThreshold
            data L U V ≤ (sieveN : ℝ) →
          (((T.filter fun y ↦
            IsSquare (MvPolynomial.eval y P) ∧
              MvPolynomial.eval y P ≠ 0).card : ℝ)) ≤
            fullCellOddDegreeSieveEnvelope sieveN d U V M₀ mu := by
  dsimp only
  intro hBrect
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
  have hfull' := hfull hBrect
  rcases hfull' with ⟨harea, hsideA, hsideB⟩
  have hU : 0 < U := by
    dsimp only [U]
    linarith [cert.K_pos]
  have hV : 0 < V := by
    dsimp only [V]
    linarith [cert.C_pos]
  have hM₀pos : 0 < M₀ := zero_lt_one.trans_le hM₀one
  have hT₀ : (1 : ℝ) ≤ T₀ := by
    dsimp only [T₀]
    exact
      one_le_main3LargeAnalyticFixedKeyTargetCoordinateRadius_of_targetImage_nonempty
        htheta hY hi key cell ⟨cert.anchor, cert.anchor_mem⟩
  have hReducedEntry : 0 ≤ reducedSlopeMatrixEntryBound U V M₀ z := by
    unfold reducedSlopeMatrixEntryBound slopeStandardBasisRadius
    positivity
  have hL : 0 ≤ L := by
    dsimp only [L]
    positivity
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
  filter_upwards
    [eventually_fullCell_oddHomogeneousPolynomial_filter_le hWeil]
      with sieveN hsieve
  intro hthreshold
  have hbudgets :=
    main3LargeAnalyticIntrinsicEliminantSieveBudgets_of_threshold_le
      htheta hY hi key cell hcoordinateNonempty hkeyGate data L U V sieveN
        hL hU hV hthreshold
  dsimp only at hbudgets
  exact hsieve U V M₀ mu delta A Brect W T P d HK
    hU hV hM₀pos hmu hdelta hmuSq hhom hodd hHK hcoeff
    hsubset harea hsideA hsideB hA hB hbudgets.1 hbudgets.2

/-! ## Point-fibre consequences -/

/-- The thin target branch contributes at most four residual points after
the exact two-to-one residual composition. -/
theorem card_main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber_cast_le_commonFactor_add_four_of_entryBoundSpec
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N B : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : Main3LargeAnalyticArchimedeanCellIndex)
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
    let rho := cert.ell cert.anchor
    let U := K / 2
    let V := 1 + C / 2
    let M₀ := 2 * rho * V / R
    let beta := cert.ell (fun i ↦ G i 1)
    let z := -K * beta / R
    let mu := firstSlopeSupNorm U V M₀ z
    let delta := M₀ / (U * V)
    let Brect := 4 * mu / delta
    Brect < 1 →
      ((main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
        htheta hY hi key cell).card : ℝ) ≤
        2048 * (B : ℝ) * theta *
            ((shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs.divisors.card : ℝ) +
          4 := by
  dsimp only
  intro hBrect
  have hresidualNat :=
    card_main3LargeAnalyticFixedKeyCell_intrinsicResidual_filter_le_two_of_entryBoundSpec
      htheta hY hi key cell data cert G H hspec hBrect
  have hcomposition :=
    card_main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber_cast_le_commonFactor_add_twice_intrinsicResidual
      htheta hY hi key cell data 2
      (by
        change
          (((main3LargeAnalyticFixedKeyCellTargetVectorImage
            htheta hY hi key cell).filter fun y ↦
              IsSquare (MvPolynomial.eval y
                (main3LargeAnalyticIntrinsicEliminant
                  htheta hY hi key cell data)) ∧
              MvPolynomial.eval y
                (main3LargeAnalyticIntrinsicEliminant
                  htheta hY hi key cell data) ≠ 0).card : ℝ) ≤ 2
        exact_mod_cast hresidualNat)
  convert hcomposition using 1
  all_goals norm_num

/-- In the full target branch, the exact two-to-one residual composition
turns the intrinsic sieve envelope into the corresponding point-fibre bound. -/
theorem eventually_card_main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber_cast_le_commonFactor_add_twice_fullCellEnvelope_of_entryBoundSpec
    (hWeil : OneVariableQuadraticWeilDegreeBound)
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
      ∀ᶠ sieveN : ℕ in atTop,
        main3LargeAnalyticIntrinsicEliminantSieveBudgetThreshold
            data L U V ≤ (sieveN : ℝ) →
          ((main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber
            htheta hY hi key cell).card : ℝ) ≤
            2048 * (B : ℝ) * theta *
                ((shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs.divisors.card : ℝ) +
              2 * fullCellOddDegreeSieveEnvelope sieveN d U V M₀ mu := by
  dsimp only
  intro hBrect
  have hresidualEventually :=
    eventually_card_main3LargeAnalyticFixedKeyCell_intrinsicResidual_filter_le_fullCellEnvelope_of_entryBoundSpec
      hWeil htheta hY hi key cell hcoordinateNonempty hkeyGate data
        cert G H hspec hBrect
  filter_upwards [hresidualEventually] with sieveN hresidual
  intro hthreshold
  have hcomposition :=
    card_main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber_cast_le_commonFactor_add_twice_intrinsicResidual
      htheta hY hi key cell data
      (fullCellOddDegreeSieveEnvelope sieveN
        (main3LargeAnalyticIntrinsicEliminantDegree data)
        (K / 2) (1 + C / 2)
        (2 * cert.ell cert.anchor * (1 + C / 2) / R)
        (firstSlopeSupNorm (K / 2) (1 + C / 2)
          (2 * cert.ell cert.anchor * (1 + C / 2) / R)
          (-K * cert.ell (fun i ↦ G i 1) / R)))
      (by
        change
          (((main3LargeAnalyticFixedKeyCellTargetVectorImage
            htheta hY hi key cell).filter fun y ↦
              IsSquare (MvPolynomial.eval y
                (main3LargeAnalyticIntrinsicEliminant
                  htheta hY hi key cell data)) ∧
              MvPolynomial.eval y
                (main3LargeAnalyticIntrinsicEliminant
                  htheta hY hi key cell data) ≠ 0).card : ℝ) ≤
            fullCellOddDegreeSieveEnvelope sieveN
              (main3LargeAnalyticIntrinsicEliminantDegree data)
              (K / 2) (1 + C / 2)
              (2 * cert.ell cert.anchor * (1 + C / 2) / R)
              (firstSlopeSupNorm (K / 2) (1 + C / 2)
                (2 * cert.ell cert.anchor * (1 + C / 2) / R)
                (-K * cert.ell (fun i ↦ G i 1) / R))
        exact hresidual hthreshold)
  exact hcomposition

end

end PellPaper
