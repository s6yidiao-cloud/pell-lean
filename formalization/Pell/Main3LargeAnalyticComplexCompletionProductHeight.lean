import Pell.Main3LargeAnalyticFixedKeyCellTargetCompletionEntryBoundCover
import Pell.PrimitiveWedgeCompletionSlopeHeight
import Pell.Main3FixedBasisEmbeddingStandardVectorBound
import Pell.Main3LargeAnalyticTargetImageRadiusLogBound
import Mathlib.Tactic

/-!
# Complex-cell completion and product-basis height

This module keeps the exact complex radial certificate and the exact bounded
completion/reduction witnesses supplied by the fixed-cell cover.  It bounds
the actual product-entry ledger even when the short scale `U` is below one,
then supplies the two logarithmic hypotheses consumed by the intrinsic
eliminant uniform-budget theorem.

No sieve or character-sum input is used.
-/

namespace PellPaper

open scoped MatrixGroups ComplexConjugate

noncomputable section

local instance main3LargeAnalyticComplexCompletionProductHeight_numberField
    (a : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

/-! ## Parameter-free numerical ledgers -/

/-- The expanded reduced-slope estimate remains effective with only
`0 < U`; in particular no false unit lower bound on the complex short scale
is imposed. -/
theorem primitiveWedgeProductEntryHeight_le_complexLedger
    (T₀ U V M₀ z A Y : ℝ)
    (hT₀ : 1 ≤ T₀) (hA : 1 ≤ A) (hY : 1 ≤ Y)
    (hU : 0 < U) (hV : 0 < V) (hM₀ : 0 < M₀)
    (hzU : |z| / U ≤ (2 : ℝ) ^ 14 * A ^ 2)
    (honeU : 1 / U ≤ (2 : ℝ) ^ 20 * Y * A ^ 3 / T₀ ^ 2)
    (hUupper : U ≤ T₀ ^ 2)
    (hM₀V : M₀ / V ≤ 2) (hVM₀ : V / M₀ ≤ 1) :
    2 * (T₀ + 1) * reducedSlopeMatrixEntryBound U V M₀ z ≤
      (2 : ℝ) ^ 26 * Y * A ^ 3 * T₀ ^ 3 := by
  let P : ℝ := (2 : ℝ) ^ 20 * Y * A ^ 3
  have hT₀0 : 0 ≤ T₀ := zero_le_one.trans hT₀
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hY0 : 0 ≤ Y := zero_le_one.trans hY
  have hT₀sqOne : (1 : ℝ) ≤ T₀ ^ 2 := by nlinarith
  have hApow : A ^ 2 ≤ A ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg A) (sub_nonneg.mpr hA)]
  have hP0 : 0 ≤ P := by
    dsimp only [P]
    positivity
  have hTwoP : (2 : ℝ) ≤ P := by
    dsimp only [P]
    calc
      (2 : ℝ) ≤ (2 : ℝ) ^ 20 * 1 * 1 ^ 3 := by norm_num
      _ ≤ (2 : ℝ) ^ 20 * Y * A ^ 3 := by gcongr
  have hZP : (2 : ℝ) ^ 14 * A ^ 2 ≤ P := by
    dsimp only [P]
    calc
      (2 : ℝ) ^ 14 * A ^ 2 ≤ (2 : ℝ) ^ 20 * A ^ 2 := by
        gcongr <;> norm_num
      _ ≤ (2 : ℝ) ^ 20 * (Y * A ^ 3) := by
        gcongr
        calc
          A ^ 2 ≤ A ^ 3 := hApow
          _ ≤ Y * A ^ 3 := by
            simpa only [one_mul] using
              mul_le_mul_of_nonneg_right hY (by positivity : 0 ≤ A ^ 3)
      _ = (2 : ℝ) ^ 20 * Y * A ^ 3 := by ring
  have hInvP : (2 : ℝ) ^ 20 * Y * A ^ 3 / T₀ ^ 2 ≤ P := by
    exact div_le_self hP0 hT₀sqOne
  have hsum :
      M₀ / V + |z| / U + 1 / U ≤ 3 * P := by
    calc
      M₀ / V + |z| / U + 1 / U ≤
          2 + ((2 : ℝ) ^ 14 * A ^ 2) +
            ((2 : ℝ) ^ 20 * Y * A ^ 3 / T₀ ^ 2) := by
        gcongr
      _ ≤ P + P + P := by gcongr
      _ = 3 * P := by ring
  have hsecond : U + V / M₀ ≤ 2 * T₀ ^ 2 := by
    calc
      U + V / M₀ ≤ T₀ ^ 2 + 1 := by gcongr
      _ ≤ 2 * T₀ ^ 2 := by nlinarith
  have hexpanded := primitiveWedgeProductEntryHeight_le_expanded
    T₀ U V M₀ z hT₀0 hU hV hM₀
  calc
    2 * (T₀ + 1) * reducedSlopeMatrixEntryBound U V M₀ z ≤
        4 * (T₀ + 1) *
          (M₀ / V + |z| / U + 1 / U) * (U + V / M₀) :=
      hexpanded
    _ ≤ 4 * (2 * T₀) * (3 * P) * (2 * T₀ ^ 2) := by
      gcongr
      nlinarith
    _ ≤ (2 : ℝ) ^ 26 * Y * A ^ 3 * T₀ ^ 3 := by
      dsimp only [P]
      have hnonneg : 0 ≤ Y * A ^ 3 * T₀ ^ 3 := by positivity
      ring_nf
      nlinarith

private theorem log_one_add_productHeight_le_fortynine_mul
    {L T₀ A Y : ℝ}
    (hL0 : 0 ≤ L) (hT₀ : 1 ≤ T₀) (hA : 1 ≤ A) (hY : 1 ≤ Y)
    (hheight : L ≤ (2 : ℝ) ^ 26 * Y * A ^ 3 * T₀ ^ 3)
    (hlogTwo : Real.log 2 ≤ Real.log Y)
    (hlogA : Real.log A ≤ 2 * Real.log Y)
    (hlogT₀ : Real.log T₀ ≤ 5 * Real.log Y) :
    Real.log (L + 1) ≤ 49 * Real.log Y := by
  let P : ℝ := (2 : ℝ) ^ 26 * Y * A ^ 3 * T₀ ^ 3
  have hT₀pos : 0 < T₀ := zero_lt_one.trans_le hT₀
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hYpos : 0 < Y := zero_lt_one.trans_le hY
  have hPpos : 0 < P := by
    dsimp only [P]
    positivity
  have hPone : (1 : ℝ) ≤ P := by
    dsimp only [P]
    calc
      (1 : ℝ) = (1 : ℝ) ^ 26 * 1 * 1 ^ 3 * 1 ^ 3 := by norm_num
      _ ≤ (2 : ℝ) ^ 26 * Y * A ^ 3 * T₀ ^ 3 := by
        gcongr
        norm_num
  have hLP : L + 1 ≤ 2 * P := by
    dsimp only [P] at hheight ⊢
    linarith
  have hlog := Real.log_le_log (by linarith) hLP
  have hlogP :
      Real.log P = 26 * Real.log 2 + Real.log Y +
        3 * Real.log A + 3 * Real.log T₀ := by
    dsimp only [P]
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_pow]
    norm_num
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hPpos.ne', hlogP] at hlog
  linarith

private theorem log_four_mul_add_le_eleven_mul
    {U V T₀ Y : ℝ}
    (hU : 0 < U) (hV : V = 2) (hUupper : U ≤ T₀ ^ 2)
    (hT₀ : 1 ≤ T₀) (hY : 1 ≤ Y)
    (hlogT₀ : Real.log T₀ ≤ 5 * Real.log Y)
    (hlogTwelve : Real.log 12 ≤ Real.log Y) :
    Real.log (4 * (U + V)) ≤ 11 * Real.log Y := by
  have hT₀pos : 0 < T₀ := zero_lt_one.trans_le hT₀
  have hYpos : 0 < Y := zero_lt_one.trans_le hY
  have hT₀sqOne : (1 : ℝ) ≤ T₀ ^ 2 := by nlinarith
  have hargPos : 0 < 4 * (U + V) := by rw [hV]; positivity
  have hupper : 4 * (U + V) ≤ 12 * T₀ ^ 2 := by
    rw [hV]
    nlinarith
  have hlog := Real.log_le_log hargPos hupper
  rw [Real.log_mul (by norm_num : (12 : ℝ) ≠ 0)
      (pow_ne_zero 2 hT₀pos.ne'), Real.log_pow] at hlog
  norm_num at hlog
  linarith

/-! ## The concrete complex branch -/

/-- The complex fixed-cell cover can be chosen with one and the same radial
certificate, bounded completion `G`, reduced factor `H`, product basis
`W = G * H`, and the two logarithmic budgets required by the uniform
intrinsic-eliminant ledger.  The displayed height is the literal entry bound
already occurring in the cover specification. -/
theorem exists_main3LargeAnalyticFixedKeyComplexCellTargetCompletionEntryBoundCover_with_productHeight
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : ComplexUnitCircleSlopeCellIndex)
    (ha : 0 < shiftedSquareA h v)
    (hnonempty :
      (main3LargeAnalyticFixedKeyCellTargetVectorImage
        htheta hY hi key (Sum.inr cell)).Nonempty) :
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    let F := shiftedSquareFixedExplicitIntegralBasisData
      (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
    let sigma := shiftedSquareImaginaryPlaceEmbedding
      (shiftedSquareA h v) ha
    let T := main3LargeAnalyticFixedKeyCellTargetVectorImage
      htheta hY hi key (Sum.inr cell)
    let E := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
    let Delta := Real.sqrt
      |(NumberField.discr
        (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ)|
    let Mmesh := (main3UnbalancedM theta Y : ℝ)
    let K := (6 * E / Mmesh) / Delta
    let T₀ := main3LargeAnalyticFixedKeyTargetCoordinateRadius
      (shiftedSquareA h v) Y key
    ∃ cert : PrimitiveWedgeReducedTargetCoverCertificate T E K 2,
      cert.ell = main3AnchorHermitianRadialAddHom
        1 (sigma F.omega) cert.anchor ∧
      E ≤ 2 * cert.ell cert.anchor ∧
      cert.ell cert.anchor ≤ E ∧
      (let rho := cert.ell cert.anchor
       let U := K / 2
       let V := 1 + (2 : ℝ) / 2
       let M₀ := 2 * rho * V / E
       V = 2 ∧
       M₀ = 4 * rho / E ∧
       2 ≤ M₀ ∧ M₀ ≤ 4 ∧
       4 * (U + V) = 2 * K + 8 ∧
       36 * 2 * K = 432 * E / (Mmesh * Delta)) ∧
      ∃ G H : SL(2, ℤ),
        PrimitiveWedgeReducedTargetCoverCompletionEntryBoundSpec
          T cert.ell cert.anchor E K 2 T₀ G H ∧
        (let rho := cert.ell cert.anchor
         let U := K / 2
         let V := 1 + (2 : ℝ) / 2
         let M₀ := 2 * rho * V / E
         let beta := cert.ell (fun i ↦ G i 1)
         let z := -K * beta / E
         let L := 2 * (T₀ + 1) *
           reducedSlopeMatrixEntryBound U V M₀ z
         L ≤ (2 : ℝ) ^ 26 * (Y : ℝ) *
              |(shiftedSquareA h v : ℝ)| ^ 3 * T₀ ^ 3 ∧
         Real.log (L + 1) ≤ 64 * Real.log (Y : ℝ) ∧
         Real.log (4 * (U + V)) ≤ 12 * Real.log (Y : ℝ)) := by
  dsimp only
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let F := shiftedSquareFixedExplicitIntegralBasisData
    (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
  let sigma := shiftedSquareImaginaryPlaceEmbedding
    (shiftedSquareA h v) ha
  let T := main3LargeAnalyticFixedKeyCellTargetVectorImage
    htheta hY hi key (Sum.inr cell)
  let E := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
  let Delta := Real.sqrt
    |(NumberField.discr
      (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ)|
  let Mmesh := (main3UnbalancedM theta Y : ℝ)
  let K := (6 * E / Mmesh) / Delta
  let T₀ := main3LargeAnalyticFixedKeyTargetCoordinateRadius
    (shiftedSquareA h v) Y key
  obtain ⟨cert, hell, hrhoLower, hrhoUpper, hcalibration, G, H, hspec⟩ :=
    exists_main3LargeAnalyticFixedKeyComplexCellTargetCompletionEntryBoundCover
      htheta hY hi key cell ha hnonempty
  refine ⟨cert, ?_, ?_, ?_, ?_, G, H, ?_, ?_⟩
  · simpa only [F, sigma] using hell
  · simpa only [E] using hrhoLower
  · simpa only [E] using hrhoUpper
  · simpa only [E, K, Mmesh, Delta] using hcalibration
  · simpa only [T, E, K, T₀] using hspec
  · let A := |(shiftedSquareA h v : ℝ)|
    let rho := cert.ell cert.anchor
    let U := K / 2
    let V := 1 + (2 : ℝ) / 2
    let M₀ := 2 * rho * V / E
    let beta := cert.ell (fun i ↦ G i 1)
    let z := -K * beta / E
    let L := 2 * (T₀ + 1) * reducedSlopeMatrixEntryBound U V M₀ z
    have ha0 : shiftedSquareA h v ≠ 0 := ne_of_gt ha
    have hA : (1 : ℝ) ≤ A := by
      dsimp only [A]
      exact_mod_cast Int.one_le_abs ha0
    have hA0 : 0 ≤ A := zero_le_one.trans hA
    have hApos : 0 < A := zero_lt_one.trans_le hA
    have hsqrtAOne : (1 : ℝ) ≤ Real.sqrt A :=
      Real.one_le_sqrt.mpr hA
    have hsqrtAleA : Real.sqrt A ≤ A := by
      have hsqrt0 := Real.sqrt_nonneg A
      have hsqrtSq := Real.sq_sqrt hA0
      nlinarith [mul_nonneg hsqrt0 (sub_nonneg.mpr hsqrtAOne)]
    have hYone : (1 : ℝ) ≤ (Y : ℝ) := by
      exact_mod_cast (show 1 ≤ Y by omega)
    have hYpos : (0 : ℝ) < (Y : ℝ) := zero_lt_one.trans_le hYone
    have hlogY0 : 0 ≤ Real.log (Y : ℝ) := Real.log_nonneg hYone
    have hE : 0 < E := cert.R_pos
    have hsqrtEpos : 0 < Real.sqrt E := Real.sqrt_pos.2 hE
    have hT₀ : (1 : ℝ) ≤ T₀ := by
      dsimp only [T₀]
      exact
        one_le_main3LargeAnalyticFixedKeyTargetCoordinateRadius_of_targetImage_nonempty
          htheta hY hi key (Sum.inr cell) hnonempty
    have hT₀pos : 0 < T₀ := zero_lt_one.trans_le hT₀
    have hT₀Eq : T₀ = 1024 * A * Real.sqrt E := by
      dsimp only [T₀, A, E]
      unfold main3LargeAnalyticFixedKeyTargetCoordinateRadius
        shiftedSquareRawCoordinateScaleLoss
      ring
    have hT₀SqEq : T₀ ^ 2 = (2 : ℝ) ^ 20 * A ^ 2 * E := by
      rw [hT₀Eq]
      calc
        (1024 * A * Real.sqrt E) ^ 2 =
            1024 ^ 2 * A ^ 2 * (Real.sqrt E) ^ 2 := by ring
        _ = (2 : ℝ) ^ 20 * A ^ 2 * E := by
          rw [Real.sq_sqrt hE.le]
          norm_num
    have hMmeshLower : (6 : ℝ) ≤ Mmesh := by
      dsimp only [Mmesh]
      exact_mod_cast six_le_main3UnbalancedM htheta hY
    have hMmeshPos : 0 < Mmesh := lt_of_lt_of_le (by norm_num) hMmeshLower
    have hMmeshUpper : Mmesh ≤ (Y : ℝ) := by
      dsimp only [Mmesh]
      exact_mod_cast
        (main3UnbalancedM_parameter_package theta Y htheta
          (by omega : 2 ≤ Y)).2.1
    have hdiscLowerZ :=
      abs_le_abs_rationalQuadraticAlgebra_neg_fieldDiscriminant_of_squarefree
        (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
    have hdiscLower : A ≤
        |(NumberField.discr
          (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ)| := by
      dsimp only [A]
      exact_mod_cast hdiscLowerZ
    have hDeltaLower : Real.sqrt A ≤ Delta := by
      dsimp only [Delta]
      exact Real.sqrt_le_sqrt hdiscLower
    have hDeltaOne : (1 : ℝ) ≤ Delta := hsqrtAOne.trans hDeltaLower
    have hDeltaPos : 0 < Delta := zero_lt_one.trans_le hDeltaOne
    have hDeltaUpper : Delta ≤ 2 * Real.sqrt A := by
      simpa only [Delta, A] using
        sqrt_abs_rationalQuadraticAlgebra_neg_fieldDiscriminant_le
          (shiftedSquareA h v)
    have hDeltaThreeA : Delta ≤ 3 * A := by
      calc
        Delta ≤ 2 * Real.sqrt A := hDeltaUpper
        _ ≤ 2 * A := by gcongr
        _ ≤ 3 * A := by nlinarith
    have hcal :
        V = 2 ∧ M₀ = 4 * rho / E ∧
          2 ≤ M₀ ∧ M₀ ≤ 4 ∧
          4 * (U + V) = 2 * K + 8 ∧
          36 * 2 * K = 432 * E / (Mmesh * Delta) := by
      simpa only [rho, U, V, M₀, E, K, Mmesh, Delta] using hcalibration
    have hVeq : V = 2 := hcal.1
    have hM₀Lower : (2 : ℝ) ≤ M₀ := hcal.2.2.1
    have hM₀Upper : M₀ ≤ 4 := hcal.2.2.2.1
    have hM₀Pos : 0 < M₀ := lt_of_lt_of_le (by norm_num) hM₀Lower
    have hM₀V : M₀ / V ≤ 2 := by
      rw [hVeq]
      linarith
    have hVM₀ : V / M₀ ≤ 1 := by
      rw [hVeq]
      exact (div_le_iff₀ hM₀Pos).2 (by simpa using hM₀Lower)
    have hUEq : U = 3 * E / (Mmesh * Delta) := by
      dsimp only [U, K]
      field_simp [hMmeshPos.ne', hDeltaPos.ne']
      ring
    have hMDelta : (6 : ℝ) ≤ Mmesh * Delta := by
      calc
        (6 : ℝ) = 6 * 1 := by ring
        _ ≤ Mmesh * Delta :=
          mul_le_mul hMmeshLower hDeltaOne (by norm_num) hMmeshPos.le
    have hUHalf : U ≤ E / 2 := by
      rw [hUEq]
      apply (div_le_iff₀ (mul_pos hMmeshPos hDeltaPos)).2
      calc
        3 * E = (E / 2) * 6 := by ring
        _ ≤ (E / 2) * (Mmesh * Delta) := by
          exact mul_le_mul_of_nonneg_left hMDelta (by positivity)
    have hEHalfT₀ : E / 2 ≤ T₀ ^ 2 := by
      rw [hT₀SqEq]
      have hcoeff : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ 20 * A ^ 2 := by
        nlinarith [sq_nonneg A]
      calc
        E / 2 = (1 / 2 : ℝ) * E := by ring
        _ ≤ ((2 : ℝ) ^ 20 * A ^ 2) * E :=
          mul_le_mul_of_nonneg_right hcoeff hE.le
        _ = (2 : ℝ) ^ 20 * A ^ 2 * E := by ring
    have hUupper : U ≤ T₀ ^ 2 := hUHalf.trans hEHalfT₀
    have hrhoEq : rho =
        ‖main3IntegralTargetLinearForm (sigma F.omega) cert.anchor‖ ^ 2 := by
      dsimp only [rho]
      rw [hell]
      simpa only [one_mul] using
        main3AnchorHermitianRadialAddHom_self
          1 (sigma F.omega) cert.anchor
    have hanchorSq :
        ‖main3IntegralTargetLinearForm (sigma F.omega) cert.anchor‖ ^ 2 ≤ E := by
      rw [← hrhoEq]
      exact hrhoUpper
    have hanchorNorm :
        ‖main3IntegralTargetLinearForm (sigma F.omega) cert.anchor‖ ≤
          Real.sqrt E := by
      have hnorm0 := norm_nonneg
        (main3IntegralTargetLinearForm (sigma F.omega) cert.anchor)
      have hsqrt0 := Real.sqrt_nonneg E
      have hsqrtSq := Real.sq_sqrt hE.le
      nlinarith
    have hellStandard : ∀ i,
        |cert.ell (Pi.single i (1 : ℤ))| ≤
          2 * Real.sqrt A * Real.sqrt E := by
      intro i
      have hcauchy :=
        abs_main3AnchorHermitianRadialAddHom_le_of_nonneg
          (by norm_num : (0 : ℝ) ≤ 1) (sigma F.omega) cert.anchor
            (Pi.single i (1 : ℤ))
      have hstandard :=
        norm_main3IntegralTargetLinearForm_standardVector_le_two_mul_sqrt_abs
          ha0 F sigma i
      rw [hell]
      calc
        |main3AnchorHermitianRadialAddHom 1 (sigma F.omega) cert.anchor
            (Pi.single i (1 : ℤ))| ≤
            ‖main3IntegralTargetLinearForm (sigma F.omega) cert.anchor‖ *
              ‖main3IntegralTargetLinearForm (sigma F.omega)
                (Pi.single i (1 : ℤ))‖ := by
          simpa only [one_mul] using hcauchy
        _ ≤ Real.sqrt E * (2 * Real.sqrt A) := by
          exact mul_le_mul hanchorNorm hstandard (norm_nonneg _)
            (Real.sqrt_nonneg E)
        _ = 2 * Real.sqrt A * Real.sqrt E := by ring
    have hGentry : ∀ i j, |((G i j : ℤ) : ℝ)| ≤ T₀ + 1 := hspec.1
    have hbeta : |beta| ≤
        4 * (T₀ + 1) * Real.sqrt A * Real.sqrt E := by
      have h := abs_addHom_sl2_column_le cert.ell G (T₀ + 1)
        (2 * Real.sqrt A * Real.sqrt E) (by linarith) hGentry
          hellStandard 1
      simpa only [beta] using (h.trans_eq (by ring))
    have hU : 0 < U := by
      dsimp only [U]
      exact div_pos cert.K_pos (by norm_num)
    have hzUEq : |z| / U = 2 * |beta| / E := by
      have hKne : K ≠ 0 := by exact ne_of_gt cert.K_pos
      have hcancel : (K * |beta| / E) / (K / 2) = 2 * |beta| / E := by
        field_simp [hKne, hE.ne']
      dsimp only [z, U]
      rw [abs_div, abs_mul, abs_neg, abs_of_pos cert.K_pos,
        abs_of_pos hE]
      exact hcancel
    have hzU : |z| / U ≤ (2 : ℝ) ^ 14 * A ^ 2 := by
      rw [hzUEq]
      apply (div_le_iff₀ hE).2
      calc
        2 * |beta| ≤
            2 * (4 * (T₀ + 1) * Real.sqrt A * Real.sqrt E) := by
          gcongr
        _ = 8 * (T₀ + 1) * Real.sqrt A * Real.sqrt E := by ring
        _ ≤ 8 * (2 * T₀) * Real.sqrt A * Real.sqrt E := by
          gcongr
          linarith
        _ = 16 * T₀ * Real.sqrt A * Real.sqrt E := by ring
        _ = (2 : ℝ) ^ 14 * A * Real.sqrt A * E := by
          rw [hT₀Eq]
          calc
            16 * (1024 * A * Real.sqrt E) * Real.sqrt A * Real.sqrt E =
                (2 : ℝ) ^ 14 * A * Real.sqrt A *
                  (Real.sqrt E) ^ 2 := by norm_num; ring
            _ = (2 : ℝ) ^ 14 * A * Real.sqrt A * E := by
              rw [Real.sq_sqrt hE.le]
        _ ≤ (2 : ℝ) ^ 14 * A ^ 2 * E := by
          have hleft :
              (2 : ℝ) ^ 14 * A * Real.sqrt A ≤
                (2 : ℝ) ^ 14 * A * A :=
            mul_le_mul_of_nonneg_left hsqrtAleA (by positivity)
          have := mul_le_mul_of_nonneg_right hleft hE.le
          calc
            (2 : ℝ) ^ 14 * A * Real.sqrt A * E ≤
                (2 : ℝ) ^ 14 * A * A * E := this
            _ = (2 : ℝ) ^ 14 * A ^ 2 * E := by ring
    have hInvUEq : 1 / U = Mmesh * Delta / (3 * E) := by
      rw [hUEq]
      field_simp [hMmeshPos.ne', hDeltaPos.ne', hE.ne']
    have hInvUTargetEq :
        (2 : ℝ) ^ 20 * (Y : ℝ) * A ^ 3 / T₀ ^ 2 =
          (Y : ℝ) * A / E := by
      rw [hT₀SqEq]
      field_simp [hApos.ne', hE.ne']
    have hMDeltaThird : Mmesh * Delta / 3 ≤ (Y : ℝ) * A := by
      calc
        Mmesh * Delta / 3 ≤ (Y : ℝ) * (3 * A) / 3 := by
          gcongr
        _ = (Y : ℝ) * A := by ring
    have honeU : 1 / U ≤
        (2 : ℝ) ^ 20 * (Y : ℝ) * A ^ 3 / T₀ ^ 2 := by
      calc
        1 / U = Mmesh * Delta / (3 * E) := hInvUEq
        _ = (Mmesh * Delta / 3) / E := by ring
        _ ≤ ((Y : ℝ) * A) / E :=
          div_le_div_of_nonneg_right hMDeltaThird hE.le
        _ = (2 : ℝ) ^ 20 * (Y : ℝ) * A ^ 3 / T₀ ^ 2 :=
          hInvUTargetEq.symm
    have hheight : L ≤
        (2 : ℝ) ^ 26 * (Y : ℝ) * A ^ 3 * T₀ ^ 3 := by
      dsimp only [L]
      exact primitiveWedgeProductEntryHeight_le_complexLedger
        T₀ U V M₀ z A (Y : ℝ) hT₀ hA hYone hU
          (by rw [hVeq]; norm_num) hM₀Pos hzU honeU hUupper hM₀V hVM₀
    have hReducedEntry : 0 ≤ reducedSlopeMatrixEntryBound U V M₀ z := by
      unfold reducedSlopeMatrixEntryBound slopeStandardBasisRadius
      positivity
    have hL0 : 0 ≤ L := by
      dsimp only [L]
      positivity
    have hlogA : Real.log A ≤ 2 * Real.log (Y : ℝ) := by
      dsimp only [A]
      exact main3LargeAnalytic_log_abs_shift_le_two_mul_log htheta hY hi
    have hlogT₀ : Real.log T₀ ≤ 5 * Real.log (Y : ℝ) := by
      dsimp only [T₀]
      exact log_main3LargeAnalyticFixedKeyTargetCoordinateRadius_le_five_mul
        htheta hY hi key (Sum.inr cell) hnonempty
    have hlogTwo : Real.log 2 ≤ Real.log (Y : ℝ) :=
      Real.log_le_log (by norm_num) (by
        exact_mod_cast (show 2 ≤ Y by omega))
    have hlogTwelve : Real.log 12 ≤ Real.log (Y : ℝ) :=
      Real.log_le_log (by norm_num) (by
        exact_mod_cast (show 12 ≤ Y by omega))
    have hlogL49 : Real.log (L + 1) ≤ 49 * Real.log (Y : ℝ) :=
      log_one_add_productHeight_le_fortynine_mul hL0 hT₀ hA hYone
        hheight hlogTwo hlogA hlogT₀
    have hlogUV11 : Real.log (4 * (U + V)) ≤
        11 * Real.log (Y : ℝ) :=
      log_four_mul_add_le_eleven_mul hU hVeq hUupper hT₀ hYone
        hlogT₀ hlogTwelve
    have hlogL64 : Real.log (L + 1) ≤ 64 * Real.log (Y : ℝ) := by
      linarith
    have hlogUV12 : Real.log (4 * (U + V)) ≤
        12 * Real.log (Y : ℝ) := by
      linarith
    simpa only [A, rho, U, V, M₀, beta, z, L] using
      (show L ≤ (2 : ℝ) ^ 26 * (Y : ℝ) * A ^ 3 * T₀ ^ 3 ∧
          Real.log (L + 1) ≤ 64 * Real.log (Y : ℝ) ∧
          Real.log (4 * (U + V)) ≤ 12 * Real.log (Y : ℝ) from
        ⟨hheight, hlogL64, hlogUV12⟩)

end

end PellPaper
