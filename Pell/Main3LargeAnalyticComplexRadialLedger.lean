import Pell.Main3ComplexRateBridge
import Pell.Main3LargeAnalyticComplexRadialDiscriminantCost
import Pell.Main3UnbalancedEnlargedDirectActiveBlockBound
import Pell.ShiftedSquareFieldDiscriminantLowerBound
import Mathlib.Tactic

/-!
# The actual fixed-key complex radial logarithmic ledger

This module converts the exact radial/discriminant factor on a selected
fixed-key complex cell into the exponential logarithmic budget consumed by
the checked complex fan/rate bridge.  It derives the key positivity and
normalization bounds from one selected image row, proves the required
large-analytic endpoint comparison, and combines source, target, and field
discriminant logarithms with their exact bidegree multiplicities.

No fan is selected and no determinant is declared zero here.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- A selected full row family makes the cell image nonempty, so its fixed
key is the key of one genuine normalized package. -/
theorem main3LargeAnalytic_selectedComplexCell_key_scale_package
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N B : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : ComplexUnitCircleSlopeCellIndex)
    (s : generalBidegreeFormIndex 1 B ↪
      {z // z ∈
        main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
          htheta hY hi key (Sum.inr cell)}) :
    (0 : ℝ) < key.C₀ ∧
      (key.C₀ : ℝ) ≤ 32 * Real.sqrt |(shiftedSquareA h v : ℝ)| ∧
      (1 : ℝ) ≤ key.r ∧ (1 : ℝ) ≤ key.ell := by
  let r0 : generalBidegreeFormIndex 1 B :=
    (⟨0, by omega⟩, ⟨0, by omega⟩)
  have hz := (s r0).2
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  obtain ⟨p, hp, hkey, _hcell, _hgeometry, _hcode, _hzPoint⟩ :=
    main3LargeAnalytic_blockCellCoordinatePointImage_sameCertificate
      htheta hY hi hz
  let C := main3LargeAnalytic_blockFixedBasisEncodingCertificate
    htheta (by omega : 8 ≤ Y) hi p
  have hC0pos : 0 < C.P.minkowski.C₀ := C.P.minkowski.C₀_pos
  have hC0 := C.scaled.C₀_le_thirtytwo_mul_sqrt_abs
  have hr : 0 < C.P.r := C.P.r_pos
  have hell : 0 < C.P.ell := C.P.ell_pos
  rw [← hkey]
  exact ⟨by exact_mod_cast hC0pos, hC0,
    by exact_mod_cast hr, by exact_mod_cast hell⟩

/-- Every active large-analytic endpoint lies beyond the elementary threshold
`4Y ≤ N²` used by the source-scale comparison. -/
theorem main3LargeAnalytic_four_mul_base_le_endpoint_sq
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y) :
    4 * Y ≤ N ^ 2 := by
  have hiLarge :=
    mem_main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices.mp hi
  have hthetaSqPos : 0 < theta ^ 2 := by positivity
  have hexponent :
      (1 : ℝ) ≤ (3 : ℝ) / 2 - 1 / (32 * theta ^ 2) := by
    field_simp [hthetaSqPos.ne']
    nlinarith [sq_nonneg (theta - 3)]
  have hYone : (1 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast (by omega : 1 ≤ Y)
  have hYThreshold : (Y : ℝ) ≤
      main3UnbalancedEnlargedDirectNThreshold theta Y := by
    calc
      (Y : ℝ) = (Y : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (Y : ℝ) ^ ((3 : ℝ) / 2 - 1 / (32 * theta ^ 2)) :=
        Real.rpow_le_rpow_of_exponent_le hYone hexponent
      _ = main3UnbalancedEnlargedDirectNThreshold theta Y := rfl
  have hYNreal : (Y : ℝ) < (N : ℝ) := hYThreshold.trans_lt hiLarge.2
  have hYN : Y ≤ N := by exact_mod_cast hYNreal.le
  calc
    4 * Y ≤ Y * Y := by nlinarith
    _ ≤ N * N := Nat.mul_le_mul hYN hYN
    _ = N ^ 2 := by ring

/-- The source dyadic scale has the exact balanced logarithmic budget, with
the retained endpoint-doubling `log 4` slack. -/
theorem main3LargeAnalytic_log_source_dyadic_le_balanced_base
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y) :
    Real.log (D : ℝ) ≤
      (Real.log (N : ℝ) / Real.log (Y : ℝ) - 1 / 2) *
          Real.log (Y : ℝ) + Real.log 4 := by
  have hiLarge :=
    mem_main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices.mp hi
  obtain ⟨hiBroad, hcell⟩ :=
    mem_main3UnbalancedEnlargedActiveDyadicCoverIndices.mp hiLarge.1
  have hendpoints :=
    nonempty_main3UnbalancedEnlargedShiftedSquareCell_endpoint_height_package
      htheta (by omega : 2 ≤ Y) hiBroad hcell
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hendpoints.1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hendpoints.2.1
  have hYpos : (0 : ℝ) < Y := by positivity
  have hsqrtYpos : 0 < Real.sqrt (Y : ℝ) := Real.sqrt_pos.2 hYpos
  have hlarge := main3LargeAnalytic_four_mul_base_le_endpoint_sq
    htheta hY hi
  have hlinear :=
    nonempty_main3UnbalancedEnlargedShiftedSquareCell_largeN_linear_comparability
      htheta (by omega : 2 ≤ Y) hiBroad hcell hlarge
  have hsqrtFive : Real.sqrt (5 : ℝ) ≤ 4 := by
    have hsquare : Real.sqrt (5 : ℝ) ^ 2 = 5 :=
      Real.sq_sqrt (by norm_num)
    have hnonneg := Real.sqrt_nonneg (5 : ℝ)
    nlinarith
  have hsqrtFiveN : Real.sqrt 5 * (N : ℝ) ≤ 4 * (N : ℝ) :=
    mul_le_mul_of_nonneg_right hsqrtFive hNpos.le
  have hscaled : (D : ℝ) * Real.sqrt (Y : ℝ) ≤ 4 * (N : ℝ) :=
    hlinear.2.trans hsqrtFiveN
  have hDupper : (D : ℝ) ≤ 4 * (N : ℝ) / Real.sqrt (Y : ℝ) :=
    (le_div_iff₀ hsqrtYpos).2 hscaled
  have hlog := Real.log_le_log hDpos hDupper
  rw [Real.log_div (by positivity : 4 * (N : ℝ) ≠ 0) hsqrtYpos.ne',
    Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hNpos.ne',
    Real.log_sqrt hYpos.le] at hlog
  have hlogYpos : 0 < Real.log (Y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
  have hcancel :
      Real.log (N : ℝ) / Real.log (Y : ℝ) * Real.log (Y : ℝ) =
        Real.log (N : ℝ) := div_mul_cancel₀ _ hlogYpos.ne'
  rw [sub_mul, hcancel]
  linarith

/-- Logarithmic source-scale bound after the fixed-key `C₀,r` estimates. -/
theorem log_main3LargeAnalyticFixedKeySourceScaleUpper_le
    {D : ℕ} {a : ℤ} {key : ShiftedSquareAuxiliaryKey}
    (hD : 0 < D) (ha : 0 < a)
    (hC0pos : (0 : ℝ) < key.C₀)
    (hC0 : (key.C₀ : ℝ) ≤ 32 * Real.sqrt |(a : ℝ)|)
    (hr : (1 : ℝ) ≤ key.r) :
    Real.log (main3LargeAnalyticFixedKeySourceScaleUpper D key) ≤
      Real.log (D : ℝ) + Real.log 64 + Real.log |(a : ℝ)| / 2 := by
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hD
  have haReal : (0 : ℝ) < a := by exact_mod_cast ha
  have habspos : 0 < |(a : ℝ)| := abs_pos.mpr haReal.ne'
  have hsqrtpos : 0 < Real.sqrt |(a : ℝ)| := Real.sqrt_pos.2 habspos
  have hrpos : (0 : ℝ) < key.r := zero_lt_one.trans_le hr
  have hlogC0 := Real.log_le_log hC0pos hC0
  rw [Real.log_mul (by norm_num : (32 : ℝ) ≠ 0) hsqrtpos.ne',
    Real.log_sqrt habspos.le] at hlogC0
  rw [abs_of_pos haReal] at hlogC0
  have hlogr : 0 ≤ Real.log (key.r : ℝ) := Real.log_nonneg hr
  have hlog64 : Real.log 64 = Real.log 2 + Real.log 32 := by
    rw [show (64 : ℝ) = 2 * 32 by norm_num,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
        (by norm_num : (32 : ℝ) ≠ 0)]
  unfold main3LargeAnalyticFixedKeySourceScaleUpper
  rw [Real.log_div (by positivity :
      2 * (D : ℝ) * (key.C₀ : ℝ) ≠ 0) (pow_ne_zero 2 hrpos.ne'),
    Real.log_mul (by positivity : 2 * (D : ℝ) ≠ 0) hC0pos.ne',
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hDreal.ne',
    Real.log_pow]
  rw [hlog64]
  norm_num
  linarith

/-- Logarithmic target-scale bound after the fixed-key `C₀,ell` estimates. -/
theorem log_main3LargeAnalyticFixedKeyTargetScaleUpper_le
    {Y : ℕ} {a : ℤ} {key : ShiftedSquareAuxiliaryKey}
    (hY : 0 < Y) (ha : 0 < a)
    (hC0pos : (0 : ℝ) < key.C₀)
    (hC0 : (key.C₀ : ℝ) ≤ 32 * Real.sqrt |(a : ℝ)|)
    (hell : (1 : ℝ) ≤ key.ell) :
    Real.log (main3LargeAnalyticFixedKeyTargetScaleUpper Y key) ≤
      Real.log (Y : ℝ) + Real.log 2048 + Real.log |(a : ℝ)| := by
  have hYreal : (0 : ℝ) < Y := by exact_mod_cast hY
  have haReal : (0 : ℝ) < a := by exact_mod_cast ha
  have habspos : 0 < |(a : ℝ)| := abs_pos.mpr haReal.ne'
  have hsqrtpos : 0 < Real.sqrt |(a : ℝ)| := Real.sqrt_pos.2 habspos
  have hellpos : (0 : ℝ) < key.ell := zero_lt_one.trans_le hell
  have hlogC0 := Real.log_le_log hC0pos hC0
  rw [Real.log_mul (by norm_num : (32 : ℝ) ≠ 0) hsqrtpos.ne',
    Real.log_sqrt habspos.le] at hlogC0
  rw [abs_of_pos haReal] at hlogC0
  have hlogell : 0 ≤ Real.log (key.ell : ℝ) := Real.log_nonneg hell
  have hlog2048 : Real.log 2048 = Real.log 2 + 2 * Real.log 32 := by
    rw [show (2048 : ℝ) = 2 * 32 ^ (2 : ℕ) by norm_num,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
        (by norm_num : (32 : ℝ) ^ (2 : ℕ) ≠ 0), Real.log_pow]
    norm_num
  unfold main3LargeAnalyticFixedKeyTargetScaleUpper
  rw [Real.log_div (by positivity :
      2 * (Y : ℝ) * (key.C₀ : ℝ) ^ 2 ≠ 0)
        (pow_ne_zero 2 hellpos.ne'),
    Real.log_mul (by positivity : 2 * (Y : ℝ) ≠ 0)
      (pow_ne_zero 2 hC0pos.ne'),
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hYreal.ne',
    Real.log_pow, Real.log_pow]
  rw [hlog2048]
  norm_num
  linarith

/-- The selected radial product divided by the exact field-discriminant
factor is bounded by the complete exponential radial ledger.  The residual
shift coefficient is exactly `B(B+1)/2`. -/
theorem main3LargeAnalytic_complexCellCoordinatePointImage_selectedRadialDiscriminantCostFactor_le_exp_radialLedger
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N B : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (ha : 0 < shiftedSquareA h v)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : ComplexUnitCircleSlopeCellIndex)
    (s : generalBidegreeFormIndex 1 B ↪
      {z // z ∈
        main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
          htheta hY hi key (Sum.inr cell)}) :
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    let F := shiftedSquareFixedExplicitIntegralBasisData
      (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
    let sigma := shiftedSquareImaginaryPlaceEmbedding
      (shiftedSquareA h v) ha
    main3ComplexSelectedRadialDiscriminantCostFactor
        B F sigma (fun z => z.1) s ≤
      Real.exp
        (twoLayerBalancedDoubledBaseLogCost B
            (Real.log (N : ℝ) / Real.log (Y : ℝ))
            (Real.log (Y : ℝ)) +
          ((B : ℝ) * ((B : ℝ) + 1) / 2) *
            Real.log |(shiftedSquareA h v : ℝ)| +
          main3ComplexRadialFixedLogCost B) := by
  dsimp only
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let _ : NumberField
      (rationalQuadraticAlgebra (-(shiftedSquareA h v))) :=
    rationalQuadraticAlgebra_numberField (-(shiftedSquareA h v))
  let F := shiftedSquareFixedExplicitIntegralBasisData
    (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
  let sigma := shiftedSquareImaginaryPlaceEmbedding
    (shiftedSquareA h v) ha
  let EA := main3LargeAnalyticFixedKeySourceScaleUpper D key
  let EG := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
  let Delta : ℝ :=
    |(NumberField.discr
      (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ)|
  let p : ℝ := ((((B + 1) ^ 2 : ℕ) : ℝ)) / 2
  let raw : ℝ := EA ^ (B + 1) * EG ^ (B * (B + 1)) /
    Real.rpow Delta p
  have hkey := main3LargeAnalytic_selectedComplexCell_key_scale_package
    htheta hY hi key cell s
  have hiLarge :=
    mem_main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices.mp hi
  obtain ⟨hiBroad, hcell⟩ :=
    mem_main3UnbalancedEnlargedActiveDyadicCoverIndices.mp hiLarge.1
  have hendpoints :=
    nonempty_main3UnbalancedEnlargedShiftedSquareCell_endpoint_height_package
      htheta (by omega : 2 ≤ Y) hiBroad hcell
  have hDposNat : 0 < D := hendpoints.1
  have hNposNat : 0 < N := hendpoints.2.1
  have hYposNat : 0 < Y := by omega
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hDposNat
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hNposNat
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast hYposNat
  have haReal : (0 : ℝ) < shiftedSquareA h v := by exact_mod_cast ha
  have habspos : 0 < |(shiftedSquareA h v : ℝ)| := abs_pos.mpr haReal.ne'
  have hEApos : 0 < EA := by
    dsimp [EA, main3LargeAnalyticFixedKeySourceScaleUpper]
    exact div_pos
      (mul_pos (mul_pos (by norm_num) hDpos) hkey.1)
      (pow_pos (zero_lt_one.trans_le hkey.2.2.1) 2)
  have hEGpos : 0 < EG := by
    dsimp [EG, main3LargeAnalyticFixedKeyTargetScaleUpper]
    exact div_pos
      (mul_pos (mul_pos (by norm_num) hYpos) (pow_pos hkey.1 2))
      (pow_pos (zero_lt_one.trans_le hkey.2.2.2) 2)
  have hDeltaLowerNat :=
    abs_le_abs_rationalQuadraticAlgebra_neg_fieldDiscriminant_of_squarefree
      (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
  have hDeltaLower : |(shiftedSquareA h v : ℝ)| ≤ Delta := by
    dsimp [Delta]
    exact_mod_cast hDeltaLowerNat
  have hDeltapos : 0 < Delta := habspos.trans_le hDeltaLower
  have hppos : 0 ≤ p := by
    dsimp [p]
    positivity
  have hrawpos : 0 < raw := by
    dsimp [raw]
    exact div_pos
      (mul_pos (pow_pos hEApos _) (pow_pos hEGpos _))
      (Real.rpow_pos_of_pos hDeltapos p)
  have hsourceLog : Real.log EA ≤
      Real.log (D : ℝ) + Real.log 64 +
        Real.log |(shiftedSquareA h v : ℝ)| / 2 := by
    dsimp [EA]
    exact log_main3LargeAnalyticFixedKeySourceScaleUpper_le
      hDposNat ha hkey.1 hkey.2.1 hkey.2.2.1
  have htargetLog : Real.log EG ≤
      Real.log (Y : ℝ) + Real.log 2048 +
        Real.log |(shiftedSquareA h v : ℝ)| := by
    dsimp [EG]
    exact log_main3LargeAnalyticFixedKeyTargetScaleUpper_le
      hYposNat ha hkey.1 hkey.2.1 hkey.2.2.2
  have hsourceScaled := mul_le_mul_of_nonneg_left hsourceLog
    (by positivity : (0 : ℝ) ≤ (B : ℝ) + 1)
  have htargetScaled := mul_le_mul_of_nonneg_left htargetLog
    (by positivity : (0 : ℝ) ≤ (B : ℝ) * ((B : ℝ) + 1))
  have hDeltaLog := Real.log_le_log habspos hDeltaLower
  have hDeltaScaled := mul_le_mul_of_nonneg_left hDeltaLog hppos
  have hDLog := main3LargeAnalytic_log_source_dyadic_le_balanced_base
    htheta hY hi
  have hsourceCoeff :
      1 * ((1 + 1) * (B + 1)) / 2 = B + 1 := by omega
  have htargetCoeff :
      B * ((1 + 1) * (B + 1)) / 2 = B * (B + 1) := by
    calc
      B * ((1 + 1) * (B + 1)) / 2 =
          (B * (B + 1)) * 2 / 2 := by
        congr 1
        ring
      _ = B * (B + 1) :=
        Nat.mul_div_left _ (by norm_num : 0 < 2)
  have hbase :
      twoLayerBalancedDoubledBaseLogCost B
          (Real.log (N : ℝ) / Real.log (Y : ℝ))
          (Real.log (Y : ℝ)) =
        ((B : ℝ) + 1) *
            ((Real.log (N : ℝ) / Real.log (Y : ℝ) - 1 / 2) *
              Real.log (Y : ℝ) + Real.log 4) +
          ((B : ℝ) * ((B : ℝ) + 1)) *
            (Real.log (Y : ℝ) + Real.log 4) := by
    unfold twoLayerBalancedDoubledBaseLogCost
      dyadicSymmetricBaseLogCost
    rw [hsourceCoeff, htargetCoeff]
    push_cast
    ring
  have hp : p = ((B : ℝ) + 1) ^ 2 / 2 := by
    dsimp [p]
    push_cast
    ring
  have hledgerIdentity :
      ((B : ℝ) + 1) *
          (Real.log (D : ℝ) + Real.log 64 +
            Real.log |(shiftedSquareA h v : ℝ)| / 2) +
        ((B : ℝ) * ((B : ℝ) + 1)) *
          (Real.log (Y : ℝ) + Real.log 2048 +
            Real.log |(shiftedSquareA h v : ℝ)|) -
        p * Real.log |(shiftedSquareA h v : ℝ)| ≤
      twoLayerBalancedDoubledBaseLogCost B
          (Real.log (N : ℝ) / Real.log (Y : ℝ))
          (Real.log (Y : ℝ)) +
        ((B : ℝ) * ((B : ℝ) + 1) / 2) *
          Real.log |(shiftedSquareA h v : ℝ)| +
        main3ComplexRadialFixedLogCost B := by
    rw [hbase, hp]
    unfold main3ComplexRadialFixedLogCost
    have hDscaled := mul_le_mul_of_nonneg_left hDLog
      (by positivity : (0 : ℝ) ≤ (B : ℝ) + 1)
    have htargetLogFour :
        0 ≤ ((B : ℝ) * ((B : ℝ) + 1)) * Real.log 4 :=
      mul_nonneg (by positivity) (Real.log_nonneg (by norm_num))
    nlinarith
  have hlogRaw : Real.log raw ≤
      twoLayerBalancedDoubledBaseLogCost B
          (Real.log (N : ℝ) / Real.log (Y : ℝ))
          (Real.log (Y : ℝ)) +
        ((B : ℝ) * ((B : ℝ) + 1) / 2) *
          Real.log |(shiftedSquareA h v : ℝ)| +
        main3ComplexRadialFixedLogCost B := by
    have hfirst :
        ((B : ℝ) + 1) * Real.log EA +
            ((B : ℝ) * ((B : ℝ) + 1)) * Real.log EG -
            p * Real.log Delta ≤
          ((B : ℝ) + 1) *
              (Real.log (D : ℝ) + Real.log 64 +
                Real.log |(shiftedSquareA h v : ℝ)| / 2) +
            ((B : ℝ) * ((B : ℝ) + 1)) *
              (Real.log (Y : ℝ) + Real.log 2048 +
                Real.log |(shiftedSquareA h v : ℝ)|) -
            p * Real.log |(shiftedSquareA h v : ℝ)| := by
      exact (sub_le_sub_right (add_le_add hsourceScaled htargetScaled)
        (p * Real.log Delta)).trans
          (sub_le_sub_left hDeltaScaled _)
    have hlogRawEq :
        Real.log raw =
          ((B : ℝ) + 1) * Real.log EA +
            ((B : ℝ) * ((B : ℝ) + 1)) * Real.log EG -
            p * Real.log Delta := by
      dsimp [raw]
      rw [Real.log_div
          (mul_ne_zero (pow_ne_zero _ hEApos.ne')
            (pow_ne_zero _ hEGpos.ne'))
          (Real.rpow_pos_of_pos hDeltapos p).ne',
        Real.log_mul (pow_ne_zero _ hEApos.ne')
          (pow_ne_zero _ hEGpos.ne'),
        Real.log_pow, Real.log_pow, Real.log_rpow hDeltapos]
      push_cast
      ring
    rw [hlogRawEq]
    exact hfirst.trans hledgerIdentity
  have hrawExp : raw ≤ Real.exp
      (twoLayerBalancedDoubledBaseLogCost B
          (Real.log (N : ℝ) / Real.log (Y : ℝ))
          (Real.log (Y : ℝ)) +
        ((B : ℝ) * ((B : ℝ) + 1) / 2) *
          Real.log |(shiftedSquareA h v : ℝ)| +
        main3ComplexRadialFixedLogCost B) := by
    calc
      raw = Real.exp (Real.log raw) := (Real.exp_log hrawpos).symm
      _ ≤ _ := Real.exp_le_exp.mpr hlogRaw
  have hcost :=
    main3LargeAnalytic_complexCellCoordinatePointImage_selectedRadialDiscriminantCostFactor_le
      htheta hY hi ha key cell s
  exact hcost.trans (by simpa only [raw, EA, EG, Delta, p] using hrawExp)

end

end PellPaper
