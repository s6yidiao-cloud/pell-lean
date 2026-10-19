import Pell.Main3LargeAnalyticRealEmbeddingMinorVanishing
import Pell.Main3LargeAnalyticComplexRadialLedger
import Pell.LocalLogarithmBounds
import Mathlib.Tactic

/-!
# Actual fixed-key real-cell scalar ledger

This candidate discharges the scalar hypotheses of the real-cell selected
minor endpoint.  It obtains the normalized source and target geometry from a
literal `Sum.inl` cell, retains the signed source centre, and proves the exact
positive-real-place radial identity.  The only extra radial loss relative to
the complex-place ledger is `B(B+1) log 2`, coming from the uniform lower
bound `T ≥ 1/2` for the normalized target coordinate.

The existing continuous two-layer fan-gain machinery then supplies the fan
and strict determinant rate under the standard growth hypothesis.
-/

open PellPaper

namespace PellPaper

open scoped BigOperators

theorem main3RealRadialRow_sq_mul_center_identity
    (B : ℕ) (alpha alphaBar gamma gammaBar : ℂ)
    (c S T : ℝ)
    (halphaBar : alphaBar ≠ 0) (hgamma : gamma ≠ 0)
    (hS : 0 < S) (hT : 0 < T)
    (hsource : alpha / alphaBar = ((c * S : ℝ) : ℂ))
    (htarget : gammaBar / gamma = ((c ^ 2 * T : ℝ) : ℂ)) :
    ‖alphaBar * gamma ^ B‖ ^ 2 * |c| ^ (2 * B + 1) * S * T ^ B =
      (‖alpha‖ * ‖alphaBar‖) * (‖gamma‖ * ‖gammaBar‖) ^ B := by
  have halphaBarNorm : ‖alphaBar‖ ≠ 0 := norm_ne_zero_iff.mpr halphaBar
  have hgammaNorm : ‖gamma‖ ≠ 0 := norm_ne_zero_iff.mpr hgamma
  have hsourceNorm := congrArg norm hsource
  have htargetNorm := congrArg norm htarget
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_pos hS] at hsourceNorm
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_pos hT, abs_pow] at htargetNorm
  have hsourceMul : ‖alpha‖ = (|c| * S) * ‖alphaBar‖ := by
    apply (div_eq_iff halphaBarNorm).mp
    simpa only [mul_comm] using hsourceNorm
  have htargetMul : ‖gammaBar‖ = (|c| ^ 2 * T) * ‖gamma‖ := by
    apply (div_eq_iff hgammaNorm).mp
    simpa only [mul_comm] using htargetNorm
  rw [norm_mul, norm_pow, hsourceMul, htargetMul]
  rw [mul_pow]
  ring

local instance main3LargeAnalyticRealCellRateLedgerCandidate_numberField (a : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

theorem shiftedSquare_positiveRealPlace_source_norm_mul_eq_EAlpha
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (ha : a < 0)
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq) :
    ‖shiftedSquarePositiveRealPlaceEmbedding a ha
        (shiftedSquareIntegralBasisElement P.basis P.x :
          rationalQuadraticAlgebra (-a))‖ *
      ‖shiftedSquarePositiveRealPlaceEmbedding a ha
        (star (shiftedSquareIntegralBasisElement P.basis P.x :
          rationalQuadraticAlgebra (-a)))‖ =
      shiftedSquareEAlpha P := by
  let alpha : rationalQuadraticAlgebra (-a) :=
    shiftedSquareIntegralBasisElement P.basis P.x
  let sigma := shiftedSquarePositiveRealPlaceEmbedding a ha
  have hmul : alpha * star alpha =
      (shiftedSquareExplicitNormFormEval P.t P.c P.x :
        rationalQuadraticAlgebra (-a)) := by
    simpa only [alpha] using
      shiftedSquare_integralBasisElement_mul_star_eq_explicitNormForm
        P.basis P.omega P.t P.c P.basis_zero P.basis_one P.omega_sq P.x
  have hnorm : ‖sigma alpha‖ * ‖sigma (star alpha)‖ =
      |(shiftedSquareExplicitNormFormEval P.t P.c P.x : ℝ)| := by
    calc
      ‖sigma alpha‖ * ‖sigma (star alpha)‖ = ‖sigma (alpha * star alpha)‖ := by
        rw [map_mul, norm_mul]
      _ = ‖sigma (shiftedSquareExplicitNormFormEval P.t P.c P.x)‖ := by rw [hmul]
      _ = |(shiftedSquareExplicitNormFormEval P.t P.c P.x : ℝ)| := by
        rw [map_intCast, Complex.norm_intCast]
  rw [hnorm]
  unfold shiftedSquareEAlpha
  have hr0 : (P.r : ℝ) ≠ 0 := by exact_mod_cast P.r_pos.ne'
  apply (eq_div_iff (pow_ne_zero 2 hr0)).2
  have h := congrArg (fun z : ℤ => (z : ℝ)) P.mu_norm_form
  simpa only [Int.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_abs,
    mul_comm] using h

theorem shiftedSquare_positiveRealPlace_target_norm_mul_eq_EGamma
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (ha : a < 0) (hw : 0 < w)
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq) :
    ‖shiftedSquarePositiveRealPlaceEmbedding a ha
        (shiftedSquareIntegralBasisElement P.basis P.y :
          rationalQuadraticAlgebra (-a))‖ *
      ‖shiftedSquarePositiveRealPlaceEmbedding a ha
        (star (shiftedSquareIntegralBasisElement P.basis P.y :
          rationalQuadraticAlgebra (-a)))‖ =
      shiftedSquareEGamma P := by
  let gamma : rationalQuadraticAlgebra (-a) :=
    shiftedSquareIntegralBasisElement P.basis P.y
  let sigma := shiftedSquarePositiveRealPlaceEmbedding a ha
  have hmul : gamma * star gamma =
      (shiftedSquareExplicitNormFormEval P.t P.c P.y :
        rationalQuadraticAlgebra (-a)) := by
    simpa only [gamma] using
      shiftedSquare_integralBasisElement_mul_star_eq_explicitNormForm
        P.basis P.omega P.t P.c P.basis_zero P.basis_one P.omega_sq P.y
  have hnorm : ‖sigma gamma‖ * ‖sigma (star gamma)‖ =
      (shiftedSquareExplicitNormFormEval P.t P.c P.y : ℝ) := by
    have hformNonneg : (0 : ℝ) ≤
        shiftedSquareExplicitNormFormEval P.t P.c P.y := by
      have h := congrArg (fun z : ℤ => (z : ℝ)) P.nu_norm_form
      have hell : (0 : ℝ) < P.ell := by exact_mod_cast P.ell_pos
      have hw0 : (0 : ℝ) < w := by exact_mod_cast hw
      have hC : (0 : ℝ) < P.minkowski.C₀ := by exact_mod_cast P.minkowski.C₀_pos
      push_cast at h
      have hellSq : 0 < (P.ell : ℝ) ^ 2 := sq_pos_of_pos hell
      have hrhs : 0 < (w : ℝ) * (P.minkowski.C₀ : ℝ) ^ 2 :=
        mul_pos hw0 (sq_pos_of_pos hC)
      nlinarith
    calc
      ‖sigma gamma‖ * ‖sigma (star gamma)‖ = ‖sigma (gamma * star gamma)‖ := by
        rw [map_mul, norm_mul]
      _ = ‖sigma (shiftedSquareExplicitNormFormEval P.t P.c P.y)‖ := by rw [hmul]
      _ = |(shiftedSquareExplicitNormFormEval P.t P.c P.y : ℝ)| := by
        rw [map_intCast, Complex.norm_intCast]
      _ = (shiftedSquareExplicitNormFormEval P.t P.c P.y : ℝ) :=
        abs_of_nonneg hformNonneg
  rw [hnorm]
  unfold shiftedSquareEGamma
  have hell0 : (P.ell : ℝ) ≠ 0 := by exact_mod_cast P.ell_pos.ne'
  apply (eq_div_iff (pow_ne_zero 2 hell0)).2
  have h := congrArg (fun z : ℤ => (z : ℝ)) P.nu_norm_form
  simpa only [Int.cast_mul, Int.cast_pow, Int.cast_natCast,
    mul_comm] using h

theorem main3ShiftedSquarePackagePoint_positiveRealRadial_sq_center_identity
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (ha : a < 0) (hw : 0 < w) (B : ℕ)
    (F : ShiftedSquareFixedExplicitIntegralBasisData a)
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq)
    (homega : P.omega = F.omega)
    (c S T : ℝ) (hS : 0 < S) (hT : 0 < T)
    (hsource : shiftedSquareSourceEmbeddingRatio P
      (shiftedSquarePositiveRealPlaceEmbedding a ha) = ((c * S : ℝ) : ℂ))
    (htarget : shiftedSquareTargetEmbeddingRatio P
      (shiftedSquarePositiveRealPlaceEmbedding a ha) = ((c ^ 2 * T : ℝ) : ℂ)) :
    ‖main3EmbeddingRadialRowFactor B
        (shiftedSquarePositiveRealPlaceEmbedding a ha F.omega)
        (shiftedSquarePositiveRealPlaceEmbedding a ha (star F.omega))
        (main3ShiftedSquarePackagePoint P)‖ ^ 2 *
          |c| ^ (2 * B + 1) * S * T ^ B =
      shiftedSquareEAlpha P * shiftedSquareEGamma P ^ B := by
  let sigma := shiftedSquarePositiveRealPlaceEmbedding a ha
  let alpha : ℂ := sigma
    (shiftedSquareIntegralBasisElement P.basis P.x :
      rationalQuadraticAlgebra (-a))
  let alphaBar : ℂ := sigma
    (star (shiftedSquareIntegralBasisElement P.basis P.x :
      rationalQuadraticAlgebra (-a)))
  let gamma : ℂ := sigma
    (shiftedSquareIntegralBasisElement P.basis P.y :
      rationalQuadraticAlgebra (-a))
  let gammaBar : ℂ := sigma
    (star (shiftedSquareIntegralBasisElement P.basis P.y :
      rationalQuadraticAlgebra (-a)))
  have halphaBar : alphaBar ≠ 0 :=
    shiftedSquare_sourceEmbeddingRatio_denominator_ne_zero P sigma
  have hgamma : gamma ≠ 0 :=
    shiftedSquare_targetEmbeddingRatio_denominator_ne_zero P sigma
  have hsource' : alpha / alphaBar = ((c * S : ℝ) : ℂ) := by
    simpa only [alpha, alphaBar, sigma, shiftedSquareSourceEmbeddingRatio] using hsource
  have htarget' : gammaBar / gamma = ((c ^ 2 * T : ℝ) : ℂ) := by
    simpa only [gamma, gammaBar, sigma, shiftedSquareTargetEmbeddingRatio] using htarget
  have hradial :
      main3EmbeddingRadialRowFactor B
          (sigma F.omega) (sigma (star F.omega))
          (main3ShiftedSquarePackagePoint P) = alphaBar * gamma ^ B := by
    have hsourceDen :=
      main3ShiftedSquarePackagePoint_sourceDenominator_eq F P homega sigma
    have htargetDen :=
      main3ShiftedSquarePackagePoint_targetDenominator_eq F P homega sigma
    have hsourceDen' :
        ((main3ShiftedSquarePackagePoint P).1.1 : ℂ) +
            sigma (star F.omega) *
              ((main3ShiftedSquarePackagePoint P).1.2 : ℂ) = alphaBar := by
      simpa only [main3ShiftedSquareEmbeddingOmegaBar, alphaBar] using hsourceDen
    have htargetDen' :
        ((main3ShiftedSquarePackagePoint P).2.1 : ℂ) +
            sigma F.omega *
              ((main3ShiftedSquarePackagePoint P).2.2 : ℂ) = gamma := by
      simpa only [main3ShiftedSquareEmbeddingOmega, gamma] using htargetDen
    unfold main3EmbeddingRadialRowFactor
    rw [hsourceDen', htargetDen']
  rw [hradial]
  rw [main3RealRadialRow_sq_mul_center_identity B alpha alphaBar gamma gammaBar c S T
    halphaBar hgamma hS hT hsource' htarget']
  rw [shiftedSquare_positiveRealPlace_source_norm_mul_eq_EAlpha ha P,
    shiftedSquare_positiveRealPlace_target_norm_mul_eq_EGamma ha hw P]

theorem main3ShiftedSquarePackagePoint_positiveRealRadial_sq_center_le
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (ha : a < 0) (hw : 0 < w) (B : ℕ)
    (F : ShiftedSquareFixedExplicitIntegralBasisData a)
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq)
    (homega : P.omega = F.omega)
    (c S T : ℝ) (hS : 1 ≤ S) (hT : 1 / 2 ≤ T)
    (hsource : shiftedSquareSourceEmbeddingRatio P
      (shiftedSquarePositiveRealPlaceEmbedding a ha) = ((c * S : ℝ) : ℂ))
    (htarget : shiftedSquareTargetEmbeddingRatio P
      (shiftedSquarePositiveRealPlaceEmbedding a ha) = ((c ^ 2 * T : ℝ) : ℂ)) :
    ‖main3EmbeddingRadialRowFactor B
        (shiftedSquarePositiveRealPlaceEmbedding a ha F.omega)
        (shiftedSquarePositiveRealPlaceEmbedding a ha (star F.omega))
        (main3ShiftedSquarePackagePoint P)‖ ^ 2 * |c| ^ (2 * B + 1) ≤
      shiftedSquareEAlpha P * (2 * shiftedSquareEGamma P) ^ B := by
  have hSpos : 0 < S := zero_lt_one.trans_le hS
  have hTpos : 0 < T := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hT
  have hid := main3ShiftedSquarePackagePoint_positiveRealRadial_sq_center_identity ha hw B F P homega c S T
    hSpos hTpos hsource htarget
  let x : ℝ :=
    ‖main3EmbeddingRadialRowFactor B
        (shiftedSquarePositiveRealPlaceEmbedding a ha F.omega)
        (shiftedSquarePositiveRealPlaceEmbedding a ha (star F.omega))
        (main3ShiftedSquarePackagePoint P)‖ ^ 2 * |c| ^ (2 * B + 1)
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hpow : (1 / 2 : ℝ) ^ B ≤ T ^ B := by
    exact pow_le_pow_left₀ (by norm_num) hT B
  have hST : (1 / 2 : ℝ) ^ B ≤ S * T ^ B := by
    calc
      (1 / 2 : ℝ) ^ B ≤ T ^ B := hpow
      _ ≤ S * T ^ B := by
        nlinarith [pow_nonneg hTpos.le B]
  have hright :
      (shiftedSquareEAlpha P * (2 * shiftedSquareEGamma P) ^ B) *
          (1 / 2 : ℝ) ^ B =
        shiftedSquareEAlpha P * shiftedSquareEGamma P ^ B := by
    have hpowe : (2 * shiftedSquareEGamma P) ^ B * (1 / 2 : ℝ) ^ B =
        shiftedSquareEGamma P ^ B := by
      rw [← mul_pow]
      congr 1
      ring
    rw [show shiftedSquareEAlpha P * (2 * shiftedSquareEGamma P) ^ B *
        (1 / 2 : ℝ) ^ B = shiftedSquareEAlpha P *
          ((2 * shiftedSquareEGamma P) ^ B * (1 / 2 : ℝ) ^ B) by ring,
      hpowe]
  have hhalfpos : 0 < (1 / 2 : ℝ) ^ B := pow_pos (by norm_num) B
  have hmul : x * (1 / 2 : ℝ) ^ B ≤
      (shiftedSquareEAlpha P * (2 * shiftedSquareEGamma P) ^ B) *
        (1 / 2 : ℝ) ^ B := by
    rw [hright]
    calc
    x * (1 / 2 : ℝ) ^ B ≤ x * (S * T ^ B) :=
      mul_le_mul_of_nonneg_left hST hx
    _ = shiftedSquareEAlpha P * shiftedSquareEGamma P ^ B := by
      dsimp only [x]
      nlinarith [hid]
  dsimp only [x] at hmul ⊢
  nlinarith

theorem main3LargeAnalytic_selectedRealCell_key_scale_index_package
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N B : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey) (cell : RealSquareMapCellPairIndex)
    (s : generalBidegreeFormIndex 1 B ↪
      {z // z ∈
        main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
          htheta hY hi key (Sum.inl cell)}) :
    (0 : ℝ) < key.C₀ ∧
      (key.C₀ : ℝ) ≤ 32 * Real.sqrt |(shiftedSquareA h v : ℝ)| ∧
      (1 : ℝ) ≤ key.r ∧ (1 : ℝ) ≤ key.ell ∧
      cell ∈ realSquareMapCellPairIndices
        (shiftedSquareEmbeddingScaleLoss (shiftedSquareA h v))
        (main3UnbalancedM theta Y) := by
  let r0 : generalBidegreeFormIndex 1 B :=
    (⟨0, by omega⟩, ⟨0, by omega⟩)
  have hz := (s r0).2
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  obtain ⟨p, _hp, hkey, hcell, _hgeometry, _hcode, _hzPoint⟩ :=
    main3LargeAnalytic_blockCellCoordinatePointImage_sameCertificate
      htheta hY hi hz
  let C := main3LargeAnalytic_blockFixedBasisEncodingCertificate
    htheta (by omega : 8 ≤ Y) hi p
  have hC0pos : 0 < C.P.minkowski.C₀ := C.P.minkowski.C₀_pos
  have hC0 := C.scaled.C₀_le_thirtytwo_mul_sqrt_abs
  have hr : 0 < C.P.r := C.P.r_pos
  have hell : 0 < C.P.ell := C.P.ell_pos
  have hselector :=
    main3LargeAnalytic_blockPointArchimedeanCellSelector_mem htheta hY hi p
  rw [hcell] at hselector
  have hcellMem :=
    mem_main3LargeAnalytic_archimedeanCellIndices_inl.mp hselector
  rw [← hkey]
  exact ⟨by exact_mod_cast hC0pos, hC0,
    by exact_mod_cast hr, by exact_mod_cast hell, hcellMem⟩

theorem abs_sheared_log_le_three_halves_mul_of_ratio_error
    {S T eps : ℝ} (hS : 0 < S) (hT : 0 < T)
    (heps0 : 0 ≤ eps) (heps : eps ≤ 1 / 3)
    (herror : |T / S ^ 2 - 1| ≤ eps) :
    |Real.log T - 2 * Real.log S| ≤ (3 / 2) * eps := by
  have hbase : 0 < 1 + (3 / 2) * eps := by positivity
  have herr := abs_le.mp herror
  have hupper : T / S ^ 2 ≤ 1 + (3 / 2) * eps := by linarith
  have hlowerRaw : 1 - eps ≤ T / S ^ 2 := by linarith
  have hinv : (1 + (3 / 2) * eps)⁻¹ ≤ 1 - eps := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hbase).2
    have hprod : 1 ≤ (1 - eps) * (1 + (3 / 2) * eps) := by
      nlinarith [mul_nonneg heps0 (sub_nonneg.mpr heps)]
    exact hprod
  exact abs_sheared_log_le_of_ratio_band (mul_nonneg (by norm_num) heps0)
    hS hT (hinv.trans hlowerRaw) hupper

theorem main3LargeAnalytic_realCellCoordinatePointImage_normalized_geometry
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey) (cell : RealSquareMapCellPairIndex)
    (ha : shiftedSquareA h v < 0) {z : GeneralBidegreeFormPoint}
    (hz : z ∈
      main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
        htheta hY hi key (Sum.inl cell)) :
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    let F := shiftedSquareFixedExplicitIntegralBasisData
      (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
    let sigma := shiftedSquarePositiveRealPlaceEmbedding
      (shiftedSquareA h v) ha
    let c := main3LargeAnalyticRealCellSignedCentre theta Y h v cell
    let S := main3LargeAnalyticRealCellNormalizedSource hi ha cell z
    let T := main3LargeAnalyticRealCellNormalizedTarget hi ha cell z
    c ≠ 0 ∧ 1 ≤ S ∧
      S ≤ 1 + 1 / (main3UnbalancedM theta Y : ℝ) ∧ 0 < T ∧
      main3EmbeddingSourceRatio
          (sigma F.omega) (sigma (star F.omega)) z = ((c * S : ℝ) : ℂ) ∧
      main3EmbeddingTargetRatio
          (sigma F.omega) (sigma (star F.omega)) z = ((c ^ 2 * T : ℝ) : ℂ) := by
  dsimp only
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let F := shiftedSquareFixedExplicitIntegralBasisData
    (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
  let sigma := shiftedSquarePositiveRealPlaceEmbedding
    (shiftedSquareA h v) ha
  let source := main3EmbeddingSourceRatio
    (sigma F.omega) (sigma (star F.omega)) z
  let target := main3EmbeddingTargetRatio
    (sigma F.omega) (sigma (star F.omega)) z
  let c := main3LargeAnalyticRealCellSignedCentre theta Y h v cell
  let S := main3LargeAnalyticRealCellNormalizedSource hi ha cell z
  let T := main3LargeAnalyticRealCellNormalizedTarget hi ha cell z
  have hF : 1 ≤ shiftedSquareEmbeddingScaleLoss (shiftedSquareA h v) := by
    have haOne : (1 : ℝ) ≤ |(shiftedSquareA h v : ℝ)| := by
      exact_mod_cast Int.one_le_abs (ne_of_lt ha)
    unfold shiftedSquareEmbeddingScaleLoss
    nlinarith
  let centre := annularMultiplicativeCenter
    (shiftedSquareEmbeddingScaleLoss (shiftedSquareA h v))
    (main3UnbalancedM theta Y) cell.1.2.1 cell.1.2.2
  have hcentre : 0 < centre := by
    dsimp only [centre, annularMultiplicativeCenter]
    exact mul_pos
      (annularDyadicStart_pos hF cell.1.2.1)
      (pow_pos (by unfold localRatioMeshStep; positivity) _)
  have hg := main3LargeAnalytic_realCellCoordinatePointImage_embeddingRatio_geometry
    htheta hY hi key cell ha hz
  change (((((z.1.1 : ℂ) + sigma (star F.omega) * (z.1.2 : ℂ) ≠ 0) ∧
      ((z.2.1 : ℂ) + sigma F.omega * (z.2.2 : ℂ) ≠ 0) ∧
      source.im = 0 ∧ target.im = 0 ∧ source.re ≠ 0 ∧ 0 < target.re) ∧
      InRealSquareMapCellPair
        (shiftedSquareEmbeddingScaleLoss (shiftedSquareA h v))
        (main3UnbalancedM theta Y) cell (source.re, target.re))) at hg
  rcases hg with
    ⟨⟨_hdenSource, _hdenTarget, hsourceIm, htargetIm,
      hsourceNe, htargetPos⟩, hcell⟩
  rcases hcell.1 with ⟨hsignEq, hlower, hupper⟩
  have hsignEq' : source.re = (cell.1.1 : ℝ) * |source.re| := by
    simpa only [source] using hsignEq
  have hsign : (cell.1.1 : ℝ) ≠ 0 := by
    intro hzero
    apply hsourceNe
    rw [hsignEq', hzero, zero_mul]
  have hc : c ≠ 0 := by
    dsimp only [c, main3LargeAnalyticRealCellSignedCentre, centre]
    exact mul_ne_zero hsign hcentre.ne'
  have hlower' : centre ≤ |source.re| := by
    simpa only [source] using hlower
  have hupper' : |source.re| ≤
      centre * (1 + 1 / (main3UnbalancedM theta Y : ℝ)) := by
    simpa only [Prod.fst, source, centre, localRatioMeshStep] using hupper
  have hquot :
      ((cell.1.1 : ℝ) * |source.re|) /
          ((cell.1.1 : ℝ) * centre) = |source.re| / centre := by
    field_simp [hsign, hcentre.ne']
  have hSvalue : S = |source.re| / centre := by
    dsimp only [S, main3LargeAnalyticRealCellNormalizedSource,
      main3LargeAnalyticRealCellSourceRatio, c,
      main3LargeAnalyticRealCellSignedCentre, source, F, sigma]
    trans ((cell.1.1 : ℝ) * |source.re|) /
      ((cell.1.1 : ℝ) * centre)
    · exact congrArg (fun x : ℝ =>
        x / ((cell.1.1 : ℝ) * centre)) hsignEq'
    · exact hquot
  have hSone : 1 ≤ S := by
    rw [hSvalue]
    exact (le_div_iff₀ hcentre).2 (by simpa using hlower')
  have hSupper : S ≤
      1 + 1 / (main3UnbalancedM theta Y : ℝ) := by
    rw [hSvalue]
    exact (div_le_iff₀ hcentre).2 (by simpa [mul_comm] using hupper')
  have hTpos : 0 < T := by
    dsimp only [T, main3LargeAnalyticRealCellNormalizedTarget,
      main3LargeAnalyticRealCellTargetRatio, c, F, sigma, target]
    exact div_pos htargetPos (sq_pos_of_ne_zero hc)
  have hsourceReal :
      main3EmbeddingSourceRatio
          (sigma F.omega) (sigma (star F.omega)) z = ((source.re : ℝ) : ℂ) := by
    change source = ((source.re : ℝ) : ℂ)
    apply Complex.ext
    · simp
    · simpa using hsourceIm
  have htargetReal :
      main3EmbeddingTargetRatio
          (sigma F.omega) (sigma (star F.omega)) z = ((target.re : ℝ) : ℂ) := by
    change target = ((target.re : ℝ) : ℂ)
    apply Complex.ext
    · simp
    · simpa using htargetIm
  have hsource : main3EmbeddingSourceRatio
      (sigma F.omega) (sigma (star F.omega)) z = ((c * S : ℝ) : ℂ) := by
    rw [hsourceReal]
    norm_cast
    change source.re = c * (source.re / c)
    field_simp [hc]
  have htarget : main3EmbeddingTargetRatio
      (sigma F.omega) (sigma (star F.omega)) z = ((c ^ 2 * T : ℝ) : ℂ) := by
    rw [htargetReal]
    norm_cast
    change target.re = c ^ 2 * (target.re / c ^ 2)
    field_simp [hc]
  exact ⟨hc, hSone, hSupper, hTpos, hsource, htarget⟩

theorem main3LargeAnalytic_realCellCoordinatePointImage_normalized_ratio_error_le_endpoint
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey) (cell : RealSquareMapCellPairIndex)
    (ha : shiftedSquareA h v < 0) {z : GeneralBidegreeFormPoint}
    (hz : z ∈
      main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
        htheta hY hi key (Sum.inl cell)) :
    |main3LargeAnalyticRealCellNormalizedTarget hi ha cell z /
        main3LargeAnalyticRealCellNormalizedSource hi ha cell z ^ 2 - 1| ≤
      (8 * Real.sqrt |(shiftedSquareA h v : ℝ)|) / (N : ℝ) := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  obtain ⟨p, _hpfiber, _hkey, _hcell, _hgeometry, _hcode, hzPoint⟩ :=
    main3LargeAnalytic_blockCellCoordinatePointImage_sameCertificate
      htheta hY hi hz
  let C := main3LargeAnalytic_blockFixedBasisEncodingCertificate
    htheta (by omega : 8 ≤ Y) hi p
  let F := shiftedSquareFixedExplicitIntegralBasisData
    (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
  let sigma := shiftedSquarePositiveRealPlaceEmbedding
    (shiftedSquareA h v) ha
  let source := main3EmbeddingSourceRatio
    (sigma F.omega) (sigma (star F.omega)) z
  let target := main3EmbeddingTargetRatio
    (sigma F.omega) (sigma (star F.omega)) z
  let c := main3LargeAnalyticRealCellSignedCentre theta Y h v cell
  let S := main3LargeAnalyticRealCellNormalizedSource hi ha cell z
  let T := main3LargeAnalyticRealCellNormalizedTarget hi ha cell z
  have hnorm := main3LargeAnalytic_realCellCoordinatePointImage_normalized_geometry
    htheta hY hi key cell ha hz
  change c ≠ 0 ∧ 1 ≤ S ∧
      S ≤ 1 + 1 / (main3UnbalancedM theta Y : ℝ) ∧ 0 < T ∧
      source = ((c * S : ℝ) : ℂ) ∧
      target = ((c ^ 2 * T : ℝ) : ℂ) at hnorm
  have hc := hnorm.1
  have hSpos : 0 < S := zero_lt_one.trans_le hnorm.2.1
  have hpointEq : z = main3ShiftedSquarePackagePoint C.P :=
    hzPoint.trans (main3ShiftedSquarePackagePoint_eq C.P).symm
  have hratio := main3ShiftedSquarePackagePoint_ratioPair_eq
    F C.P C.omega_eq sigma
  have hratio' :
      (source, target) =
        (shiftedSquareSourceEmbeddingRatio C.P sigma,
          shiftedSquareTargetEmbeddingRatio C.P sigma) := by
    dsimp only [source, target]
    rw [hpointEq]
    simpa only [main3ShiftedSquareEmbeddingOmega,
      main3ShiftedSquareEmbeddingOmegaBar] using hratio
  have hsourceEq : source = shiftedSquareSourceEmbeddingRatio C.P sigma :=
    congrArg Prod.fst hratio'
  have htargetEq : target = shiftedSquareTargetEmbeddingRatio C.P sigma :=
    congrArg Prod.snd hratio'
  obtain ⟨hdpos, hwpos, hnpos, _hdLower, _hdUpper,
      _hwLower, _hwUpper, hNn, _hnUpper, _heq, _hsf⟩ :=
    mem_squarefreeShiftedSquareBlock.mp p.2
  have hloc := shiftedSquare_embeddingRatio_localizationCertificate
    (ne_of_lt ha) hdpos hwpos C.scaled.base.shift_dominance C.P sigma
  have hquotEq : source⁻¹ ^ 2 * target - 1 =
      ((T / S ^ 2 - 1 : ℝ) : ℂ) := by
    rw [hnorm.2.2.2.2.2, hnorm.2.2.2.2.1]
    push_cast
    field_simp [hc, hSpos.ne']
  have herr : |T / S ^ 2 - 1| ≤
      (8 * Real.sqrt |(shiftedSquareA h v : ℝ)|) / (p.1.2.2 : ℝ) := by
    have h := hloc.quotient_error
    rw [← hsourceEq, ← htargetEq, hquotEq,
      Complex.norm_real, Real.norm_eq_abs] at h
    exact h
  have hiLarge :=
    mem_main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices.mp hi
  obtain ⟨hiBroad, hblock⟩ :=
    mem_main3UnbalancedEnlargedActiveDyadicCoverIndices.mp hiLarge.1
  have hNposNat :=
    (nonempty_main3UnbalancedEnlargedShiftedSquareCell_endpoint_height_package
      htheta (by omega : 2 ≤ Y) hiBroad hblock).2.1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hNposNat
  have hnreal : (N : ℝ) ≤ (p.1.2.2 : ℝ) := by exact_mod_cast hNn
  have hnum : 0 ≤ 8 * Real.sqrt |(shiftedSquareA h v : ℝ)| := by positivity
  exact herr.trans (div_le_div_of_nonneg_left hnum hNpos hnreal)

theorem six_le_main3UnbalancedM
    {theta : ℝ} {Y : ℕ} (htheta : 3 ≤ theta) (hY : 65536 ≤ Y) :
    6 ≤ main3UnbalancedM theta Y := by
  have hYone : (1 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast (show 1 ≤ Y by omega)
  have hexp : (1 / 2 : ℝ) ≤ main3UnbalancedMExponent theta := by
    have h := (main3UnbalancedMExponent_mem htheta).1
    norm_num at h ⊢
    linarith
  have hrpow : (Y : ℝ) ^ (1 / 2 : ℝ) ≤
      (Y : ℝ) ^ main3UnbalancedMExponent theta :=
    Real.rpow_le_rpow_of_exponent_le hYone hexp
  have hYreal : (65536 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
  have hsqrt : (256 : ℝ) ≤ Real.sqrt (Y : ℝ) := by
    rw [show (256 : ℝ) = Real.sqrt 65536 by norm_num]
    exact Real.sqrt_le_sqrt hYreal
  have hsix : (6 : ℝ) ≤ (Y : ℝ) ^ (1 / 2 : ℝ) := by
    have hsixSqrt : (6 : ℝ) ≤ Real.sqrt (Y : ℝ) := by linarith
    simpa [Real.sqrt_eq_rpow, one_div] using hsixSqrt
  have hceil : (Y : ℝ) ^ main3UnbalancedMExponent theta ≤
      (main3UnbalancedM theta Y : ℝ) := by
    unfold main3UnbalancedM
    exact Nat.le_ceil _
  exact_mod_cast hsix.trans (hrpow.trans hceil)

theorem main3LargeAnalytic_realCell_endpoint_error_le_one_third
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y) :
    (8 * Real.sqrt |(shiftedSquareA h v : ℝ)|) / (N : ℝ) ≤ 1 / 3 := by
  let M := main3UnbalancedM theta Y
  let s := Real.sqrt |(shiftedSquareA h v : ℝ)|
  have hM : (6 : ℝ) ≤ M := by
    exact_mod_cast six_le_main3UnbalancedM htheta hY
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hendpoint : 4 * (M : ℝ) * s < (N : ℝ) := by
    simpa only [M, s] using
      main3LargeAnalytic_four_mul_mesh_sqrt_shift_lt_endpoint htheta hY hi
  have hNpos : (0 : ℝ) < N :=
    (mul_nonneg (mul_nonneg (by norm_num) (by positivity)) hs).trans_lt hendpoint
  apply (div_le_iff₀ hNpos).2
  nlinarith [mul_nonneg (sub_nonneg.mpr hM) hs]

theorem main3LargeAnalytic_realCellCoordinatePointImage_normalized_sheared_log_le_defectScale
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey) (cell : RealSquareMapCellPairIndex)
    (ha : shiftedSquareA h v < 0) {z : GeneralBidegreeFormPoint}
    (hz : z ∈
      main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
        htheta hY hi key (Sum.inl cell)) :
    |Real.log (main3LargeAnalyticRealCellNormalizedTarget hi ha cell z) -
        2 * Real.log
          (main3LargeAnalyticRealCellNormalizedSource hi ha cell z)| ≤
      Real.exp (-main3ComplexDefectLogScale (shiftedSquareA h v) N) := by
  let S := main3LargeAnalyticRealCellNormalizedSource hi ha cell z
  let T := main3LargeAnalyticRealCellNormalizedTarget hi ha cell z
  let eps := (8 * Real.sqrt |(shiftedSquareA h v : ℝ)|) / (N : ℝ)
  have hgeometry := main3LargeAnalytic_realCellCoordinatePointImage_normalized_geometry
    htheta hY hi key cell ha hz
  change _ ≠ 0 ∧ 1 ≤ S ∧
      S ≤ 1 + 1 / (main3UnbalancedM theta Y : ℝ) ∧ 0 < T ∧ _ at hgeometry
  have hS : 0 < S := zero_lt_one.trans_le hgeometry.2.1
  have hT : 0 < T := hgeometry.2.2.2.1
  have heps0 : 0 ≤ eps := by dsimp [eps]; positivity
  have heps : eps ≤ 1 / 3 := by
    simpa only [eps] using
      main3LargeAnalytic_realCell_endpoint_error_le_one_third htheta hY hi
  have herror : |T / S ^ 2 - 1| ≤ eps := by
    simpa only [S, T, eps] using
      main3LargeAnalytic_realCellCoordinatePointImage_normalized_ratio_error_le_endpoint
        htheta hY hi key cell ha hz
  have hlog := abs_sheared_log_le_three_halves_mul_of_ratio_error
    hS hT heps0 heps herror
  have hiLarge :=
    mem_main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices.mp hi
  obtain ⟨hiBroad, hblock⟩ :=
    mem_main3UnbalancedEnlargedActiveDyadicCoverIndices.mp hiLarge.1
  have hNpos :=
    (nonempty_main3UnbalancedEnlargedShiftedSquareCell_endpoint_height_package
      htheta (by omega : 2 ≤ Y) hiBroad hblock).2.1
  rw [exp_neg_main3ComplexDefectLogScale_eq (ne_of_lt ha) hNpos]
  change |Real.log T - 2 * Real.log S| ≤ _
  exact hlog.trans (by dsimp [eps]; ring_nf; rfl)

theorem main3LargeAnalytic_realCellCoordinatePointImage_radial_sq_center_le
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N B : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey) (cell : RealSquareMapCellPairIndex)
    (ha : shiftedSquareA h v < 0) {z : GeneralBidegreeFormPoint}
    (hz : z ∈
      main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
        htheta hY hi key (Sum.inl cell)) :
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    let F := shiftedSquareFixedExplicitIntegralBasisData
      (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
    let sigma := shiftedSquarePositiveRealPlaceEmbedding
      (shiftedSquareA h v) ha
    let c := main3LargeAnalyticRealCellSignedCentre theta Y h v cell
    ‖main3EmbeddingRadialRowFactor B
        (sigma F.omega) (sigma (star F.omega)) z‖ ^ 2 *
          |c| ^ (2 * B + 1) ≤
      main3LargeAnalyticFixedKeySourceScaleUpper D key *
        (2 * main3LargeAnalyticFixedKeyTargetScaleUpper Y key) ^ B := by
  dsimp only
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  obtain ⟨p, _hp, hkey, _hcell, _hgeometry, _hcode, hzPoint⟩ :=
    main3LargeAnalytic_blockCellCoordinatePointImage_sameCertificate
      htheta hY hi hz
  let C := main3LargeAnalytic_blockFixedBasisEncodingCertificate
    htheta (by omega : 8 ≤ Y) hi p
  let F := shiftedSquareFixedExplicitIntegralBasisData
    (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
  let sigma := shiftedSquarePositiveRealPlaceEmbedding
    (shiftedSquareA h v) ha
  let c := main3LargeAnalyticRealCellSignedCentre theta Y h v cell
  let S := main3LargeAnalyticRealCellNormalizedSource hi ha cell z
  let T := main3LargeAnalyticRealCellNormalizedTarget hi ha cell z
  let eps := (8 * Real.sqrt |(shiftedSquareA h v : ℝ)|) / (N : ℝ)
  have hnorm := main3LargeAnalytic_realCellCoordinatePointImage_normalized_geometry
    htheta hY hi key cell ha hz
  change c ≠ 0 ∧ 1 ≤ S ∧
      S ≤ 1 + 1 / (main3UnbalancedM theta Y : ℝ) ∧ 0 < T ∧
      main3EmbeddingSourceRatio
          (sigma F.omega) (sigma (star F.omega)) z = ((c * S : ℝ) : ℂ) ∧
      main3EmbeddingTargetRatio
          (sigma F.omega) (sigma (star F.omega)) z = ((c ^ 2 * T : ℝ) : ℂ)
        at hnorm
  have hSpos : 0 < S := zero_lt_one.trans_le hnorm.2.1
  have hTpos : 0 < T := hnorm.2.2.2.1
  have heps : eps ≤ 1 / 3 := by
    simpa only [eps] using
      main3LargeAnalytic_realCell_endpoint_error_le_one_third htheta hY hi
  have herror : |T / S ^ 2 - 1| ≤ eps := by
    simpa only [S, T, eps] using
      main3LargeAnalytic_realCellCoordinatePointImage_normalized_ratio_error_le_endpoint
        htheta hY hi key cell ha hz
  have hratioLower : 1 - eps ≤ T / S ^ 2 := by
    have := (abs_le.mp herror).1
    linarith
  have hSsq : 1 ≤ S ^ 2 := by nlinarith
  have hTLower : (1 / 2 : ℝ) ≤ T := by
    have hratio : (2 / 3 : ℝ) ≤ T / S ^ 2 := by linarith
    have hmul : (2 / 3 : ℝ) * S ^ 2 ≤ T :=
      (le_div_iff₀ (sq_pos_of_pos hSpos)).mp hratio
    nlinarith
  have hzPackage : z = main3ShiftedSquarePackagePoint C.P :=
    hzPoint.trans (main3ShiftedSquarePackagePoint_eq C.P).symm
  have hratio := main3ShiftedSquarePackagePoint_ratioPair_eq
    F C.P C.omega_eq sigma
  have hsource : shiftedSquareSourceEmbeddingRatio C.P sigma =
      ((c * S : ℝ) : ℂ) := by
    rw [← hnorm.2.2.2.2.1]
    rw [hzPackage]
    simpa only [main3ShiftedSquareEmbeddingOmega,
      main3ShiftedSquareEmbeddingOmegaBar] using (congrArg Prod.fst hratio).symm
  have htarget : shiftedSquareTargetEmbeddingRatio C.P sigma =
      ((c ^ 2 * T : ℝ) : ℂ) := by
    rw [← hnorm.2.2.2.2.2]
    rw [hzPackage]
    simpa only [main3ShiftedSquareEmbeddingOmega,
      main3ShiftedSquareEmbeddingOmegaBar] using (congrArg Prod.snd hratio).symm
  obtain ⟨_hdpos, hwpos, _hnpos, _hdLower, hdUpper,
      _hwLower, hwUpper, _hNn, _hnUpper, _heq, _hsf⟩ :=
    mem_squarefreeShiftedSquareBlock.mp p.2
  have hrow := main3ShiftedSquarePackagePoint_positiveRealRadial_sq_center_le
    ha hwpos B F C.P C.omega_eq c S T hnorm.2.1 hTLower hsource htarget
  have hEA := shiftedSquareEAlpha_le_fixedKeySourceScaleUpper hdUpper C.P
  have hEG := shiftedSquareEGamma_le_fixedKeyTargetScaleUpper hwUpper C.P
  have hEAnonneg : 0 ≤ shiftedSquareEAlpha C.P := by
    unfold shiftedSquareEAlpha
    positivity
  have hEGnonneg : 0 ≤ shiftedSquareEGamma C.P := by
    unfold shiftedSquareEGamma
    positivity
  have hEAUpperNonneg : 0 ≤
      main3LargeAnalyticFixedKeySourceScaleUpper D
        ⟨C.P.minkowski.C₀, C.P.r, C.P.ell, C.P.bζ⟩ := by
    unfold main3LargeAnalyticFixedKeySourceScaleUpper
    positivity
  have htwice : 2 * shiftedSquareEGamma C.P ≤
      2 * main3LargeAnalyticFixedKeyTargetScaleUpper Y
        ⟨C.P.minkowski.C₀, C.P.r, C.P.ell, C.P.bζ⟩ :=
    mul_le_mul_of_nonneg_left hEG (by norm_num)
  have hpow : (2 * shiftedSquareEGamma C.P) ^ B ≤
      (2 * main3LargeAnalyticFixedKeyTargetScaleUpper Y
        ⟨C.P.minkowski.C₀, C.P.r, C.P.ell, C.P.bζ⟩) ^ B :=
    pow_le_pow_left₀ (mul_nonneg (by norm_num) hEGnonneg) htwice B
  rw [hzPackage]
  calc
    ‖main3EmbeddingRadialRowFactor B
        (sigma F.omega) (sigma (star F.omega))
        (main3ShiftedSquarePackagePoint C.P)‖ ^ 2 * |c| ^ (2 * B + 1) ≤
        shiftedSquareEAlpha C.P * (2 * shiftedSquareEGamma C.P) ^ B := hrow
    _ ≤ main3LargeAnalyticFixedKeySourceScaleUpper D key *
        (2 * main3LargeAnalyticFixedKeyTargetScaleUpper Y key) ^ B := by
      rw [← hkey]
      exact mul_le_mul hEA hpow (pow_nonneg (mul_nonneg (by norm_num) hEGnonneg) B)
        hEAUpperNonneg

theorem prod_mul_center_pow_le_of_sq_mul_center_pow_le
    {ι : Type*} [Fintype ι]
    (B : ℕ) (R : ι → ℝ) (c EA EG : ℝ)
    (hR : ∀ i, 0 ≤ R i) (hc : 0 ≤ c) (hEA : 0 ≤ EA) (hEG : 0 ≤ EG)
    (hcard : Fintype.card ι = 2 * (B + 1))
    (hrow : ∀ i, R i ^ 2 * c ^ (2 * B + 1) ≤ EA * (2 * EG) ^ B) :
    (∏ i, R i) * c ^ ((B + 1) * (2 * B + 1)) ≤
      EA ^ (B + 1) * (2 * EG) ^ (B * (B + 1)) := by
  let lhs := (∏ i, R i) * c ^ ((B + 1) * (2 * B + 1))
  let rhs := EA ^ (B + 1) * (2 * EG) ^ (B * (B + 1))
  have hlhs : 0 ≤ lhs := by
    dsimp [lhs]
    exact mul_nonneg (Finset.prod_nonneg fun i _hi => hR i) (pow_nonneg hc _)
  have hrhs : 0 ≤ rhs := by
    dsimp [rhs]
    exact mul_nonneg (pow_nonneg hEA _) (pow_nonneg (mul_nonneg (by norm_num) hEG) _)
  apply (sq_le_sq₀ hlhs hrhs).mp
  have hprod :
      (∏ i, R i ^ 2 * c ^ (2 * B + 1)) ≤
        ∏ _i : ι, EA * (2 * EG) ^ B := by
    apply Finset.prod_le_prod
    · intro i _hi
      exact mul_nonneg (sq_nonneg _) (pow_nonneg hc _)
    · intro i _hi
      exact hrow i
  have hleft : lhs ^ 2 =
      ∏ i, R i ^ 2 * c ^ (2 * B + 1) := by
    dsimp only [lhs]
    rw [mul_pow, ← Finset.prod_pow, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, hcard]
    congr 1
    simp only [← pow_mul]
    congr 1
    ring
  have hright : rhs ^ 2 =
      ∏ _i : ι, EA * (2 * EG) ^ B := by
    dsimp only [rhs]
    rw [Finset.prod_const, Finset.card_univ, hcard]
    rw [mul_pow (EA ^ (B + 1)) ((2 * EG) ^ (B * (B + 1))) 2]
    rw [mul_pow EA ((2 * EG) ^ B) (2 * (B + 1))]
    simp only [← pow_mul]
    congr 1 <;> congr 1 <;> ring
  rw [hleft, hright]
  exact hprod

theorem main3LargeAnalytic_realCellCoordinatePointImage_selectedRadialCenterProduct_le
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N B : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (ha : shiftedSquareA h v < 0)
    (key : ShiftedSquareAuxiliaryKey) (cell : RealSquareMapCellPairIndex)
    (s : generalBidegreeFormIndex 1 B ↪
      {z // z ∈
        main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
          htheta hY hi key (Sum.inl cell)}) :
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    let F := shiftedSquareFixedExplicitIntegralBasisData
      (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
    let sigma := shiftedSquarePositiveRealPlaceEmbedding
      (shiftedSquareA h v) ha
    (∏ r : generalBidegreeFormIndex 1 B,
        ‖main3EmbeddingRadialRowFactor B
          (sigma F.omega) (sigma (star F.omega)) (s r).1‖) *
      |main3LargeAnalyticRealCellSignedCentre theta Y h v cell| ^
        shearedCenterExponent 1 B ≤
      main3LargeAnalyticFixedKeySourceScaleUpper D key ^ (B + 1) *
        (2 * main3LargeAnalyticFixedKeyTargetScaleUpper Y key) ^
          (B * (B + 1)) := by
  dsimp only
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let F := shiftedSquareFixedExplicitIntegralBasisData
    (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
  let sigma := shiftedSquarePositiveRealPlaceEmbedding
    (shiftedSquareA h v) ha
  let c := |main3LargeAnalyticRealCellSignedCentre theta Y h v cell|
  let EA := main3LargeAnalyticFixedKeySourceScaleUpper D key
  let EG := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
  have hEA : 0 ≤ EA := by
    unfold EA main3LargeAnalyticFixedKeySourceScaleUpper
    positivity
  have hEG : 0 ≤ EG := by
    unfold EG main3LargeAnalyticFixedKeyTargetScaleUpper
    positivity
  have hproduct := prod_mul_center_pow_le_of_sq_mul_center_pow_le
    B (fun r : generalBidegreeFormIndex 1 B =>
      ‖main3EmbeddingRadialRowFactor B
        (sigma F.omega) (sigma (star F.omega)) (s r).1‖)
    c EA EG (fun _ => norm_nonneg _) (abs_nonneg _) hEA hEG
    (by simp only [card_generalBidegreeFormIndex])
    (fun r => by
      simpa only [c, EA, EG] using
        main3LargeAnalytic_realCellCoordinatePointImage_radial_sq_center_le
          htheta hY hi key cell ha (s r).2)
  rw [shearedCenterExponent_one_eq]
  simpa only [c, EA, EG] using hproduct

theorem main3LargeAnalytic_realCellCoordinatePointImage_selectedCost_le
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N B : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (ha : shiftedSquareA h v < 0)
    (key : ShiftedSquareAuxiliaryKey) (cell : RealSquareMapCellPairIndex)
    (s : generalBidegreeFormIndex 1 B ↪
      {z // z ∈
        main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
          htheta hY hi key (Sum.inl cell)}) :
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    main3LargeAnalyticRealCellSelectedCost htheta hY hi key cell ha B s ≤
      (main3LargeAnalyticFixedKeySourceScaleUpper D key ^ (B + 1) *
          (2 * main3LargeAnalyticFixedKeyTargetScaleUpper Y key) ^
            (B * (B + 1))) /
        Real.rpow
          |(NumberField.discr
            (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ)|
          (((((B + 1) ^ 2 : ℕ) : ℝ)) / 2) := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let F := shiftedSquareFixedExplicitIntegralBasisData
    (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
  let sigma := shiftedSquarePositiveRealPlaceEmbedding
    (shiftedSquareA h v) ha
  unfold main3LargeAnalyticRealCellSelectedCost
    main3RealSelectedRadialCenterDiscriminantCostFactor
  rw [div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right
  · simpa only [F, sigma] using
      main3LargeAnalytic_realCellCoordinatePointImage_selectedRadialCenterProduct_le
        htheta hY hi ha key cell s
  · exact (main3ShiftedSquare_discriminantRpowFactor_pos B).le

/-- The real-place radial ledger differs from the complex-place ledger only
by the lower bound `T ≥ 1/2` in every selected row. -/
noncomputable def main3RealRadialFixedLogCost (B : ℕ) : ℝ :=
  main3ComplexRadialFixedLogCost B +
    (B : ℝ) * ((B : ℝ) + 1) * Real.log 2

theorem main3LargeAnalytic_realCellCoordinatePointImage_selectedCost_le_exp_radialLedger
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N B : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (ha : shiftedSquareA h v < 0)
    (key : ShiftedSquareAuxiliaryKey) (cell : RealSquareMapCellPairIndex)
    (s : generalBidegreeFormIndex 1 B ↪
      {z // z ∈
        main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
          htheta hY hi key (Sum.inl cell)}) :
    main3LargeAnalyticRealCellSelectedCost htheta hY hi key cell ha B s ≤
      Real.exp
        (twoLayerBalancedDoubledBaseLogCost B
            (Real.log (N : ℝ) / Real.log (Y : ℝ))
            (Real.log (Y : ℝ)) +
          ((B : ℝ) * ((B : ℝ) + 1) / 2) *
            Real.log |(shiftedSquareA h v : ℝ)| +
          main3RealRadialFixedLogCost B) := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let EA := main3LargeAnalyticFixedKeySourceScaleUpper D key
  let EG := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
  let EG2 := 2 * EG
  let Delta : ℝ :=
    |(NumberField.discr
      (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ)|
  let p : ℝ := ((((B + 1) ^ 2 : ℕ) : ℝ)) / 2
  let raw : ℝ := EA ^ (B + 1) * EG2 ^ (B * (B + 1)) /
    Real.rpow Delta p
  have hkey := main3LargeAnalytic_selectedRealCell_key_scale_index_package
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
  have haReal : (shiftedSquareA h v : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_lt ha)
  have habspos : 0 < |(shiftedSquareA h v : ℝ)| := abs_pos.mpr haReal
  have hEApos : 0 < EA := by
    dsimp [EA, main3LargeAnalyticFixedKeySourceScaleUpper]
    exact div_pos
      (mul_pos (mul_pos (by norm_num) hDpos) hkey.1)
      (pow_pos (zero_lt_one.trans_le hkey.2.2.1) 2)
  have hEGpos : 0 < EG := by
    dsimp [EG, main3LargeAnalyticFixedKeyTargetScaleUpper]
    exact div_pos
      (mul_pos (mul_pos (by norm_num) hYpos) (pow_pos hkey.1 2))
      (pow_pos (zero_lt_one.trans_le hkey.2.2.2.1) 2)
  have hEG2pos : 0 < EG2 := by dsimp [EG2]; positivity
  have hDeltaLowerNat :=
    abs_le_abs_rationalQuadraticAlgebra_neg_fieldDiscriminant_of_squarefree
      (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
  have hDeltaLower : |(shiftedSquareA h v : ℝ)| ≤ Delta := by
    dsimp [Delta]
    exact_mod_cast hDeltaLowerNat
  have hDeltapos : 0 < Delta := habspos.trans_le hDeltaLower
  have hppos : 0 ≤ p := by dsimp [p]; positivity
  have hrawpos : 0 < raw := by
    dsimp [raw]
    exact div_pos
      (mul_pos (pow_pos hEApos _) (pow_pos hEG2pos _))
      (Real.rpow_pos_of_pos hDeltapos p)
  have hsourceLog : Real.log EA ≤
      Real.log (D : ℝ) + Real.log 64 +
        Real.log |(shiftedSquareA h v : ℝ)| / 2 := by
    have hneg : 0 < -(shiftedSquareA h v) := neg_pos.mpr ha
    have hbound : (key.C₀ : ℝ) ≤
        32 * Real.sqrt |((-(shiftedSquareA h v) : ℤ) : ℝ)| := by
      simpa only [Int.cast_neg, abs_neg] using hkey.2.1
    have h := log_main3LargeAnalyticFixedKeySourceScaleUpper_le
      hDposNat hneg hkey.1 hbound hkey.2.2.1
    simpa only [EA, Int.cast_neg, abs_neg] using h
  have htargetLogBase : Real.log EG ≤
      Real.log (Y : ℝ) + Real.log 2048 +
        Real.log |(shiftedSquareA h v : ℝ)| := by
    have hneg : 0 < -(shiftedSquareA h v) := neg_pos.mpr ha
    have hbound : (key.C₀ : ℝ) ≤
        32 * Real.sqrt |((-(shiftedSquareA h v) : ℤ) : ℝ)| := by
      simpa only [Int.cast_neg, abs_neg] using hkey.2.1
    have h := log_main3LargeAnalyticFixedKeyTargetScaleUpper_le
      hYposNat hneg hkey.1 hbound hkey.2.2.2.1
    simpa only [EG, Int.cast_neg, abs_neg] using h
  have htargetLog : Real.log EG2 ≤
      Real.log (Y : ℝ) + Real.log 2048 +
        Real.log |(shiftedSquareA h v : ℝ)| + Real.log 2 := by
    dsimp [EG2]
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hEGpos.ne']
    linarith
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
      _ = B * (B + 1) := Nat.mul_div_left _ (by norm_num : 0 < 2)
  have hbase :
      twoLayerBalancedDoubledBaseLogCost B
          (Real.log (N : ℝ) / Real.log (Y : ℝ))
          (Real.log (Y : ℝ)) =
        ((B : ℝ) + 1) *
            ((Real.log (N : ℝ) / Real.log (Y : ℝ) - 1 / 2) *
              Real.log (Y : ℝ) + Real.log 4) +
          ((B : ℝ) * ((B : ℝ) + 1)) *
            (Real.log (Y : ℝ) + Real.log 4) := by
    unfold twoLayerBalancedDoubledBaseLogCost dyadicSymmetricBaseLogCost
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
            Real.log |(shiftedSquareA h v : ℝ)| + Real.log 2) -
        p * Real.log |(shiftedSquareA h v : ℝ)| ≤
      twoLayerBalancedDoubledBaseLogCost B
          (Real.log (N : ℝ) / Real.log (Y : ℝ))
          (Real.log (Y : ℝ)) +
        ((B : ℝ) * ((B : ℝ) + 1) / 2) *
          Real.log |(shiftedSquareA h v : ℝ)| +
        main3RealRadialFixedLogCost B := by
    rw [hbase, hp]
    unfold main3RealRadialFixedLogCost main3ComplexRadialFixedLogCost
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
        main3RealRadialFixedLogCost B := by
    have hfirst :
        ((B : ℝ) + 1) * Real.log EA +
            ((B : ℝ) * ((B : ℝ) + 1)) * Real.log EG2 -
            p * Real.log Delta ≤
          ((B : ℝ) + 1) *
              (Real.log (D : ℝ) + Real.log 64 +
                Real.log |(shiftedSquareA h v : ℝ)| / 2) +
            ((B : ℝ) * ((B : ℝ) + 1)) *
              (Real.log (Y : ℝ) + Real.log 2048 +
                Real.log |(shiftedSquareA h v : ℝ)| + Real.log 2) -
            p * Real.log |(shiftedSquareA h v : ℝ)| := by
      exact (sub_le_sub_right (add_le_add hsourceScaled htargetScaled)
        (p * Real.log Delta)).trans
          (sub_le_sub_left hDeltaScaled _)
    have hlogRawEq :
        Real.log raw =
          ((B : ℝ) + 1) * Real.log EA +
            ((B : ℝ) * ((B : ℝ) + 1)) * Real.log EG2 -
            p * Real.log Delta := by
      dsimp [raw]
      rw [Real.log_div
          (mul_ne_zero (pow_ne_zero _ hEApos.ne')
            (pow_ne_zero _ hEG2pos.ne'))
          (Real.rpow_pos_of_pos hDeltapos p).ne',
        Real.log_mul (pow_ne_zero _ hEApos.ne')
          (pow_ne_zero _ hEG2pos.ne'),
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
        main3RealRadialFixedLogCost B) := by
    calc
      raw = Real.exp (Real.log raw) := (Real.exp_log hrawpos).symm
      _ ≤ _ := Real.exp_le_exp.mpr hlogRaw
  have hcost := main3LargeAnalytic_realCellCoordinatePointImage_selectedCost_le
    htheta hY hi ha key cell s
  exact hcost.trans (by simpa only [raw, EA, EG2, EG, Delta, p] using hrawExp)

theorem main3RealRateFixedLogCost_le_thirtyone_mul_sq (B : ℕ) :
    main3ComplexRateFixedLogCost B (main3RealRadialFixedLogCost B) ≤
      31 * ((B : ℝ) + 1) ^ 2 := by
  have hbase := main3ComplexRateFixedLogCost_le_thirty_mul_sq B
  have hb0 : (0 : ℝ) ≤ B := by positivity
  have hb1 : 0 ≤ (B : ℝ) + 1 := by positivity
  have hcoeff : (B : ℝ) * ((B : ℝ) + 1) ≤
      ((B : ℝ) + 1) ^ 2 := by nlinarith
  have hlog2nonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hextraA := mul_le_mul_of_nonneg_left log_two_le_three_div_four
    (mul_nonneg hb0 hb1)
  have hextraB := mul_le_mul_of_nonneg_right hcoeff hlog2nonneg
  have hextra :
      (B : ℝ) * ((B : ℝ) + 1) * Real.log 2 ≤
        ((B : ℝ) + 1) ^ 2 := by nlinarith [sq_nonneg ((B : ℝ) + 1)]
  unfold main3RealRadialFixedLogCost
    main3ComplexRateFixedLogCost at *
  linarith

theorem main3RealRateFixedLogCost_lt_theta_sq_div_sixteen_mul_log
    (theta : ℝ) (Y : ℕ) (htheta : 3 ≤ theta)
    (hYgrow : Real.exp (800 * theta ^ 2) < (Y : ℝ)) :
    main3ComplexRateFixedLogCost (main3BalancedDegree theta)
        (main3RealRadialFixedLogCost (main3BalancedDegree theta)) <
      theta ^ 2 / 16 * Real.log (Y : ℝ) := by
  let t : ℝ := theta ^ 2
  let B : ℕ := main3BalancedDegree theta
  have ht9 : 9 ≤ t := by
    dsimp [t]
    nlinarith [sq_nonneg (theta - 3)]
  have hYpos : (0 : ℝ) < Y := (Real.exp_pos _).trans hYgrow
  have hlog : 800 * t < Real.log (Y : ℝ) := by
    have h := Real.strictMonoOn_log (Real.exp_pos _) hYpos hYgrow
    rw [Real.log_exp] at h
    simpa only [t] using h
  have hBupper : (B : ℝ) < t + 1 := by
    dsimp [B, t]
    exact (main3UnbalancedDegree_nearSquare theta).2
  have hBplus : (B : ℝ) + 1 < t + 2 := by linarith
  have hsq : ((B : ℝ) + 1) ^ 2 < (t + 2) ^ 2 := by
    exact (sq_lt_sq₀ (by positivity) (by positivity)).2 hBplus
  have hpoly : 31 * (t + 2) ^ 2 ≤ 50 * t ^ 2 := by
    have haux : 0 ≤ (t - 9) * (19 * t + 43) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hlogGain : 50 * t ^ 2 < t / 16 * Real.log (Y : ℝ) := by
    have hscale := mul_lt_mul_of_pos_left hlog (by positivity : 0 < t / 16)
    nlinarith
  have hcost := main3RealRateFixedLogCost_le_thirtyone_mul_sq B
  dsimp [B, t] at hcost hsq hpoly hlogGain ⊢
  exact hcost.trans_lt
    (((mul_lt_mul_of_pos_left hsq (by norm_num : (0 : ℝ) < 31)).trans_le
      hpoly).trans hlogGain)

theorem exists_main3LargeAnalytic_realFanIndex
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hYgrow : Real.exp (800 * theta ^ 2) < (Y : ℝ))
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (ha : shiftedSquareA h v < 0) :
    ∃ k : ℕ,
      1 ≤ k ∧ k ≤ main3BalancedDegree theta ∧
      (2 * (k : ℝ) - 1) *
          main3ComplexSourceLogScale (main3UnbalancedM theta Y) ≤
        main3ComplexDefectLogScale (shiftedSquareA h v) N ∧
      main3ComplexDefectLogScale (shiftedSquareA h v) N ≤
        (2 * (k : ℝ) + 1) *
          main3ComplexSourceLogScale (main3UnbalancedM theta Y) := by
  let ellM := main3ComplexSourceLogScale (main3UnbalancedM theta Y)
  let ellX := main3ComplexDefectLogScale (shiftedSquareA h v) N
  let B := main3BalancedDegree theta
  have hlogYpos : 0 < Real.log (Y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
  have hellM : 0 < ellM := by
    have hhalf := half_log_le_main3ComplexSourceLogScale htheta hY
    dsimp [ellM]
    linarith
  have hmq : ellM ≤ ellX := by
    simpa only [ellM, ellX] using
      (main3LargeAnalytic_complexSourceLogScale_lt_defectLogScale
        htheta hY hi).le
  have hq :=
    (main3LargeAnalytic_endpoint_logExponent_mem htheta hY hYgrow hi).2
  have hqB : ellX ≤ 2 * ellM * (B : ℝ) := by
    simpa only [ellX, ellM, B] using
      main3ComplexDefectLogScale_le_two_mul_degree_sourceLogScale
        htheta hY (ne_of_lt ha) hq
  refine ⟨nearestTwoLayerFanIndex ellM ellX, ?_⟩
  simpa only [ellM, ellX, B] using
    nearestTwoLayerFanIndex_spec B ellM ellX hellM hmq hqB

theorem exists_main3LargeAnalytic_realFanIndex_and_rate_of_radialLedger
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hYgrow : Real.exp (800 * theta ^ 2) < (Y : ℝ))
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (ha : shiftedSquareA h v < 0) (cost : ℝ)
    (hradial :
      cost ≤
        twoLayerBalancedDoubledBaseLogCost
            (main3BalancedDegree theta)
            (Real.log (N : ℝ) / Real.log (Y : ℝ))
            (Real.log (Y : ℝ)) +
          ((main3BalancedDegree theta : ℝ) *
              ((main3BalancedDegree theta : ℝ) + 1) / 2) *
            Real.log |(shiftedSquareA h v : ℝ)| +
          main3RealRadialFixedLogCost
            (main3BalancedDegree theta)) :
    ∃ k : ℕ,
      1 ≤ k ∧ k ≤ main3BalancedDegree theta ∧
      (2 * (k : ℝ) - 1) *
          main3ComplexSourceLogScale (main3UnbalancedM theta Y) ≤
        main3ComplexDefectLogScale (shiftedSquareA h v) N ∧
      main3ComplexDefectLogScale (shiftedSquareA h v) N ≤
        (2 * (k : ℝ) + 1) *
          main3ComplexSourceLogScale (main3UnbalancedM theta Y) ∧
      cost +
          Real.log (Nat.factorial
            (Fintype.card (generalBidegreeGrid 1
              (main3BalancedDegree theta))) : ℝ) +
        twoLayerFanTaylorTail (main3BalancedDegree theta) *
          (Fintype.card (generalBidegreeGrid 1
            (main3BalancedDegree theta)) : ℝ) <
        twoLayerWeight (main3BalancedDegree theta) k
          (main3ComplexSourceLogScale (main3UnbalancedM theta Y))
          (main3ComplexDefectLogScale (shiftedSquareA h v) N) := by
  let B := main3BalancedDegree theta
  let M := main3UnbalancedM theta Y
  let a := shiftedSquareA h v
  let m := main3UnbalancedMLogExponent theta Y
  let q := Real.log (N : ℝ) / Real.log (Y : ℝ)
  let L := Real.log (Y : ℝ)
  have hLpos : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
  have hq := main3LargeAnalytic_endpoint_logExponent_mem htheta hY hYgrow hi
  obtain ⟨k, hkpos, hkB, hfanLower, hfanUpper⟩ :=
    exists_main3LargeAnalytic_realFanIndex htheta hY hYgrow hi ha
  have hiLarge :=
    mem_main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices.mp hi
  have hiBroad :=
    (mem_main3UnbalancedEnlargedActiveDyadicCoverIndices.mp hiLarge.1).1
  have hshift : |(a : ℝ)| ≤
      2 * (Y : ℝ) ^ main3BalancedRExponent theta := by
    dsimp [a]
    exact (main3UnbalancedEnlargedShiftedSquareIndex_shift_abs_bounds
      htheta (by omega : 2 ≤ Y) hiBroad).2.1.le
  have hshiftCharge :=
    main3Complex_combinedShiftLog_le_discriminantCharge_add_fixed
      B theta Y a htheta (by omega) (by exact ne_of_lt ha) hshift
  have hgain :=
    theta_sq_div_sixteen_le_main3LargeAnalytic_ceilingChargedFanSurplus
      theta Y k q htheta (by omega) (by simpa only [q] using hq.1)
        (by simpa only [q] using hq.2)
  have hlogM : m * L = Real.log (M : ℝ) := by
    simpa only [m, L, M] using
      (main3UnbalancedM_parameter_package theta Y htheta (by omega)).2.2.2.2.2
  have hlogN : q * L = Real.log (N : ℝ) := by
    dsimp [q, L]
    exact div_mul_cancel₀ _ hLpos.ne'
  have hfixed :=
    main3RealRateFixedLogCost_lt_theta_sq_div_sixteen_mul_log
      theta Y htheta hYgrow
  have hrate := main3Complex_rate_of_radial_and_positiveFan_charges
    B k theta m q L cost (main3RealRadialFixedLogCost B)
      M N a hkpos hkB (by exact ne_of_lt ha) hLpos.le hlogM hlogN
      (by simpa only [B, q, L, a] using hradial)
      hshiftCharge hgain (by simpa only [B, L] using hfixed)
  refine ⟨k, hkpos, hkB, ?_, ?_, ?_⟩
  · simpa only [B, M, a] using hfanLower
  · simpa only [B, M, a] using hfanUpper
  · simpa only [B, M, a] using hrate

theorem main3LargeAnalytic_realCellCoordinatePointImage_selectedMinor_det_eq_zero
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hYgrow : Real.exp (800 * theta ^ 2) < (Y : ℝ))
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (ha : shiftedSquareA h v < 0)
    (key : ShiftedSquareAuxiliaryKey) (cell : RealSquareMapCellPairIndex)
    (s : generalBidegreeFormIndex 1 (main3BalancedDegree theta) ↪
      {z // z ∈
        main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
          htheta hY hi key (Sum.inl cell)}) :
    ((generalBidegreeFormEvaluationMatrix 1 (main3BalancedDegree theta)
      (fun z : {z // z ∈
        main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
          htheta hY hi key (Sum.inl cell)} => z.1)).submatrix s id).det = 0 := by
  let B := main3BalancedDegree theta
  let M := main3UnbalancedM theta Y
  let a := shiftedSquareA h v
  let ellM := main3ComplexSourceLogScale M
  let ellX := main3ComplexDefectLogScale a N
  let cost :=
    twoLayerBalancedDoubledBaseLogCost B
        (Real.log (N : ℝ) / Real.log (Y : ℝ)) (Real.log (Y : ℝ)) +
      ((B : ℝ) * ((B : ℝ) + 1) / 2) * Real.log |(a : ℝ)| +
      main3RealRadialFixedLogCost B
  have hM6 : 6 ≤ M := by
    simpa only [M] using six_le_main3UnbalancedM htheta hY
  have hMpos : 0 < M := by omega
  have hellM : 0 < ellM := by
    dsimp only [ellM]
    exact main3ComplexSourceLogScale_pos (by omega)
  have hsourceScale : 1 / (M : ℝ) ≤ Real.exp (-ellM) := by
    rw [exp_neg_main3ComplexSourceLogScale_eq hMpos]
    exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
  have hlogDefect : ∀ r,
      |generalBidegreeReindexedShearedLogT 1 B
        (generalBidegreeGridPointEquiv 1 B)
        (fun q => main3LargeAnalyticRealCellNormalizedSource
          hi ha cell (s q).1)
        (fun q => main3LargeAnalyticRealCellNormalizedTarget
          hi ha cell (s q).1) r| ≤ Real.exp (-ellX) := by
    intro r
    change
      |Real.log (main3LargeAnalyticRealCellNormalizedTarget hi ha cell
          (s ((generalBidegreeGridPointEquiv 1 B).symm r)).1) -
        2 * Real.log (main3LargeAnalyticRealCellNormalizedSource hi ha cell
          (s ((generalBidegreeGridPointEquiv 1 B).symm r)).1)| ≤
        Real.exp (-ellX)
    simpa only [ellX, a, B] using
      main3LargeAnalytic_realCellCoordinatePointImage_normalized_sheared_log_le_defectScale
        htheta hY hi key cell ha
          (s ((generalBidegreeGridPointEquiv 1 B).symm r)).2
  have hcost : main3LargeAnalyticRealCellSelectedCost
      htheta hY hi key cell ha B s ≤ Real.exp cost := by
    simpa only [B, a, cost] using
      main3LargeAnalytic_realCellCoordinatePointImage_selectedCost_le_exp_radialLedger
        htheta hY hi ha key cell s
  have hcostLedger :
      cost ≤
        twoLayerBalancedDoubledBaseLogCost B
            (Real.log (N : ℝ) / Real.log (Y : ℝ))
            (Real.log (Y : ℝ)) +
          ((B : ℝ) * ((B : ℝ) + 1) / 2) * Real.log |(a : ℝ)| +
          main3RealRadialFixedLogCost B := by rfl
  obtain ⟨k, hkpos, hkB, hfanLower, hfanUpper, hrate⟩ :=
    exists_main3LargeAnalytic_realFanIndex_and_rate_of_radialLedger
      htheta hY hYgrow hi ha cost
        (by simpa only [B, a] using hcostLedger)
  exact main3LargeAnalytic_realCellCoordinatePointImage_selectedMinor_det_eq_zero_of_rate
    htheta hY hi key cell ha B k s ellM ellX hellM hkpos hkB
      (by simpa only [B, M, a, ellM, ellX] using hfanLower)
      (by simpa only [B, M, a, ellM, ellX] using hfanUpper)
      (by simpa only [M] using hsourceScale)
      (by simpa only [B, a, ellX] using hlogDefect)
      cost (by simpa only [B] using hcost)
      (by simpa only [B, M, a, ellM, ellX] using hrate)

end PellPaper
