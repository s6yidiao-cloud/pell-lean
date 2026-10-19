import Pell.Main3ShiftedSquareEmbeddingRatioCoordinateAdapter
import Pell.Main3ComplexEmbeddingMinorVanishing
import Pell.TwoLayerFanDeterminantDecay
import Pell.ShearedCenterExponentFormula
import Pell.IntegralDeterminantVanishing
import Mathlib.Tactic

namespace PellPaper

open scoped BigOperators

noncomputable section

local instance main3LargeAnalyticRealEmbeddingMinorVanishing_numberField
    (a : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

/-- The exact real-place multiplier left after extracting the common signed
source centre from every ratio-power column.  The absolute value of the
signed centre is essential: the source ratio may be negative, whereas the
normalized source and target coordinates are positive. -/
def main3RealSelectedRadialCenterDiscriminantCostFactor
    {ι : Type*} {a : ℤ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (B : ℕ) (F : ShiftedSquareFixedExplicitIntegralBasisData a)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ)
    (points : ι → GeneralBidegreeFormPoint)
    (s : generalBidegreeFormIndex 1 B ↪ ι) (signedCentre : ℝ) : ℝ :=
  ((∏ r : generalBidegreeFormIndex 1 B,
      ‖main3EmbeddingRadialRowFactor B
        (sigma F.omega) (sigma (star F.omega)) (points (s r))‖) /
    Real.rpow
      |(NumberField.discr (rationalQuadraticAlgebra (-a)) : ℝ)|
      (((((B + 1) ^ 2 : ℕ) : ℝ)) / 2)) *
    |signedCentre| ^ shearedCenterExponent 1 B

theorem main3RealSelectedRadialCenterDiscriminantCostFactor_nonneg
    {ι : Type*} {a : ℤ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (B : ℕ) (F : ShiftedSquareFixedExplicitIntegralBasisData a)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ)
    (points : ι → GeneralBidegreeFormPoint)
    (s : generalBidegreeFormIndex 1 B ↪ ι) (signedCentre : ℝ) :
    0 ≤ main3RealSelectedRadialCenterDiscriminantCostFactor
      B F sigma points s signedCentre := by
  unfold main3RealSelectedRadialCenterDiscriminantCostFactor
  exact mul_nonneg
    (main3ComplexSelectedRadialDiscriminantCostFactor_nonneg
      B F sigma points s)
    (pow_nonneg (abs_nonneg _) _)

/-- In bidegree `(1,B)`, the signed source centre contributes exactly one
factor for each source exponent and two for each target exponent. -/
theorem shearedCenterExponent_one_eq (B : ℕ) :
    shearedCenterExponent 1 B = (B + 1) * (2 * B + 1) := by
  rw [shearedCenterExponent_eq]
  norm_num
  ring

/-- Positive real local source coordinate after division by the common
signed centre. -/
def main3RealNormalizedSourceCoordinate
    (omega omegaBar : ℂ) (signedCentre : ℝ)
    (z : GeneralBidegreeFormPoint) : ℝ :=
  (main3EmbeddingSourceRatio omega omegaBar z).re / signedCentre

/-- Positive real local target coordinate after division by the square of
the same signed centre. -/
def main3RealNormalizedTargetCoordinate
    (omega omegaBar : ℂ) (signedCentre : ℝ)
    (z : GeneralBidegreeFormPoint) : ℝ :=
  (main3EmbeddingTargetRatio omega omegaBar z).re / signedCentre ^ 2

/-- Every point of an actual fixed-key real cell retains one and the same
normalized package.  In particular, its reflected embedding ratios are real,
the target ratio is positive, and both radial denominators are nonzero. -/
theorem main3LargeAnalytic_realCellCoordinatePointImage_embeddingRatio_geometry
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey) (cell : RealSquareMapCellPairIndex)
    (ha : shiftedSquareA h v < 0)
    {z : GeneralBidegreeFormPoint}
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
    let source := main3EmbeddingSourceRatio
      (sigma F.omega) (sigma (star F.omega)) z
    let target := main3EmbeddingTargetRatio
      (sigma F.omega) (sigma (star F.omega)) z
    ((((z.1.1 : ℂ) + sigma (star F.omega) * (z.1.2 : ℂ) ≠ 0) ∧
        ((z.2.1 : ℂ) + sigma F.omega * (z.2.2 : ℂ) ≠ 0) ∧
      source.im = 0 ∧ target.im = 0 ∧ source.re ≠ 0 ∧
        0 < target.re) ∧
      InRealSquareMapCellPair
        (shiftedSquareEmbeddingScaleLoss (shiftedSquareA h v))
        (main3UnbalancedM theta Y) cell (source.re, target.re)) := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let hY8 : 8 ≤ Y := by omega
  let F := shiftedSquareFixedExplicitIntegralBasisData
    (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
  let sigma := shiftedSquarePositiveRealPlaceEmbedding
    (shiftedSquareA h v) ha
  obtain ⟨p, hp, hpz⟩ :=
    (mem_main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage_iff
      htheta hY hi).mp hz
  let C := main3LargeAnalytic_blockFixedBasisEncodingCertificate
    htheta hY8 hi p
  have hpSpec :=
    main3LargeAnalytic_blockAuxiliaryArchimedeanCellPointFiber_spec
      htheta hY hi hp
  have hgeometry : InMain3LargeAnalyticArchimedeanCell
      (main3UnbalancedM theta Y) C.P (Sum.inl cell) := by
    simpa only [Main3LargeAnalyticBlockPointInArchimedeanCell, C, hY8]
      using hpSpec.2.2
  change ∃ ha' : shiftedSquareA h v < 0,
      InRealSquareMapCellPair
        (shiftedSquareEmbeddingScaleLoss (shiftedSquareA h v))
        (main3UnbalancedM theta Y) cell
          ((shiftedSquareSourceEmbeddingRatio C.P
            (shiftedSquarePositiveRealPlaceEmbedding
              (shiftedSquareA h v) ha')).re,
           (shiftedSquareTargetEmbeddingRatio C.P
            (shiftedSquarePositiveRealPlaceEmbedding
              (shiftedSquareA h v) ha')).re) at hgeometry
  obtain ⟨ha', hcell⟩ := hgeometry
  have hha : ha' = ha := Subsingleton.elim _ _
  subst ha'
  have hpointEq : main3ShiftedSquarePackagePoint C.P = z := by
    calc
      main3ShiftedSquarePackagePoint C.P =
          shiftedSquareCoordinateCodePoint C.encoded.code := by
        exact (congrArg shiftedSquareCoordinateCodePoint
          C.encoded_code_eq).symm
      _ = main3LargeAnalytic_blockCellCoordinatePoint htheta hY hi p := by
        have hsame :=
          main3LargeAnalytic_blockPointArchimedeanCellSelector_sameCertificate
            htheta hY hi p |>.2
        simp only [main3LargeAnalytic_blockCellCoordinatePoint]
        rw [hsame]
      _ = z := hpz
  have homega : C.P.omega = F.omega := by
    simpa only [C, F] using C.omega_eq
  have hratio :=
    main3ShiftedSquarePackagePoint_ratioPair_eq F C.P homega sigma
  have hratio' :
      (main3EmbeddingSourceRatio
          (sigma F.omega) (sigma (star F.omega)) z,
        main3EmbeddingTargetRatio
          (sigma F.omega) (sigma (star F.omega)) z) =
        (shiftedSquareSourceEmbeddingRatio C.P sigma,
          shiftedSquareTargetEmbeddingRatio C.P sigma) := by
    rw [← hpointEq]
    simpa only [main3ShiftedSquareEmbeddingOmega,
      main3ShiftedSquareEmbeddingOmegaBar] using hratio
  have hsourceEq :
      main3EmbeddingSourceRatio
          (sigma F.omega) (sigma (star F.omega)) z =
        shiftedSquareSourceEmbeddingRatio C.P sigma := by
    simpa using congrArg Prod.fst hratio'
  have htargetEq :
      main3EmbeddingTargetRatio
          (sigma F.omega) (sigma (star F.omega)) z =
        shiftedSquareTargetEmbeddingRatio C.P sigma := by
    simpa using congrArg Prod.snd hratio'
  have hgeo := shiftedSquare_positiveRealPlace_ratioGeometry ha C.P
  have hden :=
    main3ShiftedSquarePackagePoint_denominators_ne_zero
      F C.P homega sigma
  rw [hpointEq] at hden
  refine ⟨⟨hden.1, hden.2, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hsourceEq]
    exact hgeo.source_ratio_im_eq_zero
  · rw [htargetEq]
    exact hgeo.target_ratio_im_eq_zero
  · rw [hsourceEq]
    exact hgeo.source_ratio_re_ne_zero
  · rw [htargetEq]
    exact hgeo.target_ratio_re_pos
  · change InRealSquareMapCellPair
      (shiftedSquareEmbeddingScaleLoss (shiftedSquareA h v))
      (main3UnbalancedM theta Y) cell
        ((main3EmbeddingSourceRatio
          (sigma F.omega) (sigma (star F.omega)) z).re,
         (main3EmbeddingTargetRatio
          (sigma F.omega) (sigma (star F.omega)) z).re)
    rw [hsourceEq, htargetEq]
    exact hcell

/-- Exact alignment of a selected normalized embedding-ratio minor with the
real sheared-exponential determinant.  The hypotheses retain the signed
source centre and a positive normalized source coordinate. -/
theorem norm_det_main3RatioPowerEvaluationMatrix_selected_eq_abs_center_pow_mul_abs_sheared
    {ι : Type*} [Fintype ι]
    (B : ℕ) (omega omegaBar : ℂ)
    (points : ι → GeneralBidegreeFormPoint)
    (s : generalBidegreeFormIndex 1 B ↪ ι)
    (signedCentre : ℝ) (S T : ι → ℝ)
    (hS : ∀ r, 0 < S r) (hT : ∀ r, 0 < T r)
    (hsource : ∀ r,
      main3EmbeddingSourceRatio omega omegaBar (points r) =
        ((signedCentre * S r : ℝ) : ℂ))
    (htarget : ∀ r,
      main3EmbeddingTargetRatio omega omegaBar (points r) =
        ((signedCentre ^ 2 * T r : ℝ) : ℂ)) :
    ‖((main3RatioPowerEvaluationMatrix
        B omega omegaBar points).submatrix s id).det‖ =
      |signedCentre| ^ shearedCenterExponent 1 B *
        |((shearedExponentialEvaluationMatrix 1 B
          (fun r => S (s r)) (fun r => T (s r))).det)| := by
  let S' : generalBidegreeFormIndex 1 B → ℝ := fun r => S (s r)
  let T' : generalBidegreeFormIndex 1 B → ℝ := fun r => T (s r)
  have hmatrix :
      ((main3RatioPowerEvaluationMatrix
          B omega omegaBar points).submatrix s id) =
        (centeredAffineEvaluationMatrix 1 B signedCentre S' T').map
          (algebraMap ℝ ℂ) := by
    ext r ij
    simp only [Matrix.submatrix_apply, id_eq,
      main3RatioPowerEvaluationMatrix, main3RatioPowerMonomial,
      Matrix.map_apply, centeredAffineEvaluationMatrix, affineMonomialEntry,
      S', T']
    rw [hsource, htarget]
    norm_cast
  rw [hmatrix]
  have hdetMap := RingHom.map_det (algebraMap ℝ ℂ)
    (centeredAffineEvaluationMatrix 1 B signedCentre S' T')
  change
    (((centeredAffineEvaluationMatrix 1 B signedCentre S' T').det : ℝ) : ℂ) =
      ((centeredAffineEvaluationMatrix 1 B signedCentre S' T').map
        (algebraMap ℝ ℂ)).det at hdetMap
  rw [← hdetMap]
  rw [Complex.norm_real, Real.norm_eq_abs]
  have hcentered :=
    det_centeredAffineEvaluationMatrix_submatrix_eq_centerFactor_mul
      1 B signedCentre S' T' (fun r => hS (s r)) (fun r => hT (s r))
        (Function.Embedding.refl _)
  have hcenteredSub :
      (centeredAffineEvaluationMatrix 1 B signedCentre S' T').submatrix
          (Function.Embedding.refl _) id =
        centeredAffineEvaluationMatrix 1 B signedCentre S' T' := by
    ext r ij
    rfl
  have hshearedSub :
      (shearedExponentialEvaluationMatrix 1 B S' T').submatrix
          (Function.Embedding.refl _) id =
        shearedExponentialEvaluationMatrix 1 B S' T' := by
    ext r ij
    rfl
  rw [hcenteredSub, hshearedSub] at hcentered
  have hcentered' :
      (centeredAffineEvaluationMatrix 1 B signedCentre S' T').det =
        (∏ ab : generalBidegreeFormIndex 1 B,
          shearedCenterColumnScale (A := 1) (B := B) signedCentre ab) *
          (shearedExponentialEvaluationMatrix 1 B S' T').det := by
    exact hcentered
  rw [hcentered', abs_mul]
  rw [prod_shearedCenterColumnScale]
  rw [abs_pow]

/-- The exact radial/discriminant/centre multiplier times real two-layer fan
decay forces a selected integral minor to vanish. -/
theorem generalBidegreeMinor_det_eq_zero_of_realEmbeddingRatioFan_rate
    {ι : Type*} [Fintype ι]
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (B k : ℕ) (F : ShiftedSquareFixedExplicitIntegralBasisData a)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ)
    (points : ι → GeneralBidegreeFormPoint)
    (s : generalBidegreeFormIndex 1 B ↪ ι)
    (signedCentre : ℝ) (S T : ι → ℝ)
    (hsourceDen : ∀ r,
      ((points r).1.1 : ℂ) + sigma (star F.omega) *
        ((points r).1.2 : ℂ) ≠ 0)
    (htargetDen : ∀ r,
      ((points r).2.1 : ℂ) + sigma F.omega *
        ((points r).2.2 : ℂ) ≠ 0)
    (hS : ∀ r, 0 < S r) (hT : ∀ r, 0 < T r)
    (hsource : ∀ r,
      main3EmbeddingSourceRatio (sigma F.omega) (sigma (star F.omega))
          (points r) = ((signedCentre * S r : ℝ) : ℂ))
    (htarget : ∀ r,
      main3EmbeddingTargetRatio (sigma F.omega) (sigma (star F.omega))
          (points r) = ((signedCentre ^ 2 * T r : ℝ) : ℂ))
    (ellM ellX : ℝ)
    (hellM : 0 < ellM)
    (hkpos : 1 ≤ k) (hkB : k ≤ B)
    (hfanLower : (2 * (k : ℝ) - 1) * ellM ≤ ellX)
    (hfanUpper : ellX ≤ (2 * (k : ℝ) + 1) * ellM)
    (hlogS : ∀ r,
      |generalBidegreeReindexedLogS 1 B
        (generalBidegreeGridPointEquiv 1 B)
        (fun q => S (s q)) r| ≤ Real.exp (-ellM))
    (hlogDefect : ∀ r,
      |generalBidegreeReindexedShearedLogT 1 B
        (generalBidegreeGridPointEquiv 1 B)
        (fun q => S (s q)) (fun q => T (s q)) r| ≤ Real.exp (-ellX))
    (cost : ℝ)
    (hcost : main3RealSelectedRadialCenterDiscriminantCostFactor
      B F sigma points s signedCentre ≤ Real.exp cost)
    (hrate : cost +
        Real.log (Nat.factorial
          (Fintype.card (generalBidegreeGrid 1 B)) : ℝ) +
        twoLayerFanTaylorTail B *
          (Fintype.card (generalBidegreeGrid 1 B) : ℝ) <
      twoLayerWeight B k ellM ellX) :
    ((generalBidegreeFormEvaluationMatrix
      1 B points).submatrix s id).det = 0 := by
  let z := main3RealSelectedRadialCenterDiscriminantCostFactor
    B F sigma points s signedCentre
  let E := shearedExponentialEvaluationMatrix 1 B
    (fun r => S (s r)) (fun r => T (s r))
  have hz0 : 0 ≤ z :=
    main3RealSelectedRadialCenterDiscriminantCostFactor_nonneg
      B F sigma points s signedCentre
  have hE : |E.det| ≤
      (Nat.factorial (Fintype.card (generalBidegreeGrid 1 B)) : ℝ) *
        Real.exp (-twoLayerWeight B k ellM ellX) *
          (Real.exp (twoLayerFanTaylorTail B)) ^
            Fintype.card (generalBidegreeGrid 1 B) := by
    have h :=
      abs_det_reindex_shearedExponentialEvaluationMatrix_le_twoLayerFan_exp_tail
        B k (generalBidegreeGridPointEquiv 1 B)
          (fun r => S (s r)) (fun r => T (s r))
          ellM ellX hellM hkpos hkB hfanLower hfanUpper hlogS hlogDefect
    simpa only [E, Matrix.det_reindex_self, twoLayerFanTaylorTail] using h
  have hsmall : |z * E.det| < 1 :=
    abs_mul_lt_one_of_exp_cost_and_factorial_exp_decay
      (n := generalBidegreeGrid 1 B)
      cost (twoLayerWeight B k ellM ellX) (twoLayerFanTaylorTail B)
      z E.det (by simpa only [abs_of_nonneg hz0, z] using hcost) hE hrate
  apply integral_det_eq_zero_of_abs_cast_lt_one
  rw [abs_cast_det_generalBidegreeMinor_eq_radialDiscriminantCost_mul_norm_ratioPower
    B F sigma points s hsourceDen htargetDen]
  rw [norm_det_main3RatioPowerEvaluationMatrix_selected_eq_abs_center_pow_mul_abs_sheared
    B (sigma F.omega) (sigma (star F.omega)) points s signedCentre S T
      hS hT hsource htarget]
  rw [abs_mul, abs_of_nonneg hz0] at hsmall
  simpa only [z, E, main3RealSelectedRadialCenterDiscriminantCostFactor,
    main3ComplexSelectedRadialDiscriminantCostFactor, mul_assoc] using hsmall

/-! ## Specialization to the actual main3 real-cell image -/

/-- The source ratio of a literal block-cell image point at the fixed
positive real place. -/
noncomputable def main3LargeAnalyticRealCellSourceRatio
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (ha : shiftedSquareA h v < 0) (z : GeneralBidegreeFormPoint) : ℂ := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let F := shiftedSquareFixedExplicitIntegralBasisData
    (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
  let sigma := shiftedSquarePositiveRealPlaceEmbedding
    (shiftedSquareA h v) ha
  exact main3EmbeddingSourceRatio
    (sigma F.omega) (sigma (star F.omega)) z

/-- The target ratio of a literal block-cell image point at the fixed
positive real place. -/
noncomputable def main3LargeAnalyticRealCellTargetRatio
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (ha : shiftedSquareA h v < 0) (z : GeneralBidegreeFormPoint) : ℂ := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let F := shiftedSquareFixedExplicitIntegralBasisData
    (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
  let sigma := shiftedSquarePositiveRealPlaceEmbedding
    (shiftedSquareA h v) ha
  exact main3EmbeddingTargetRatio
    (sigma F.omega) (sigma (star F.omega)) z

/-- The common signed source centre determined by the real cell index. -/
def main3LargeAnalyticRealCellSignedCentre
    (theta : ℝ) (Y : ℕ) (h : ℤ) (v : ℕ)
    (cell : RealSquareMapCellPairIndex) : ℝ :=
  (cell.1.1 : ℝ) *
    annularMultiplicativeCenter
      (shiftedSquareEmbeddingScaleLoss (shiftedSquareA h v))
      (main3UnbalancedM theta Y) cell.1.2.1 cell.1.2.2

/-- The positive normalized source coordinate on an actual real cell. -/
noncomputable def main3LargeAnalyticRealCellNormalizedSource
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (ha : shiftedSquareA h v < 0) (cell : RealSquareMapCellPairIndex)
    (z : GeneralBidegreeFormPoint) : ℝ :=
  (main3LargeAnalyticRealCellSourceRatio hi ha z).re /
    main3LargeAnalyticRealCellSignedCentre theta Y h v cell

/-- The positive normalized target coordinate on an actual real cell. -/
noncomputable def main3LargeAnalyticRealCellNormalizedTarget
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (ha : shiftedSquareA h v < 0) (cell : RealSquareMapCellPairIndex)
    (z : GeneralBidegreeFormPoint) : ℝ :=
  (main3LargeAnalyticRealCellTargetRatio hi ha z).re /
    main3LargeAnalyticRealCellSignedCentre theta Y h v cell ^ 2

/-- The exact selected real-place cost on the literal fixed-key/fixed-cell
coordinate image.  It contains the reflected radial factors, the
discriminant divisor, and every signed-centre column factor. -/
noncomputable def main3LargeAnalyticRealCellSelectedCost
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey) (cell : RealSquareMapCellPairIndex)
    (ha : shiftedSquareA h v < 0) (B : ℕ)
    (s : generalBidegreeFormIndex 1 B ↪
      {z // z ∈
        main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
          htheta hY hi key (Sum.inl cell)}) : ℝ := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let F := shiftedSquareFixedExplicitIntegralBasisData
    (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
  let sigma := shiftedSquarePositiveRealPlaceEmbedding
    (shiftedSquareA h v) ha
  exact main3RealSelectedRadialCenterDiscriminantCostFactor
    B F sigma (fun z => z.1) s
      (main3LargeAnalyticRealCellSignedCentre theta Y h v cell)

/-- **Actual fixed-key/fixed-real-cell selected-minor endpoint.**

For any selected full bidegree-`(1,B)` minor of the literal coordinate-point
image, the displayed logarithmic fan bounds and one explicit bound on the
exact radial/discriminant/centre cost force the integral determinant to
vanish.  All realness, positivity, denominator, sign, and same-certificate
obligations are discharged from actual `Sum.inl` cell membership. -/
theorem main3LargeAnalytic_realCellCoordinatePointImage_selectedMinor_det_eq_zero_of_rate
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey) (cell : RealSquareMapCellPairIndex)
    (ha : shiftedSquareA h v < 0)
    (B k : ℕ)
    (s : generalBidegreeFormIndex 1 B ↪
      {z // z ∈
        main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
          htheta hY hi key (Sum.inl cell)})
    (ellM ellX : ℝ)
    (hellM : 0 < ellM)
    (hkpos : 1 ≤ k) (hkB : k ≤ B)
    (hfanLower : (2 * (k : ℝ) - 1) * ellM ≤ ellX)
    (hfanUpper : ellX ≤ (2 * (k : ℝ) + 1) * ellM)
    (hsourceScale :
      1 / (main3UnbalancedM theta Y : ℝ) ≤ Real.exp (-ellM))
    (hlogDefect : ∀ r,
      |generalBidegreeReindexedShearedLogT 1 B
        (generalBidegreeGridPointEquiv 1 B)
        (fun q => main3LargeAnalyticRealCellNormalizedSource
          hi ha cell (s q).1)
        (fun q => main3LargeAnalyticRealCellNormalizedTarget
          hi ha cell (s q).1) r| ≤ Real.exp (-ellX))
    (cost : ℝ)
    (hcost : main3LargeAnalyticRealCellSelectedCost
      htheta hY hi key cell ha B s ≤ Real.exp cost)
    (hrate : cost +
        Real.log (Nat.factorial
          (Fintype.card (generalBidegreeGrid 1 B)) : ℝ) +
        twoLayerFanTaylorTail B *
          (Fintype.card (generalBidegreeGrid 1 B) : ℝ) <
      twoLayerWeight B k ellM ellX) :
    ((generalBidegreeFormEvaluationMatrix 1 B
      (fun z : {z // z ∈
        main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
          htheta hY hi key (Sum.inl cell)} => z.1)).submatrix s id).det = 0 := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let F := shiftedSquareFixedExplicitIntegralBasisData
    (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
  let sigma := shiftedSquarePositiveRealPlaceEmbedding
    (shiftedSquareA h v) ha
  let pointType := {z // z ∈
    main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
      htheta hY hi key (Sum.inl cell)}
  let points : pointType → GeneralBidegreeFormPoint := fun z => z.1
  let signedCentre :=
    main3LargeAnalyticRealCellSignedCentre theta Y h v cell
  let S : pointType → ℝ := fun z =>
    main3LargeAnalyticRealCellNormalizedSource hi ha cell z.1
  let T : pointType → ℝ := fun z =>
    main3LargeAnalyticRealCellNormalizedTarget hi ha cell z.1
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
      (pow_pos (by
        unfold localRatioMeshStep
        positivity) _)
  have hMpos : 0 < main3UnbalancedM theta Y :=
    (main3UnbalancedM_parameter_package theta Y htheta (by omega)).1
  have hMreal : (1 : ℝ) ≤ (main3UnbalancedM theta Y : ℝ) := by
    exact_mod_cast hMpos
  have hgeometry : ∀ z : pointType,
      let source := main3EmbeddingSourceRatio
        (sigma F.omega) (sigma (star F.omega)) (points z)
      let target := main3EmbeddingTargetRatio
        (sigma F.omega) (sigma (star F.omega)) (points z)
      (((((points z).1.1 : ℂ) + sigma (star F.omega) *
            ((points z).1.2 : ℂ) ≠ 0) ∧
        (((points z).2.1 : ℂ) + sigma F.omega *
            ((points z).2.2 : ℂ) ≠ 0) ∧
        source.im = 0 ∧ target.im = 0 ∧ source.re ≠ 0 ∧
          0 < target.re) ∧
        InRealSquareMapCellPair
          (shiftedSquareEmbeddingScaleLoss (shiftedSquareA h v))
          (main3UnbalancedM theta Y) cell (source.re, target.re)) := by
    intro z
    simpa only [F, sigma, points, pointType] using
      main3LargeAnalytic_realCellCoordinatePointImage_embeddingRatio_geometry
        htheta hY hi key cell ha z.property
  have hsignedCentre : ∀ z : pointType, signedCentre ≠ 0 := by
    intro z
    have hg := hgeometry z
    rcases hg with
      ⟨⟨_hdenSource, _hdenTarget, _hsourceIm, _htargetIm,
        hsourceNe, _htargetPos⟩, hcell⟩
    rcases hcell.1 with ⟨hsignEq, _hlower, _hupper⟩
    have hsignEq' :
      (main3EmbeddingSourceRatio
        (sigma F.omega) (sigma (star F.omega)) (points z)).re =
          (cell.1.1 : ℝ) *
            |(main3EmbeddingSourceRatio
              (sigma F.omega) (sigma (star F.omega)) (points z)).re| := by
      simpa using hsignEq
    have hsign : (cell.1.1 : ℝ) ≠ 0 := by
      intro hzero
      apply hsourceNe
      rw [hsignEq', hzero, zero_mul]
    dsimp only [signedCentre,
      main3LargeAnalyticRealCellSignedCentre, centre]
    exact mul_ne_zero hsign hcentre.ne'
  have hSWindow : ∀ z : pointType,
      1 ≤ S z ∧ S z ≤ 1 + 1 / (main3UnbalancedM theta Y : ℝ) := by
    intro z
    have hg := hgeometry z
    rcases hg with
      ⟨⟨_hdenSource, _hdenTarget, _hsourceIm, _htargetIm,
        _hsourceNe, _htargetPos⟩, hcell⟩
    rcases hcell.1 with ⟨hsignEq, hlower, hupper⟩
    have hsignEq' :
      (main3EmbeddingSourceRatio
        (sigma F.omega) (sigma (star F.omega)) (points z)).re =
          (cell.1.1 : ℝ) *
            |(main3EmbeddingSourceRatio
              (sigma F.omega) (sigma (star F.omega)) (points z)).re| := by
      simpa using hsignEq
    have hlower' : centre ≤
        |(main3EmbeddingSourceRatio
          (sigma F.omega) (sigma (star F.omega)) (points z)).re| := by
      simpa using hlower
    have hupper' :
        |(main3EmbeddingSourceRatio
          (sigma F.omega) (sigma (star F.omega)) (points z)).re| ≤
          centre * (1 + 1 / (main3UnbalancedM theta Y : ℝ)) := by
      simpa only [Prod.fst, centre, localRatioMeshStep] using hupper
    have habsPos : 0 <
        |(main3EmbeddingSourceRatio
          (sigma F.omega) (sigma (star F.omega)) (points z)).re| :=
      hcentre.trans_le hlower'
    have hsign : (cell.1.1 : ℝ) ≠ 0 := by
      intro hzero
      apply _hsourceNe
      calc
        (main3EmbeddingSourceRatio
            (sigma F.omega) (sigma (star F.omega)) (points z)).re =
            (cell.1.1 : ℝ) *
              |(main3EmbeddingSourceRatio
                (sigma F.omega) (sigma (star F.omega)) (points z)).re| :=
          hsignEq'
        _ = 0 := by rw [hzero, zero_mul]
    have hquot :
        ((cell.1.1 : ℝ) *
            |(main3EmbeddingSourceRatio
              (sigma F.omega) (sigma (star F.omega)) (points z)).re|) /
            ((cell.1.1 : ℝ) * centre) =
          |(main3EmbeddingSourceRatio
            (sigma F.omega) (sigma (star F.omega)) (points z)).re| /
            centre := by
      field_simp [hsign, hcentre.ne']
    have hSvalue : S z =
        |(main3EmbeddingSourceRatio
          (sigma F.omega) (sigma (star F.omega)) (points z)).re| /
            centre := by
      change
        (main3EmbeddingSourceRatio
          (sigma F.omega) (sigma (star F.omega)) (points z)).re /
            ((cell.1.1 : ℝ) * centre) = _
      trans
        ((cell.1.1 : ℝ) *
            |(main3EmbeddingSourceRatio
              (sigma F.omega) (sigma (star F.omega)) (points z)).re|) /
          ((cell.1.1 : ℝ) * centre)
      · exact congrArg (fun x : ℝ =>
          x / ((cell.1.1 : ℝ) * centre)) hsignEq'
      · exact hquot
    rw [hSvalue]
    constructor
    · exact (le_div_iff₀ hcentre).2 (by simpa using hlower')
    · exact (div_le_iff₀ hcentre).2 (by simpa [mul_comm] using hupper')
  have hS : ∀ z : pointType, 0 < S z := by
    intro z
    exact zero_lt_one.trans_le (hSWindow z).1
  have hT : ∀ z : pointType, 0 < T z := by
    intro z
    have hg := hgeometry z
    rcases hg with
      ⟨⟨_hdenSource, _hdenTarget, _hsourceIm, _htargetIm,
        _hsourceNe, htargetPos⟩, _hcell⟩
    dsimp only [T, main3LargeAnalyticRealCellNormalizedTarget,
      main3LargeAnalyticRealCellTargetRatio, signedCentre,
      F, sigma, points]
    exact div_pos htargetPos (sq_pos_of_ne_zero (hsignedCentre z))
  have hsourceDen : ∀ z : pointType,
      ((points z).1.1 : ℂ) + sigma (star F.omega) *
        ((points z).1.2 : ℂ) ≠ 0 := by
    intro z
    exact (hgeometry z).1.1
  have htargetDen : ∀ z : pointType,
      ((points z).2.1 : ℂ) + sigma F.omega *
        ((points z).2.2 : ℂ) ≠ 0 := by
    intro z
    exact (hgeometry z).1.2.1
  have hsource : ∀ z : pointType,
      main3EmbeddingSourceRatio (sigma F.omega) (sigma (star F.omega))
          (points z) = ((signedCentre * S z : ℝ) : ℂ) := by
    intro z
    have him := (hgeometry z).1.2.2.1
    have hreal :
        main3EmbeddingSourceRatio
            (sigma F.omega) (sigma (star F.omega)) (points z) =
          ((main3EmbeddingSourceRatio
            (sigma F.omega) (sigma (star F.omega)) (points z)).re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using him
    rw [hreal]
    norm_cast
    change
      (main3EmbeddingSourceRatio
          (sigma F.omega) (sigma (star F.omega)) (points z)).re =
        signedCentre *
          ((main3EmbeddingSourceRatio
            (sigma F.omega) (sigma (star F.omega)) (points z)).re /
              signedCentre)
    field_simp [hsignedCentre z]
  have htarget : ∀ z : pointType,
      main3EmbeddingTargetRatio (sigma F.omega) (sigma (star F.omega))
          (points z) = ((signedCentre ^ 2 * T z : ℝ) : ℂ) := by
    intro z
    have him := (hgeometry z).1.2.2.2.1
    have hreal :
        main3EmbeddingTargetRatio
            (sigma F.omega) (sigma (star F.omega)) (points z) =
          ((main3EmbeddingTargetRatio
            (sigma F.omega) (sigma (star F.omega)) (points z)).re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using him
    rw [hreal]
    norm_cast
    change
      (main3EmbeddingTargetRatio
          (sigma F.omega) (sigma (star F.omega)) (points z)).re =
        signedCentre ^ 2 *
          ((main3EmbeddingTargetRatio
            (sigma F.omega) (sigma (star F.omega)) (points z)).re /
              signedCentre ^ 2)
    field_simp [hsignedCentre z]
  apply generalBidegreeMinor_det_eq_zero_of_realEmbeddingRatioFan_rate
    B k F sigma points s signedCentre S T hsourceDen htargetDen hS hT
      hsource htarget ellM ellX hellM hkpos hkB hfanLower hfanUpper
  · intro r
    change |Real.log
      (S (s ((generalBidegreeGridPointEquiv 1 B).symm r)))| ≤
        Real.exp (-ellM)
    exact
      (abs_log_le_one_div_of_one_le_le_one_add_one_div
        hMreal
        (hSWindow (s ((generalBidegreeGridPointEquiv 1 B).symm r))).1
        (hSWindow (s ((generalBidegreeGridPointEquiv 1 B).symm r))).2).trans
          hsourceScale
  · simpa only [S, T, points, pointType] using hlogDefect
  · simpa only [main3LargeAnalyticRealCellSelectedCost, F, sigma,
      points, pointType, signedCentre] using hcost
  · exact hrate

end

end PellPaper
