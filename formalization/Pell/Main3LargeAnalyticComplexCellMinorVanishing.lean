import Pell.Main3LargeAnalyticComplexRadialLedger
import Pell.Main3ComplexEmbeddingMinorVanishing
import Pell.Main3ShiftedSquareEmbeddingRatioCoordinateAdapter
import Mathlib.Tactic

/-!
# Actual fixed-key complex-cell selected-minor vanishing

This module completes the same-certificate geometric handoff for a literal
`Sum.inr` cell and composes the checked radial ledger, fan selection, and
complex determinant estimate.  The pointwise error is kept as the actual
target-minus-source-square norm; its mesh and defect-scale bounds are derived
from the original shifted-square row, not from the coarser cell diameter.
-/

namespace PellPaper

noncomputable section

local instance main3LargeAnalyticComplexCellMinorVanishing_numberField
    (a : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

/-- Every literal point in a fixed positive-shift complex cell retains the
same normalized package used to build its integral coordinate code.  Hence
both reflected denominators are nonzero, the determinant ratios lie in the
selected cell, and the actual square-map defect satisfies both logarithmic
scales needed by the complex fan theorem. -/
theorem main3LargeAnalytic_complexCellCoordinatePointImage_embeddingRatio_geometry
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : ComplexUnitCircleSlopeCellIndex)
    (ha : 0 < shiftedSquareA h v)
    {z : GeneralBidegreeFormPoint}
    (hz : z ∈
      main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
        htheta hY hi key (Sum.inr cell)) :
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    let F := shiftedSquareFixedExplicitIntegralBasisData
      (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
    let sigma := shiftedSquareImaginaryPlaceEmbedding
      (shiftedSquareA h v) ha
    let source := main3EmbeddingSourceRatio
      (sigma F.omega) (sigma (star F.omega)) z
    let target := main3EmbeddingTargetRatio
      (sigma F.omega) (sigma (star F.omega)) z
    (((z.1.1 : ℂ) + sigma (star F.omega) * (z.1.2 : ℂ) ≠ 0) ∧
      ((z.2.1 : ℂ) + sigma F.omega * (z.2.2 : ℂ) ≠ 0) ∧
      InComplexUnitCircleSquareMapCellPair
        (main3UnbalancedM theta Y) cell (source, target) ∧
      ‖target - source ^ 2‖ ≤
        1 / (main3UnbalancedM theta Y : ℝ) ∧
      (3 / 2 : ℝ) * ‖target - source ^ 2‖ ≤
        Real.exp
          (-main3ComplexDefectLogScale (shiftedSquareA h v) N)) := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let hY8 : 8 ≤ Y := by omega
  let F := shiftedSquareFixedExplicitIntegralBasisData
    (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
  let sigma := shiftedSquareImaginaryPlaceEmbedding
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
      (main3UnbalancedM theta Y) C.P (Sum.inr cell) := by
    simpa only [Main3LargeAnalyticBlockPointInArchimedeanCell, C, hY8]
      using hpSpec.2.2
  change ∃ ha' : 0 < shiftedSquareA h v,
      InComplexUnitCircleSquareMapCellPair
        (main3UnbalancedM theta Y) cell
          (shiftedSquareSourceEmbeddingRatio C.P
            (shiftedSquareImaginaryPlaceEmbedding
              (shiftedSquareA h v) ha'),
           shiftedSquareTargetEmbeddingRatio C.P
            (shiftedSquareImaginaryPlaceEmbedding
              (shiftedSquareA h v) ha')) at hgeometry
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
  have hden :=
    main3ShiftedSquarePackagePoint_denominators_ne_zero
      F C.P homega sigma
  rw [hpointEq] at hden
  have hgeo := shiftedSquare_imaginaryPlace_ratioGeometry ha C.P
  have hquotient := shiftedSquare_embeddingRatio_quotientError
    C.scaled.base.shift_dominance C.P sigma
  have hactual :
      ‖shiftedSquareTargetEmbeddingRatio C.P sigma -
          shiftedSquareSourceEmbeddingRatio C.P sigma ^ 2‖ ≤
        (8 * Real.sqrt |(shiftedSquareA h v : ℝ)|) /
          (p.1.2.2 : ℝ) := by
    exact norm_target_sub_source_sq_le_of_unit_quotientError
      hgeo.source_ratio_norm_eq_one hquotient
  have hmesh :=
    main3LargeAnalytic_quotientError_le_inv_unbalancedMesh
      htheta hY hi p.2
  obtain ⟨_hd, _hw, hn, _hDd, _hdD, _hYw, _hwY,
      hNn, hnN, _heq, _hsquarefree⟩ :=
    (mem_squarefreeShiftedSquareBlock.mp p.2)
  have hNpos : 0 < N := by omega
  have hdefectRaw :=
    three_halves_mul_shiftedSquareError_le_exp_neg_defectLogScale
      ha.ne' hNpos hNn
  have hactualMesh :
      ‖main3EmbeddingTargetRatio
          (sigma F.omega) (sigma (star F.omega)) z -
        main3EmbeddingSourceRatio
          (sigma F.omega) (sigma (star F.omega)) z ^ 2‖ ≤
        1 / (main3UnbalancedM theta Y : ℝ) := by
    rw [hsourceEq, htargetEq]
    exact hactual.trans hmesh
  have hactualDefect :
      (3 / 2 : ℝ) *
          ‖main3EmbeddingTargetRatio
              (sigma F.omega) (sigma (star F.omega)) z -
            main3EmbeddingSourceRatio
              (sigma F.omega) (sigma (star F.omega)) z ^ 2‖ ≤
        Real.exp
          (-main3ComplexDefectLogScale (shiftedSquareA h v) N) := by
    rw [hsourceEq, htargetEq]
    exact (mul_le_mul_of_nonneg_left hactual (by norm_num)).trans hdefectRaw
  refine ⟨hden.1, hden.2, ?_, hactualMesh, hactualDefect⟩
  change InComplexUnitCircleSquareMapCellPair
    (main3UnbalancedM theta Y) cell
      (main3EmbeddingSourceRatio
          (sigma F.omega) (sigma (star F.omega)) z,
       main3EmbeddingTargetRatio
          (sigma F.omega) (sigma (star F.omega)) z)
  rw [hsourceEq, htargetEq]
  exact hcell

/-- The literal complex cell supporting a selected full row family belongs
to the finite complex index set. -/
theorem main3LargeAnalytic_selectedComplexCell_mem
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
    cell ∈ complexUnitCircleSlopeCellIndices
      (main3UnbalancedM theta Y) := by
  let r0 : generalBidegreeFormIndex 1 B :=
    (⟨0, by omega⟩, ⟨0, by omega⟩)
  have hz := (s r0).2
  obtain ⟨p, _hp, _hkey, hselector, _hgeometry, _hcode, _hpoint⟩ :=
    main3LargeAnalytic_blockCellCoordinatePointImage_sameCertificate
      htheta hY hi hz
  have hmem :=
    main3LargeAnalytic_blockPointArchimedeanCellSelector_mem
      htheta hY hi p
  rw [hselector] at hmem
  exact mem_main3LargeAnalytic_archimedeanCellIndices_inr.mp hmem

/-- At the standing base threshold the unbalanced complex mesh has at least
ten cells in each unit scale, as required by the principal-log chart. -/
theorem ten_le_main3UnbalancedM
    {theta : ℝ} {Y : ℕ} (htheta : 3 ≤ theta) (hY : 65536 ≤ Y) :
    10 ≤ main3UnbalancedM theta Y := by
  let a := main3UnbalancedMExponent theta
  let M := main3UnbalancedM theta Y
  have hYone : (1 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast (show 1 ≤ Y by omega)
  have haLower : (1 / 2 : ℝ) ≤ a := by
    have h := (main3UnbalancedMExponent_mem htheta).1
    dsimp only [a]
    linarith
  have hpow := Real.rpow_le_rpow_of_exponent_le hYone haLower
  have hsqrt : (256 : ℝ) ≤ Real.sqrt (Y : ℝ) := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 256)]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hY)
  have hceil : (Y : ℝ) ^ a ≤ (M : ℝ) := by
    dsimp only [M, main3UnbalancedM]
    exact Nat.le_ceil ((Y : ℝ) ^ main3UnbalancedMExponent theta)
  have h256 : (256 : ℝ) ≤ (M : ℝ) := by
    calc
      (256 : ℝ) ≤ Real.sqrt (Y : ℝ) := hsqrt
      _ = (Y : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
      _ ≤ (Y : ℝ) ^ a := hpow
      _ ≤ (M : ℝ) := hceil
  exact_mod_cast (show (10 : ℝ) ≤ (M : ℝ) by linarith)

/-- **Actual fixed-key/fixed-complex-cell selected-minor endpoint.**

For every selected full bidegree-`(1,B)` minor, with the manuscript choice
`B=ceil(theta^2)`, the standard fixed-cost growth threshold supplies the fan,
the exact radial ledger supplies its cost, and the same-certificate row
geometry supplies both localization scales.  Therefore the integral minor
vanishes without any remaining project-specific analytic premise. -/
theorem main3LargeAnalytic_complexCellCoordinatePointImage_selectedMinor_det_eq_zero
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hYgrow : Real.exp (800 * theta ^ 2) < (Y : ℝ))
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (ha : 0 < shiftedSquareA h v)
    (key : ShiftedSquareAuxiliaryKey)
    (cell : ComplexUnitCircleSlopeCellIndex)
    (s : generalBidegreeFormIndex 1 (main3BalancedDegree theta) ↪
      {z // z ∈
        main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
          htheta hY hi key (Sum.inr cell)}) :
    ((generalBidegreeFormEvaluationMatrix 1 (main3BalancedDegree theta)
      (fun z : {z // z ∈
        main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
          htheta hY hi key (Sum.inr cell)} => z.1)).submatrix s id).det = 0 := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let B := main3BalancedDegree theta
  let M := main3UnbalancedM theta Y
  let a := shiftedSquareA h v
  let F := shiftedSquareFixedExplicitIntegralBasisData
    a (main3LargeAnalytic_shift_squarefree hi)
  let sigma := shiftedSquareImaginaryPlaceEmbedding a ha
  let pointType := {z // z ∈
    main3LargeAnalytic_blockAuxiliaryArchimedeanCellCoordinatePointImage
      htheta hY hi key (Sum.inr cell)}
  let points : pointType → GeneralBidegreeFormPoint := fun z => z.1
  let source : pointType → ℂ := fun z =>
    main3EmbeddingSourceRatio
      (sigma F.omega) (sigma (star F.omega)) (points z)
  let target : pointType → ℂ := fun z =>
    main3EmbeddingTargetRatio
      (sigma F.omega) (sigma (star F.omega)) (points z)
  let epsilon : pointType → ℝ := fun z => ‖target z - source z ^ 2‖
  let ellM := main3ComplexSourceLogScale M
  let ellX := main3ComplexDefectLogScale a N
  let cost :=
    twoLayerBalancedDoubledBaseLogCost B
        (Real.log (N : ℝ) / Real.log (Y : ℝ)) (Real.log (Y : ℝ)) +
      ((B : ℝ) * ((B : ℝ) + 1) / 2) * Real.log |(a : ℝ)| +
      main3ComplexRadialFixedLogCost B
  let r0 : generalBidegreeFormIndex 1 B :=
    (⟨0, by omega⟩, ⟨0, by omega⟩)
  let centre : ℂ := source (s r0)
  have hM10 : 10 ≤ M := by
    simpa only [M] using ten_le_main3UnbalancedM htheta hY
  have hMpos : 0 < M := by omega
  have hiCell : cell ∈ complexUnitCircleSlopeCellIndices M := by
    simpa only [M, B] using
      main3LargeAnalytic_selectedComplexCell_mem htheta hY hi key cell s
  have hgeometry : ∀ z : pointType,
      (((points z).1.1 : ℂ) + sigma (star F.omega) *
            ((points z).1.2 : ℂ) ≠ 0) ∧
        (((points z).2.1 : ℂ) + sigma F.omega *
            ((points z).2.2 : ℂ) ≠ 0) ∧
        InComplexUnitCircleSquareMapCellPair M cell
          (source z, target z) ∧
        epsilon z ≤ 1 / (M : ℝ) ∧
        (3 / 2 : ℝ) * epsilon z ≤ Real.exp (-ellX) := by
    intro z
    simpa only [F, sigma, points, pointType, source, target, epsilon,
      M, a, ellX] using
      main3LargeAnalytic_complexCellCoordinatePointImage_embeddingRatio_geometry
        htheta hY hi key cell ha z.property
  have hsourceDen : ∀ z : pointType,
      (((points z).1.1 : ℂ) + sigma (star F.omega) *
        ((points z).1.2 : ℂ) ≠ 0) := fun z => (hgeometry z).1
  have htargetDen : ∀ z : pointType,
      (((points z).2.1 : ℂ) + sigma F.omega *
        ((points z).2.2 : ℂ) ≠ 0) := fun z => (hgeometry z).2.1
  have hcell : ∀ z : pointType,
      InComplexUnitCircleSquareMapCellPair M cell
        (source z, target z) := fun z => (hgeometry z).2.2.1
  have hcentre : InComplexUnitCircleSlopeCell M cell centre := by
    exact (hcell (s r0)).1
  have herror : ∀ z : pointType,
      ‖target z - source z ^ 2‖ ≤ epsilon z := fun _ => le_rfl
  have hepsilonMesh : ∀ z : pointType,
      epsilon z ≤ 1 / (M : ℝ) := fun z => (hgeometry z).2.2.2.1
  have hdefectScale : ∀ z : pointType,
      (3 / 2 : ℝ) * epsilon z ≤ Real.exp (-ellX) :=
    fun z => (hgeometry z).2.2.2.2
  have hsourceScale : 3 / (M : ℝ) ≤ Real.exp (-ellM) := by
    rw [exp_neg_main3ComplexSourceLogScale_eq hMpos]
  have hellM : 0 < ellM := by
    dsimp only [ellM]
    exact main3ComplexSourceLogScale_pos (by omega)
  have hradial :
      main3ComplexSelectedRadialDiscriminantCostFactor
          B F sigma points s ≤ Real.exp cost := by
    simpa only [B, F, sigma, points, pointType, cost, a] using
      main3LargeAnalytic_complexCellCoordinatePointImage_selectedRadialDiscriminantCostFactor_le_exp_radialLedger
        htheta hY hi ha key cell s
  have hcostLedger :
      cost ≤
        twoLayerBalancedDoubledBaseLogCost B
            (Real.log (N : ℝ) / Real.log (Y : ℝ))
            (Real.log (Y : ℝ)) +
          ((B : ℝ) * ((B : ℝ) + 1) / 2) *
            Real.log |(a : ℝ)| +
          main3ComplexRadialFixedLogCost B := by
    rfl
  obtain ⟨k, hkpos, hkB, hfanLower, hfanUpper, hrate⟩ :=
    exists_main3LargeAnalytic_complexFanIndex_and_rate_of_radialLedger
      htheta hY hYgrow hi ha cost
        (by simpa only [B, a] using hcostLedger)
  exact generalBidegreeMinor_det_eq_zero_of_mem_complexSquareMapCell_rate
    hM10 hiCell B k F sigma centre points s hsourceDen htargetDen
      (by simpa only [source, target] using hcell) hcentre epsilon
      (by simpa only [source, target] using herror) hepsilonMesh ellM ellX
      hsourceScale hdefectScale hellM hkpos hkB hfanLower hfanUpper cost
      hradial hrate

end

end PellPaper
