import Pell.PrimitiveWedgeReducedTargetCoverShortVector
import Mathlib.Tactic

/-!
# The complex-cover first minimum in original target coordinates

The reduced-cover first column need not belong to the finite target image.
This module therefore bounds its imaginary-place target norm using only the
exact normalized radial/wedge identity, the Hermitian anchor, and the exact
discriminant factor.  No pointwise target-set norm estimate is applied to the
short vector.
-/

namespace PellPaper

open scoped MatrixGroups ComplexConjugate

noncomputable section

local instance main3LargeAnalyticComplexCoverShortestVectorBound_numberField
    (a : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

/-- At the explicit imaginary place, applying the conjugate integral-basis
generator to an integral column is complex conjugation of the original
target linear form. -/
@[simp]
theorem main3IntegralTargetLinearForm_imaginaryPlace_star_eq_conj
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (F : ShiftedSquareFixedExplicitIntegralBasisData a)
    (ha : 0 < a) (y : Fin 2 → ℤ) :
    main3IntegralTargetLinearForm
        (shiftedSquareImaginaryPlaceEmbedding a ha (star F.omega)) y =
      conj (main3IntegralTargetLinearForm
        (shiftedSquareImaginaryPlaceEmbedding a ha F.omega) y) := by
  change ((y 0 : ℤ) : ℂ) +
      shiftedSquareImaginaryPlaceEmbedding a ha (star F.omega) *
        ((y 1 : ℤ) : ℂ) =
    conj (((y 0 : ℤ) : ℂ) +
      shiftedSquareImaginaryPlaceEmbedding a ha F.omega *
        ((y 1 : ℤ) : ℂ))
  rw [shiftedSquareImaginaryPlaceEmbedding_star]
  simp

/-- Elementary Hermitian reconstruction: control of the real component and
of the alternating conjugate cross product controls the full second vector.
The anchor lower bound is deliberately stated in the exact form supplied by
the complex radial certificate. -/
private theorem complex_second_norm_sq_le_of_re_cross
    (a b : ℂ) (E mu : ℝ)
    (hE : 0 < E) (hmu : 0 ≤ mu)
    (hanchor : E ≤ 2 * ‖a‖ ^ 2)
    (hre : |(conj a * b).re| ≤ E * mu / 2)
    (hcross : ‖conj a * b - conj b * a‖ ≤ E * mu / 2) :
    ‖b‖ ^ 2 ≤ (5 / 8 : ℝ) * E * mu ^ 2 := by
  let q : ℂ := conj a * b
  have hcrossQ : ‖q - conj q‖ ≤ E * mu / 2 := by
    calc
      ‖q - conj q‖ = ‖conj a * b - conj b * a‖ := by
        congr 1
        dsimp only [q]
        rw [map_mul]
        simp only [starRingEnd_apply, star_star]
        ring
      _ ≤ E * mu / 2 := hcross
  have himTwo : |2 * q.im| ≤ ‖q - conj q‖ := by
    calc
      |2 * q.im| = |(q - conj q).im| := by
        congr 1
        simp
        ring
      _ ≤ ‖q - conj q‖ := Complex.abs_im_le_norm _
  have him : |q.im| ≤ E * mu / 4 := by
    have h := himTwo.trans hcrossQ
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at h
    nlinarith
  have hre' : |q.re| ≤ E * mu / 2 := by
    simpa only [q] using hre
  have hEmu0 : 0 ≤ E * mu := mul_nonneg hE.le hmu
  have hreSq : q.re ^ 2 ≤ (E * mu / 2) ^ 2 := by
    have hsquare := (sq_le_sq₀ (abs_nonneg q.re)
      (div_nonneg hEmu0 (by norm_num))).2 hre'
    simpa only [sq_abs] using hsquare
  have himSq : q.im ^ 2 ≤ (E * mu / 4) ^ 2 := by
    have hsquare := (sq_le_sq₀ (abs_nonneg q.im)
      (div_nonneg hEmu0 (by norm_num))).2 him
    simpa only [sq_abs] using hsquare
  have hq : ‖q‖ ^ 2 ≤ (5 / 16 : ℝ) * E ^ 2 * mu ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith
  have hqProduct : ‖q‖ ^ 2 = ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
    dsimp only [q]
    rw [norm_mul, Complex.norm_conj]
    ring
  have hanchorScaled : E * ‖b‖ ^ 2 ≤
      2 * (‖a‖ ^ 2 * ‖b‖ ^ 2) := by
    have h := mul_le_mul_of_nonneg_right hanchor (sq_nonneg ‖b‖)
    nlinarith
  have hscaled : E * ‖b‖ ^ 2 ≤
      E * ((5 / 8 : ℝ) * E * mu ^ 2) := by
    calc
    E * ‖b‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 * ‖b‖ ^ 2) := hanchorScaled
    _ = 2 * ‖q‖ ^ 2 := by rw [hqProduct]
    _ ≤ 2 * ((5 / 16 : ℝ) * E ^ 2 * mu ^ 2) := by gcongr
    _ = E * ((5 / 8 : ℝ) * E * mu ^ 2) := by ring
  exact le_of_mul_le_mul_left hscaled hE

/-- For any complex radial certificate and the exact same reduced-cover
witnesses `G,H`, the product-basis first column has imaginary-place norm
square at most `(5/8) E mu^2`.  The second conclusion is the division-free
threshold form, followed by the equivalent positive-threshold quotient
bound. -/
theorem PrimitiveWedgeReducedTargetCoverSpec.complex_shortest_original_vector_norm_sq_bounds
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (F : ShiftedSquareFixedExplicitIntegralBasisData a)
    (ha : 0 < a)
    {T : Finset (Fin 2 → ℤ)} {E Mmesh : ℝ}
    (hE : 0 < E) (hMmesh : 6 ≤ Mmesh)
    (cert : PrimitiveWedgeReducedTargetCoverCertificate T E
      ((6 * E / Mmesh) /
        Real.sqrt |(NumberField.discr
          (rationalQuadraticAlgebra (-a)) : ℝ)|) 2)
    (hell : cert.ell = main3AnchorHermitianRadialAddHom 1
      (shiftedSquareImaginaryPlaceEmbedding a ha F.omega) cert.anchor)
    (hrhoLower : E ≤ 2 * cert.ell cert.anchor)
    {G H : SL(2, ℤ)}
    (hspec : PrimitiveWedgeReducedTargetCoverSpec
      T cert.ell cert.anchor E
        ((6 * E / Mmesh) /
          Real.sqrt |(NumberField.discr
            (rationalQuadraticAlgebra (-a)) : ℝ)|) 2 G H) :
    let Delta := Real.sqrt |(NumberField.discr
      (rationalQuadraticAlgebra (-a)) : ℝ)|
    let K := (6 * E / Mmesh) / Delta
    let rho := cert.ell cert.anchor
    let U := K / 2
    let V := 1 + (2 : ℝ) / 2
    let M₀ := 2 * rho * V / E
    let beta := cert.ell (fun i ↦ G i 1)
    let z := -K * beta / E
    let mu := firstSlopeSupNorm U V M₀ z
    let y := primitiveWedgeReducedTargetCoverShortestVector G H
    ‖main3IntegralTargetLinearForm
        (shiftedSquareImaginaryPlaceEmbedding a ha F.omega) y‖ ^ 2 ≤
        (5 / 8 : ℝ) * E * mu ^ 2 ∧
      (∀ S : ℝ, 0 ≤ S → S ≤ 1 / mu →
        S ^ 2 * ‖main3IntegralTargetLinearForm
          (shiftedSquareImaginaryPlaceEmbedding a ha F.omega) y‖ ^ 2 ≤
            (5 / 8 : ℝ) * E) ∧
      (∀ S : ℝ, 0 < S → S ≤ 1 / mu →
        ‖main3IntegralTargetLinearForm
          (shiftedSquareImaginaryPlaceEmbedding a ha F.omega) y‖ ^ 2 ≤
            ((5 / 8 : ℝ) * E) / S ^ 2) := by
  dsimp only
  let sigma := shiftedSquareImaginaryPlaceEmbedding a ha
  let Delta := Real.sqrt |(NumberField.discr
    (rationalQuadraticAlgebra (-a)) : ℝ)|
  let K := (6 * E / Mmesh) / Delta
  let rho := cert.ell cert.anchor
  let U := K / 2
  let V := 1 + (2 : ℝ) / 2
  let M₀ := 2 * rho * V / E
  let beta := cert.ell (fun i ↦ G i 1)
  let z := -K * beta / E
  let mu := firstSlopeSupNorm U V M₀ z
  let y := primitiveWedgeReducedTargetCoverShortestVector G H
  change ‖main3IntegralTargetLinearForm (sigma F.omega) y‖ ^ 2 ≤
      (5 / 8 : ℝ) * E * mu ^ 2 ∧
    (∀ S : ℝ, 0 ≤ S → S ≤ 1 / mu →
      S ^ 2 * ‖main3IntegralTargetLinearForm (sigma F.omega) y‖ ^ 2 ≤
        (5 / 8 : ℝ) * E) ∧
    (∀ S : ℝ, 0 < S → S ≤ 1 / mu →
      ‖main3IntegralTargetLinearForm (sigma F.omega) y‖ ^ 2 ≤
        ((5 / 8 : ℝ) * E) / S ^ 2)
  have hdiscZ : NumberField.discr (rationalQuadraticAlgebra (-a)) ≠ 0 :=
    NumberField.discr_ne_zero _
  have hdiscR :
      (NumberField.discr (rationalQuadraticAlgebra (-a)) : ℝ) ≠ 0 := by
    exact_mod_cast hdiscZ
  have hDelta : 0 < Delta := by
    dsimp only [Delta]
    exact Real.sqrt_pos.2 (abs_pos.mpr hdiscR)
  have hMmeshPos : 0 < Mmesh := lt_of_lt_of_le (by norm_num) hMmesh
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  have hshort := hspec.shortest_original_vector
  dsimp only at hshort
  change y ≠ 0 ∧ IsCoprime (y 0) (y 1) ∧
    max |2 * cert.ell y / E|
      |2 * (main3IntegralTargetWedge cert.anchor y : ℝ) / K| = mu at hshort
  have hminimum := hshort.2.2
  have hmu : 0 ≤ mu := by
    rw [← hminimum]
    exact (abs_nonneg _).trans (le_max_left _ _)
  have hradialNormalized : |2 * cert.ell y / E| ≤ mu := by
    rw [← hminimum]
    exact le_max_left _ _
  have hwedgeNormalized :
      |2 * (main3IntegralTargetWedge cert.anchor y : ℝ) / K| ≤ mu := by
    rw [← hminimum]
    exact le_max_right _ _
  have hradial : |cert.ell y| ≤ E * mu / 2 := by
    rw [abs_div, abs_mul, abs_of_pos hE,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hradialNormalized
    have hscaled := (div_le_iff₀ hE).mp hradialNormalized
    nlinarith
  have hwedge : |(main3IntegralTargetWedge cert.anchor y : ℝ)| ≤
      K * mu / 2 := by
    rw [abs_div, abs_mul, abs_of_pos hK,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hwedgeNormalized
    have hscaled := (div_le_iff₀ hK).mp hwedgeNormalized
    nlinarith
  let anchorValue := main3IntegralTargetLinearForm
    (sigma F.omega) cert.anchor
  let yValue := main3IntegralTargetLinearForm (sigma F.omega) y
  have hcrossEq :
      ‖conj anchorValue * yValue - conj yValue * anchorValue‖ =
        |(main3IntegralTargetWedge cert.anchor y : ℝ)| * Delta := by
    have hwedgeNorm :=
      norm_main3IntegralTargetLinearForm_wedge_eq F sigma cert.anchor y
    simpa only [sigma, Delta, anchorValue, yValue,
      main3IntegralTargetLinearForm_imaginaryPlace_star_eq_conj] using
        hwedgeNorm
  have hcross :
      ‖conj anchorValue * yValue - conj yValue * anchorValue‖ ≤
        E * mu / 2 := by
    rw [hcrossEq]
    calc
      |(main3IntegralTargetWedge cert.anchor y : ℝ)| * Delta ≤
          (K * mu / 2) * Delta :=
        mul_le_mul_of_nonneg_right hwedge hDelta.le
      _ = 3 * E * mu / Mmesh := by
        dsimp only [K]
        field_simp [hDelta.ne', hMmeshPos.ne']
        ring
      _ ≤ E * mu / 2 := by
        apply (div_le_iff₀ hMmeshPos).2
        have hEmu : 0 ≤ E * mu := mul_nonneg hE.le hmu
        have hscaled := mul_le_mul_of_nonneg_right hMmesh hEmu
        nlinarith
  have hellY : cert.ell y = (conj anchorValue * yValue).re := by
    have hfun := congrArg (fun f : (Fin 2 → ℤ) →+ ℝ ↦ f y) hell
    simpa only [main3AnchorHermitianRadialAddHom_apply, one_mul,
      sigma, anchorValue, yValue] using hfun
  have hellAnchor : cert.ell cert.anchor = ‖anchorValue‖ ^ 2 := by
    calc
      cert.ell cert.anchor =
          main3AnchorHermitianRadialAddHom 1
            (sigma F.omega) cert.anchor cert.anchor := by rw [hell]
      _ = 1 * ‖main3IntegralTargetLinearForm
          (sigma F.omega) cert.anchor‖ ^ 2 :=
        main3AnchorHermitianRadialAddHom_self 1
          (sigma F.omega) cert.anchor
      _ = ‖anchorValue‖ ^ 2 := by simp only [one_mul, anchorValue]
  have hanchor : E ≤ 2 * ‖anchorValue‖ ^ 2 := by
    rw [← hellAnchor]
    exact hrhoLower
  have hre : |(conj anchorValue * yValue).re| ≤ E * mu / 2 := by
    rw [← hellY]
    exact hradial
  have hdirect : ‖yValue‖ ^ 2 ≤ (5 / 8 : ℝ) * E * mu ^ 2 :=
    complex_second_norm_sq_le_of_re_cross
      anchorValue yValue E mu hE hmu hanchor hre hcross
  have hthreshold : ∀ S : ℝ, 0 ≤ S → S ≤ 1 / mu →
      S ^ 2 * ‖main3IntegralTargetLinearForm (sigma F.omega) y‖ ^ 2 ≤
        (5 / 8 : ℝ) * E := by
    intro S hS hSinv
    have hSmu : S * mu ≤ 1 := by
      by_cases hmuZero : mu = 0
      · rw [hmuZero, mul_zero]
        norm_num
      · have hmuPos : 0 < mu := lt_of_le_of_ne hmu (Ne.symm hmuZero)
        exact (le_div_iff₀ hmuPos).mp hSinv
    have hSmuSq : S ^ 2 * mu ^ 2 ≤ 1 := by
      rw [← mul_pow]
      have hprod0 : 0 ≤ S * mu := mul_nonneg hS hmu
      nlinarith
    calc
      S ^ 2 * ‖main3IntegralTargetLinearForm (sigma F.omega) y‖ ^ 2 ≤
          S ^ 2 * ((5 / 8 : ℝ) * E * mu ^ 2) := by gcongr
      _ = ((5 / 8 : ℝ) * E) * (S ^ 2 * mu ^ 2) := by ring
      _ ≤ ((5 / 8 : ℝ) * E) * 1 :=
        mul_le_mul_of_nonneg_left hSmuSq (by positivity)
      _ = (5 / 8 : ℝ) * E := by ring
  refine ⟨by simpa only [yValue] using hdirect, hthreshold, ?_⟩
  · intro S hS hSinv
    have hweighted :
        S ^ 2 * ‖main3IntegralTargetLinearForm (sigma F.omega) y‖ ^ 2 ≤
          (5 / 8 : ℝ) * E := hthreshold S hS.le hSinv
    exact (le_div_iff₀ (sq_pos_of_pos hS)).2 (by
      simpa only [mul_comm] using hweighted)

/-- Compact downstream proposition for the direct and threshold forms of the
complex-cover short-vector estimate. -/
def Main3LargeAnalyticComplexCoverShortestVectorBoundSpec
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (F : ShiftedSquareFixedExplicitIntegralBasisData a)
    (ha : 0 < a) {T : Finset (Fin 2 → ℤ)} (E K : ℝ)
    (cert : PrimitiveWedgeReducedTargetCoverCertificate T E K 2)
    (G H : SL(2, ℤ)) : Prop :=
  let rho := cert.ell cert.anchor
  let U := K / 2
  let V := 1 + (2 : ℝ) / 2
  let M₀ := 2 * rho * V / E
  let beta := cert.ell (fun i ↦ G i 1)
  let z := -K * beta / E
  let mu := firstSlopeSupNorm U V M₀ z
  let y := primitiveWedgeReducedTargetCoverShortestVector G H
  ‖main3IntegralTargetLinearForm
      (shiftedSquareImaginaryPlaceEmbedding a ha F.omega) y‖ ^ 2 ≤
      (5 / 8 : ℝ) * E * mu ^ 2 ∧
    (∀ S : ℝ, 0 ≤ S → S ≤ 1 / mu →
      S ^ 2 * ‖main3IntegralTargetLinearForm
        (shiftedSquareImaginaryPlaceEmbedding a ha F.omega) y‖ ^ 2 ≤
          (5 / 8 : ℝ) * E) ∧
    (∀ S : ℝ, 0 < S → S ≤ 1 / mu →
      ‖main3IntegralTargetLinearForm
        (shiftedSquareImaginaryPlaceEmbedding a ha F.omega) y‖ ^ 2 ≤
          ((5 / 8 : ℝ) * E) / S ^ 2)

/-- A nonempty complex fixed cell supplies one radial certificate and one
pair of reduced-cover witnesses for which the original-coordinate first
column satisfies the sharp Hermitian norm bound.  The certificate, `G`, and
`H` in the bound are literally those in the returned cover specification. -/
theorem exists_main3LargeAnalyticFixedKeyComplexCellTargetCoverShortestVectorBound
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
    ∃ cert : PrimitiveWedgeReducedTargetCoverCertificate T E K 2,
      cert.ell = main3AnchorHermitianRadialAddHom
        1 (sigma F.omega) cert.anchor ∧
      E ≤ 2 * cert.ell cert.anchor ∧
      cert.ell cert.anchor ≤ E ∧
      ∃ G H : SL(2, ℤ),
        PrimitiveWedgeReducedTargetCoverSpec
          T cert.ell cert.anchor E K 2 G H ∧
        Main3LargeAnalyticComplexCoverShortestVectorBoundSpec
          F ha E K cert G H := by
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
  obtain ⟨cert, hell, hrhoLower, hrhoUpper, _hcalibration⟩ :=
    exists_main3LargeAnalyticFixedKeyComplexCellTargetRadialCoverCertificate
      htheta hY hi key cell ha hnonempty
  obtain ⟨G, H, hspec⟩ := cert.exists_reducedTargetCover
  have hE : 0 < E := by
    simpa only [E] using cert.R_pos
  have hMmesh : 6 ≤ Mmesh := by
    dsimp only [Mmesh]
    exact_mod_cast six_le_main3UnbalancedM htheta hY
  have hbound :=
    PrimitiveWedgeReducedTargetCoverSpec.complex_shortest_original_vector_norm_sq_bounds
      F ha hE hMmesh cert hell hrhoLower hspec
  refine ⟨cert, ?_, ?_, ?_, G, H, ?_, ?_⟩
  · simpa only [F, sigma] using hell
  · simpa only [E] using hrhoLower
  · simpa only [E] using hrhoUpper
  · simpa only [T, E, K] using hspec
  · unfold Main3LargeAnalyticComplexCoverShortestVectorBoundSpec
    simpa only [F, sigma, E, K, Mmesh, Delta] using hbound

end

end PellPaper
