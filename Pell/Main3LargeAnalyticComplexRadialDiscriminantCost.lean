import Pell.Main3ComplexEmbeddingMinorVanishing
import Pell.Main3ShiftedSquareEmbeddingRatioCoordinateAdapter
import Pell.Main3LargeAnalyticCellCoordinatePointImage
import Pell.Main3ShiftedSquareRawCoordinateBounds
import Mathlib.Tactic

/-!
# Sharp complex radial/discriminant cost on a main3 block cell

At the explicit imaginary place, multiplication by quadratic conjugation is
complex multiplication by conjugation.  For the primitive source and target
elements of a shifted-square package this identifies their norm squares with
the exact scales `E_alpha` and `E_gamma`, with no use of the coarse all-place
`512 * |a|` loss.

The final result applies these pointwise identities to the literal finite
coordinate image of one fixed auxiliary-key and complex-cell fibre.  It
bounds the selected product of radial row factors, divided by the exact
embedding-basis discriminant factor.  No local Taylor estimate, determinant
vanishing statement, fibre count, or asymptotic estimate is asserted here.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

local instance main3LargeAnalyticComplexRadialDiscriminantCost_numberField
    (a : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

/-! ## Exact imaginary-place norm scales -/

/-- A displayed integral-basis element times its quadratic conjugate is the
scalar represented by the explicit binary norm form. -/
theorem shiftedSquare_integralBasisElement_mul_star_eq_explicitNormForm
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (b : Module.Basis (Fin 2) ℤ
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))))
    (omega : NumberField.RingOfIntegers
      (rationalQuadraticAlgebra (-a))) (t c : ℤ)
    (hb0 : b 0 = 1) (hb1 : b 1 = omega)
    (homega : omega ^ 2 =
      (t : NumberField.RingOfIntegers
        (rationalQuadraticAlgebra (-a))) * omega + c)
    (u : Fin 2 → ℤ) :
    (shiftedSquareIntegralBasisElement b u :
        rationalQuadraticAlgebra (-a)) *
        star (shiftedSquareIntegralBasisElement b u :
          rationalQuadraticAlgebra (-a)) =
      (shiftedSquareExplicitNormFormEval t c u :
        rationalQuadraticAlgebra (-a)) := by
  have hz :
      (shiftedSquareIntegralBasisElement b u :
          rationalQuadraticAlgebra (-a)) =
        (u 0 : rationalQuadraticAlgebra (-a)) +
          (u 1 : rationalQuadraticAlgebra (-a)) * omega := by
    exact congrArg Subtype.val
      (shiftedSquareIntegralBasisElement_eq_explicit b omega hb0 hb1 u)
  have hadd := shiftedSquare_displayedOmega_add_star_eq
    b omega t c hb0 hb1 homega
  have hstar : star (omega : rationalQuadraticAlgebra (-a)) =
      (t : rationalQuadraticAlgebra (-a)) - omega := by
    linear_combination hadd
  have homegaField :
      (omega : rationalQuadraticAlgebra (-a)) ^ 2 =
        (t : rationalQuadraticAlgebra (-a)) * omega + c := by
    exact congrArg Subtype.val homega
  rw [hz, star_add, star_mul, star_intCast, hstar]
  simp only [star_intCast]
  simp only [shiftedSquareExplicitNormFormEval]
  push_cast
  linear_combination
    -(u 1 : rationalQuadraticAlgebra (-a)) ^ 2 * homegaField

/-- At the explicit imaginary place, the norm square of a displayed basis
element is exactly its signed explicit norm form; in particular the latter
is automatically nonnegative. -/
theorem shiftedSquare_imaginaryPlace_integralBasisElement_norm_sq_eq_explicit
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (ha : 0 < a)
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq)
    (u : Fin 2 → ℤ) :
    ‖shiftedSquareImaginaryPlaceEmbedding a ha
        (shiftedSquareIntegralBasisElement P.basis u :
          rationalQuadraticAlgebra (-a))‖ ^ 2 =
      (shiftedSquareExplicitNormFormEval P.t P.c u : ℝ) := by
  let z : rationalQuadraticAlgebra (-a) :=
    shiftedSquareIntegralBasisElement P.basis u
  let sigma := shiftedSquareImaginaryPlaceEmbedding a ha
  have hmul : z * star z =
      (shiftedSquareExplicitNormFormEval P.t P.c u :
        rationalQuadraticAlgebra (-a)) := by
    simpa only [z] using
      shiftedSquare_integralBasisElement_mul_star_eq_explicitNormForm
        P.basis P.omega P.t P.c P.basis_zero P.basis_one P.omega_sq u
  have hcomplex :
      ((‖sigma z‖ ^ 2 : ℝ) : ℂ) =
        ((shiftedSquareExplicitNormFormEval P.t P.c u : ℤ) : ℂ) := by
    calc
      ((‖sigma z‖ ^ 2 : ℝ) : ℂ) =
          sigma z * (starRingEnd ℂ) (sigma z) := by
        push_cast
        exact (Complex.mul_conj' (sigma z)).symm
      _ = sigma z * sigma (star z) := by
        congr 1
        exact (shiftedSquareImaginaryPlaceEmbedding_star a ha z).symm
      _ = sigma (z * star z) := by rw [map_mul]
      _ = ((shiftedSquareExplicitNormFormEval P.t P.c u : ℤ) : ℂ) := by
        rw [hmul, map_intCast]
  exact_mod_cast hcomplex

/-- The primitive source element has imaginary-place norm square exactly
`E_alpha`. -/
theorem shiftedSquare_imaginaryPlace_sourcePrimitive_norm_sq_eq_EAlpha
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (ha : 0 < a)
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq) :
    ‖shiftedSquareImaginaryPlaceEmbedding a ha
        (shiftedSquareIntegralBasisElement P.basis P.x :
          rationalQuadraticAlgebra (-a))‖ ^ 2 =
      shiftedSquareEAlpha P := by
  have hnorm :=
    shiftedSquare_imaginaryPlace_integralBasisElement_norm_sq_eq_explicit
      ha P P.x
  have hformNonneg :
      0 ≤ (shiftedSquareExplicitNormFormEval P.t P.c P.x : ℝ) := by
    rw [← hnorm]
    positivity
  have hr0 : (P.r : ℝ) ≠ 0 := by exact_mod_cast P.r_pos.ne'
  have hform :
      (P.r : ℝ) ^ 2 *
          (shiftedSquareExplicitNormFormEval P.t P.c P.x : ℝ) =
        ((shiftedSquareD₀ d * P.minkowski.C₀ : ℕ) : ℝ) := by
    have h := congrArg (fun z : ℤ ↦ (z : ℝ)) P.mu_norm_form
    simpa only [Int.cast_mul, Int.cast_pow, Int.cast_natCast,
      Int.cast_abs, abs_of_nonneg hformNonneg] using h
  rw [hnorm, shiftedSquareEAlpha]
  apply (eq_div_iff (pow_ne_zero 2 hr0)).2
  simpa only [mul_comm] using hform

/-- The primitive target element has imaginary-place norm square exactly
`E_gamma`. -/
theorem shiftedSquare_imaginaryPlace_targetPrimitive_norm_sq_eq_EGamma
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (ha : 0 < a)
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq) :
    ‖shiftedSquareImaginaryPlaceEmbedding a ha
        (shiftedSquareIntegralBasisElement P.basis P.y :
          rationalQuadraticAlgebra (-a))‖ ^ 2 =
      shiftedSquareEGamma P := by
  have hnorm :=
    shiftedSquare_imaginaryPlace_integralBasisElement_norm_sq_eq_explicit
      ha P P.y
  have hell0 : (P.ell : ℝ) ≠ 0 := by exact_mod_cast P.ell_pos.ne'
  have hform :
      (P.ell : ℝ) ^ 2 *
          (shiftedSquareExplicitNormFormEval P.t P.c P.y : ℝ) =
        ((w * P.minkowski.C₀ ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast P.nu_norm_form
  rw [hnorm, shiftedSquareEGamma]
  apply (eq_div_iff (pow_ne_zero 2 hell0)).2
  simpa only [mul_comm] using hform

/-- The source norm itself is the nonnegative square root of `E_alpha`. -/
theorem shiftedSquare_imaginaryPlace_sourcePrimitive_norm_eq_sqrt_EAlpha
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (ha : 0 < a)
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq) :
    ‖shiftedSquareImaginaryPlaceEmbedding a ha
        (shiftedSquareIntegralBasisElement P.basis P.x :
          rationalQuadraticAlgebra (-a))‖ =
      Real.sqrt (shiftedSquareEAlpha P) := by
  rw [← shiftedSquare_imaginaryPlace_sourcePrimitive_norm_sq_eq_EAlpha ha P,
    Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

/-- The target norm itself is the nonnegative square root of `E_gamma`. -/
theorem shiftedSquare_imaginaryPlace_targetPrimitive_norm_eq_sqrt_EGamma
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (ha : 0 < a)
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq) :
    ‖shiftedSquareImaginaryPlaceEmbedding a ha
        (shiftedSquareIntegralBasisElement P.basis P.y :
          rationalQuadraticAlgebra (-a))‖ =
      Real.sqrt (shiftedSquareEGamma P) := by
  rw [← shiftedSquare_imaginaryPlace_targetPrimitive_norm_sq_eq_EGamma ha P]
  exact (Real.sqrt_sq (norm_nonneg _)).symm

/-- On a package point, the radial row factor has exactly the square-root
source scale times the `B`-th power of the square-root target scale. -/
theorem main3ShiftedSquarePackagePoint_imaginaryRadialRowFactor_norm_eq
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (ha : 0 < a) (degree : ℕ)
    (F : ShiftedSquareFixedExplicitIntegralBasisData a)
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq)
    (homega : P.omega = F.omega) :
    ‖main3EmbeddingRadialRowFactor degree
        (shiftedSquareImaginaryPlaceEmbedding a ha F.omega)
        (shiftedSquareImaginaryPlaceEmbedding a ha (star F.omega))
        (main3ShiftedSquarePackagePoint P)‖ =
      Real.sqrt (shiftedSquareEAlpha P) *
        Real.sqrt (shiftedSquareEGamma P) ^ degree := by
  let sigma := shiftedSquareImaginaryPlaceEmbedding a ha
  have hsource :=
    main3ShiftedSquarePackagePoint_sourceDenominator_eq F P homega sigma
  have htarget :=
    main3ShiftedSquarePackagePoint_targetDenominator_eq F P homega sigma
  have hsource' :
      ((main3ShiftedSquarePackagePoint P).1.1 : ℂ) +
          sigma (star F.omega) *
            ((main3ShiftedSquarePackagePoint P).1.2 : ℂ) =
        sigma (star (shiftedSquareIntegralBasisElement P.basis P.x :
          rationalQuadraticAlgebra (-a))) := by
    simpa only [main3ShiftedSquareEmbeddingOmegaBar] using hsource
  have htarget' :
      ((main3ShiftedSquarePackagePoint P).2.1 : ℂ) +
          sigma F.omega *
            ((main3ShiftedSquarePackagePoint P).2.2 : ℂ) =
        sigma (shiftedSquareIntegralBasisElement P.basis P.y :
          rationalQuadraticAlgebra (-a)) := by
    simpa only [main3ShiftedSquareEmbeddingOmega] using htarget
  unfold main3EmbeddingRadialRowFactor
  change ‖(((main3ShiftedSquarePackagePoint P).1.1 : ℂ) +
      sigma (star F.omega) * ((main3ShiftedSquarePackagePoint P).1.2 : ℂ)) *
      ((((main3ShiftedSquarePackagePoint P).2.1 : ℂ) +
        sigma F.omega * ((main3ShiftedSquarePackagePoint P).2.2 : ℂ)) ^ degree)‖ = _
  rw [hsource', htarget', norm_mul, norm_pow,
    shiftedSquareImaginaryPlaceEmbedding_star, norm_star,
    shiftedSquare_imaginaryPlace_sourcePrimitive_norm_eq_sqrt_EAlpha ha P,
    shiftedSquare_imaginaryPlace_targetPrimitive_norm_eq_sqrt_EGamma ha P]

/-! ## Fixed-key dyadic upper scales -/

/-- A fixed key and source dyadic scale give this common upper bound for
`E_alpha` throughout the fibre. -/
def main3LargeAnalyticFixedKeySourceScaleUpper
    (D : ℕ) (key : ShiftedSquareAuxiliaryKey) : ℝ :=
  2 * (D : ℝ) * (key.C₀ : ℝ) / (key.r : ℝ) ^ 2

/-- A fixed key and target dyadic scale give this common upper bound for
`E_gamma` throughout the fibre. -/
def main3LargeAnalyticFixedKeyTargetScaleUpper
    (Y : ℕ) (key : ShiftedSquareAuxiliaryKey) : ℝ :=
  2 * (Y : ℝ) * (key.C₀ : ℝ) ^ 2 / (key.ell : ℝ) ^ 2

/-- The upper half of the source dyadic interval bounds `E_alpha` by the
fixed-key source scale. -/
theorem shiftedSquareEAlpha_le_fixedKeySourceScaleUpper
    {a : ℤ} {d w n D : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (hdD : d < 2 * D)
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq) :
    shiftedSquareEAlpha P ≤
      main3LargeAnalyticFixedKeySourceScaleUpper D
        ⟨P.minkowski.C₀, P.r, P.ell, P.bζ⟩ := by
  unfold shiftedSquareEAlpha main3LargeAnalyticFixedKeySourceScaleUpper
  apply div_le_div_of_nonneg_right _ (sq_nonneg (P.r : ℝ))
  have hd₀d : shiftedSquareD₀ d ≤ d := by
    exact Nat.div_le_self d (shiftedSquareQ₂ d)
  have hd₀D : (shiftedSquareD₀ d : ℝ) ≤ 2 * (D : ℝ) := by
    exact_mod_cast (show shiftedSquareD₀ d ≤ 2 * D by omega)
  simpa only [Nat.cast_mul] using
    mul_le_mul_of_nonneg_right hd₀D (Nat.cast_nonneg P.minkowski.C₀)

/-- The upper half of the target dyadic interval bounds `E_gamma` by the
fixed-key target scale. -/
theorem shiftedSquareEGamma_le_fixedKeyTargetScaleUpper
    {a : ℤ} {d w n Y : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (hwY : w < 2 * Y)
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq) :
    shiftedSquareEGamma P ≤
      main3LargeAnalyticFixedKeyTargetScaleUpper Y
        ⟨P.minkowski.C₀, P.r, P.ell, P.bζ⟩ := by
  unfold shiftedSquareEGamma main3LargeAnalyticFixedKeyTargetScaleUpper
  apply div_le_div_of_nonneg_right _ (sq_nonneg (P.ell : ℝ))
  have hwY' : (w : ℝ) ≤ 2 * (Y : ℝ) := by
    exact_mod_cast (show w ≤ 2 * Y by omega)
  simpa only [Nat.cast_mul, Nat.cast_pow] using
    mul_le_mul_of_nonneg_right hwY' (sq_nonneg (P.minkowski.C₀ : ℝ))

/-- Every literal coordinate point in a fixed key and complex-cell image has
the common sharp dyadic radial-row bound. -/
theorem main3LargeAnalytic_complexCellCoordinatePointImage_radialRowFactor_norm_le
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 65536 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    (ha : 0 < shiftedSquareA h v) (degree : ℕ)
    {key : ShiftedSquareAuxiliaryKey}
    {cell : ComplexUnitCircleSlopeCellIndex}
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
    ‖main3EmbeddingRadialRowFactor degree
        (sigma F.omega) (sigma (star F.omega)) z‖ ≤
      Real.sqrt (main3LargeAnalyticFixedKeySourceScaleUpper D key) *
        Real.sqrt (main3LargeAnalyticFixedKeyTargetScaleUpper Y key) ^ degree := by
  dsimp only
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let hY8 : 8 ≤ Y := by omega
  obtain ⟨p, hp, hkey, _hcell, _hgeometry, _hcode, hzPoint⟩ :=
    main3LargeAnalytic_blockCellCoordinatePointImage_sameCertificate
      htheta hY hi hz
  let F := shiftedSquareFixedExplicitIntegralBasisData
    (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
  let C := main3LargeAnalytic_blockFixedBasisEncodingCertificate
    htheta hY8 hi p
  let sigma := shiftedSquareImaginaryPlaceEmbedding
    (shiftedSquareA h v) ha
  have hzPackage : z = main3ShiftedSquarePackagePoint C.P := by
    exact hzPoint.trans (main3ShiftedSquarePackagePoint_eq C.P).symm
  have hrow :=
    main3ShiftedSquarePackagePoint_imaginaryRadialRowFactor_norm_eq
      ha degree F C.P C.omega_eq
  have hsource :=
    shiftedSquareEAlpha_le_fixedKeySourceScaleUpper
      C.scaled.base.source_dyadic.2 C.P
  have htarget :=
    shiftedSquareEGamma_le_fixedKeyTargetScaleUpper
      C.scaled.base.target_dyadic.2 C.P
  rw [hzPackage, hrow, ← hkey]
  gcongr

/-- Squaring over the `2 * (B + 1)` rows turns the square-root row scale
into the exact source exponent `B + 1` and target exponent `B * (B + 1)`. -/
theorem main3ComplexRadialRowScale_pow_card_eq
    (B : ℕ) {EAlphaUpper EGammaUpper : ℝ}
    (hEAlphaUpper : 0 ≤ EAlphaUpper)
    (hEGammaUpper : 0 ≤ EGammaUpper) :
    (Real.sqrt EAlphaUpper * Real.sqrt EGammaUpper ^ B) ^
        (2 * (B + 1)) =
      EAlphaUpper ^ (B + 1) * EGammaUpper ^ (B * (B + 1)) := by
  rw [mul_pow]
  have hsource :
      Real.sqrt EAlphaUpper ^ (2 * (B + 1)) =
        EAlphaUpper ^ (B + 1) := by
    rw [pow_mul, Real.sq_sqrt hEAlphaUpper]
  have htarget :
      (Real.sqrt EGammaUpper ^ B) ^ (2 * (B + 1)) =
        EGammaUpper ^ (B * (B + 1)) := by
    calc
      (Real.sqrt EGammaUpper ^ B) ^ (2 * (B + 1)) =
          Real.sqrt EGammaUpper ^ (B * (2 * (B + 1))) :=
        (pow_mul _ B (2 * (B + 1))).symm
      _ = Real.sqrt EGammaUpper ^ (2 * (B * (B + 1))) := by
        congr 1
        ring
      _ = (Real.sqrt EGammaUpper ^ 2) ^ (B * (B + 1)) :=
        pow_mul _ 2 (B * (B + 1))
      _ = EGammaUpper ^ (B * (B + 1)) := by
        rw [Real.sq_sqrt hEGammaUpper]
  rw [hsource, htarget]

/-! ## Selected products and the discriminant quotient -/

/-- On the literal finite image of one fixed auxiliary key and complex
archimedean cell, every selection of all `2 * (B + 1)` bidegree rows has the
exact common-scale product bound. -/
theorem main3LargeAnalytic_complexCellCoordinatePointImage_selectedRadialProduct_le
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
    (∏ r : generalBidegreeFormIndex 1 B,
        ‖main3EmbeddingRadialRowFactor B
          (sigma F.omega) (sigma (star F.omega)) (s r).1‖) ≤
      main3LargeAnalyticFixedKeySourceScaleUpper D key ^ (B + 1) *
        main3LargeAnalyticFixedKeyTargetScaleUpper Y key ^ (B * (B + 1)) := by
  dsimp only
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let F := shiftedSquareFixedExplicitIntegralBasisData
    (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
  let sigma := shiftedSquareImaginaryPlaceEmbedding
    (shiftedSquareA h v) ha
  let EAlphaUpper := main3LargeAnalyticFixedKeySourceScaleUpper D key
  let EGammaUpper := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
  have hEAlphaUpper : 0 ≤ EAlphaUpper := by
    unfold EAlphaUpper main3LargeAnalyticFixedKeySourceScaleUpper
    positivity
  have hEGammaUpper : 0 ≤ EGammaUpper := by
    unfold EGammaUpper main3LargeAnalyticFixedKeyTargetScaleUpper
    positivity
  have hprod :
      (∏ r : generalBidegreeFormIndex 1 B,
          ‖main3EmbeddingRadialRowFactor B
            (sigma F.omega) (sigma (star F.omega)) (s r).1‖) ≤
        ∏ _r : generalBidegreeFormIndex 1 B,
          (Real.sqrt EAlphaUpper * Real.sqrt EGammaUpper ^ B) := by
    apply Finset.prod_le_prod
    · intro r _hr
      exact norm_nonneg _
    · intro r _hr
      exact main3LargeAnalytic_complexCellCoordinatePointImage_radialRowFactor_norm_le
        htheta hY hi ha B (s r).2
  calc
    (∏ r : generalBidegreeFormIndex 1 B,
        ‖main3EmbeddingRadialRowFactor B
          (sigma F.omega) (sigma (star F.omega)) (s r).1‖) ≤
        ∏ _r : generalBidegreeFormIndex 1 B,
          (Real.sqrt EAlphaUpper * Real.sqrt EGammaUpper ^ B) := hprod
    _ = (Real.sqrt EAlphaUpper * Real.sqrt EGammaUpper ^ B) ^
        (2 * (B + 1)) := by
      rw [Finset.prod_const, Finset.card_univ,
        card_generalBidegreeFormIndex]
    _ = EAlphaUpper ^ (B + 1) *
        EGammaUpper ^ (B * (B + 1)) :=
      main3ComplexRadialRowScale_pow_card_eq
        B hEAlphaUpper hEGammaUpper

/-- The selected radial product divided by the exact embedding-basis
discriminant factor has the corresponding fixed-key bound.  This is the
project-specific `hcost` input expected by the complex minor-vanishing API. -/
theorem
    main3LargeAnalytic_complexCellCoordinatePointImage_selectedRadialDiscriminantCostFactor_le
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
      (main3LargeAnalyticFixedKeySourceScaleUpper D key ^ (B + 1) *
          main3LargeAnalyticFixedKeyTargetScaleUpper Y key ^
            (B * (B + 1))) /
        Real.rpow
          |(NumberField.discr
            (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ)|
          (((((B + 1) ^ 2 : ℕ) : ℝ)) / 2) := by
  dsimp only
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let F := shiftedSquareFixedExplicitIntegralBasisData
    (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
  let sigma := shiftedSquareImaginaryPlaceEmbedding
    (shiftedSquareA h v) ha
  unfold main3ComplexSelectedRadialDiscriminantCostFactor
  apply div_le_div_of_nonneg_right
  · exact
      main3LargeAnalytic_complexCellCoordinatePointImage_selectedRadialProduct_le
        htheta hY hi ha key cell s
  · exact (main3ShiftedSquare_discriminantRpowFactor_pos B).le

end

end PellPaper
