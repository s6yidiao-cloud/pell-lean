import Pell.ComplexIntegralLatticeBallGrowth
import Pell.Main3LargeAnalyticComplexRadialDiscriminantCost
import Mathlib.Tactic

/-!
This module specializes complex lattice-ball growth to the fixed integral
basis and explicit imaginary place.  Integrality supplies the global unit
lower bound for nonzero lattice vectors, while the conjugate-difference
identity identifies twice the imaginary basis spacing with the square root
of the absolute field discriminant.
-/

namespace PellPaper

open scoped ComplexConjugate

noncomputable section

local instance shiftedSquareComplexIntegralLatticeBallGrowth_numberField
    (a : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

/-- The fixed-basis coordinate linear form is literally evaluation of the
corresponding ring-of-integers element at the imaginary place. -/
theorem main3IntegralTargetLinearForm_fixedBasis_imaginaryPlace_eq
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (ha : 0 < a) (F : ShiftedSquareFixedExplicitIntegralBasisData a)
    (y : Fin 2 → ℤ) :
    main3IntegralTargetLinearForm
        (shiftedSquareImaginaryPlaceEmbedding a ha F.omega) y =
      shiftedSquareImaginaryPlaceEmbedding a ha
        (shiftedSquareIntegralBasisElement F.basis y :
          rationalQuadraticAlgebra (-a)) := by
  have hcoord := congrArg Subtype.val
    (shiftedSquareIntegralBasisElement_eq_explicit
      F.basis F.omega F.basis_zero F.basis_one y)
  let sigma := shiftedSquareImaginaryPlaceEmbedding a ha
  calc
    main3IntegralTargetLinearForm (sigma F.omega) y =
        sigma ((y 0 : rationalQuadraticAlgebra (-a)) +
          (y 1 : rationalQuadraticAlgebra (-a)) * F.omega) := by
      simp only [main3IntegralTargetLinearForm, map_add, map_mul, map_intCast]
      ring
    _ = sigma (shiftedSquareIntegralBasisElement F.basis y :
          rationalQuadraticAlgebra (-a)) :=
      congrArg sigma hcoord.symm

/-- The complex norm square of a fixed-basis coordinate vector is its
integral quadratic norm form. -/
theorem norm_sq_main3IntegralTargetLinearForm_fixedBasis_imaginaryPlace_eq
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (ha : 0 < a) (F : ShiftedSquareFixedExplicitIntegralBasisData a)
    (y : Fin 2 → ℤ) :
    ‖main3IntegralTargetLinearForm
        (shiftedSquareImaginaryPlaceEmbedding a ha F.omega) y‖ ^ 2 =
      (shiftedSquareExplicitNormFormEval F.t F.c y : ℝ) := by
  let z : rationalQuadraticAlgebra (-a) :=
    shiftedSquareIntegralBasisElement F.basis y
  let sigma := shiftedSquareImaginaryPlaceEmbedding a ha
  have hmul : z * star z =
      (shiftedSquareExplicitNormFormEval F.t F.c y :
        rationalQuadraticAlgebra (-a)) := by
    simpa only [z] using
      shiftedSquare_integralBasisElement_mul_star_eq_explicitNormForm
        F.basis F.omega F.t F.c F.basis_zero F.basis_one F.omega_sq y
  have hcomplex :
      ((‖sigma z‖ ^ 2 : ℝ) : ℂ) =
        ((shiftedSquareExplicitNormFormEval F.t F.c y : ℤ) : ℂ) := by
    calc
      ((‖sigma z‖ ^ 2 : ℝ) : ℂ) =
          sigma z * (starRingEnd ℂ) (sigma z) := by
        push_cast
        exact (Complex.mul_conj' (sigma z)).symm
      _ = sigma z * sigma (star z) := by
        congr 1
        exact (shiftedSquareImaginaryPlaceEmbedding_star a ha z).symm
      _ = sigma (z * star z) := by rw [map_mul]
      _ = ((shiftedSquareExplicitNormFormEval F.t F.c y : ℤ) : ℂ) := by
        rw [hmul, map_intCast]
  rw [main3IntegralTargetLinearForm_fixedBasis_imaginaryPlace_eq ha F y]
  exact_mod_cast hcomplex

/-- Every nonzero integral coordinate vector has imaginary-place norm at
least one. -/
theorem one_le_norm_main3IntegralTargetLinearForm_fixedBasis_imaginaryPlace
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (ha : 0 < a) (F : ShiftedSquareFixedExplicitIntegralBasisData a)
    (y : Fin 2 → ℤ) (hy : y ≠ 0) :
    1 ≤ ‖main3IntegralTargetLinearForm
      (shiftedSquareImaginaryPlaceEmbedding a ha F.omega) y‖ := by
  let q := shiftedSquareExplicitNormFormEval F.t F.c y
  have helem : shiftedSquareIntegralBasisElement F.basis y ≠ 0 := by
    intro helemZero
    apply hy
    apply F.basis.equivFun.symm.injective
    simpa only [shiftedSquareIntegralBasisElement,
      map_zero] using helemZero
  have hlinear : main3IntegralTargetLinearForm
        (shiftedSquareImaginaryPlaceEmbedding a ha F.omega) y ≠ 0 := by
    rw [main3IntegralTargetLinearForm_fixedBasis_imaginaryPlace_eq ha F y]
    have helemField :
        (shiftedSquareIntegralBasisElement F.basis y :
          rationalQuadraticAlgebra (-a)) ≠ 0 := by
      intro hzero
      apply helem
      exact Subtype.ext hzero
    simpa only [map_zero] using
      (shiftedSquareImaginaryPlaceEmbedding a ha).injective.ne helemField
  have hsq :=
    norm_sq_main3IntegralTargetLinearForm_fixedBasis_imaginaryPlace_eq
      ha F y
  have hqNonnegR : (0 : ℝ) ≤ (q : ℝ) := by
    rw [← hsq]
    positivity
  have hqNonneg : (0 : ℤ) ≤ q := by exact_mod_cast hqNonnegR
  have hqNe : q ≠ 0 := by
    intro hqZero
    have hnormSq :
        ‖main3IntegralTargetLinearForm
          (shiftedSquareImaginaryPlaceEmbedding a ha F.omega) y‖ ^ 2 = 0 := by
      rw [hsq]
      simp [q, hqZero]
    have hnorm :
        ‖main3IntegralTargetLinearForm
          (shiftedSquareImaginaryPlaceEmbedding a ha F.omega) y‖ = 0 := by
      nlinarith [norm_nonneg (main3IntegralTargetLinearForm
        (shiftedSquareImaginaryPlaceEmbedding a ha F.omega) y)]
    exact hlinear (norm_eq_zero.mp hnorm)
  have hqOne : (1 : ℤ) ≤ q := by omega
  have hsqOne : (1 : ℝ) ≤
      ‖main3IntegralTargetLinearForm
        (shiftedSquareImaginaryPlaceEmbedding a ha F.omega) y‖ ^ 2 := by
    rw [hsq]
    exact_mod_cast hqOne
  nlinarith [norm_nonneg (main3IntegralTargetLinearForm
    (shiftedSquareImaginaryPlaceEmbedding a ha F.omega) y)]

/-- The imaginary coordinate of the embedded fixed-basis generator is half
the square root of the absolute field discriminant. -/
theorem two_mul_abs_im_shiftedSquareFixedBasis_imaginaryPlace_omega
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (ha : 0 < a) (F : ShiftedSquareFixedExplicitIntegralBasisData a) :
    2 * |(shiftedSquareImaginaryPlaceEmbedding a ha
      (F.omega : rationalQuadraticAlgebra (-a))).im| =
      Real.sqrt
        |(NumberField.discr (rationalQuadraticAlgebra (-a)) : ℝ)| := by
  let sigma := shiftedSquareImaginaryPlaceEmbedding a ha
  let omega := sigma (F.omega : rationalQuadraticAlgebra (-a))
  have hdiffSq := shiftedSquareFixedBasis_embeddingDifference_norm_sq F sigma
  have hdiff : ‖omega - conj omega‖ =
      Real.sqrt
        |(NumberField.discr (rationalQuadraticAlgebra (-a)) : ℝ)| := by
    calc
      ‖omega - conj omega‖ =
          ‖sigma ((F.omega : rationalQuadraticAlgebra (-a)) -
            star (F.omega : rationalQuadraticAlgebra (-a)))‖ := by
        simp only [omega, sigma, map_sub,
          shiftedSquareImaginaryPlaceEmbedding_star, starRingEnd_apply]
      _ = Real.sqrt
          (‖sigma ((F.omega : rationalQuadraticAlgebra (-a)) -
            star (F.omega : rationalQuadraticAlgebra (-a)))‖ ^ 2) := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
      _ = Real.sqrt
          |(NumberField.discr (rationalQuadraticAlgebra (-a)) : ℝ)| := by
        rw [hdiffSq]
  have hnormSq :
      Complex.normSq (omega - conj omega) =
        (2 * |omega.im|) ^ 2 := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.conj_re,
      sub_self, Complex.sub_im, Complex.conj_im, sub_neg_eq_add,
      OfNat.ofNat]
    calc
      0 * 0 + (omega.im + omega.im) * (omega.im + omega.im) =
          4 * omega.im ^ 2 := by ring
      _ = 4 * |omega.im| ^ 2 := by rw [sq_abs]
      _ = (2 * |omega.im|) ^ 2 := by ring
  have hnorm : ‖omega - conj omega‖ = 2 * |omega.im| := by
    rw [Complex.norm_def, hnormSq, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (mul_nonneg (by norm_num) (abs_nonneg _))]
  exact hnorm.symm.trans hdiff

/-- Fixed-basis specialization of complex ball growth with the field
discriminant displayed in the manuscript normalization. -/
theorem card_shiftedSquareFixedBasis_imaginaryPlace_norm_le_linear_add_area
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (ha : 0 < a) (F : ShiftedSquareFixedExplicitIntegralBasisData a)
    (T : Finset (Fin 2 → ℤ)) (H : ℝ) (hH : 1 ≤ H)
    (hnonzero : ∀ y ∈ T, y ≠ 0)
    (hball : ∀ y ∈ T,
      ‖main3IntegralTargetLinearForm
        (shiftedSquareImaginaryPlaceEmbedding a ha F.omega) y‖ ≤ H) :
    (T.card : ℝ) ≤ 12 * H + 72 * H ^ 2 /
      Real.sqrt
        |(NumberField.discr (rationalQuadraticAlgebra (-a)) : ℝ)| := by
  let omega := shiftedSquareImaginaryPlaceEmbedding a ha
    (F.omega : rationalQuadraticAlgebra (-a))
  let Delta := Real.sqrt
    |(NumberField.discr (rationalQuadraticAlgebra (-a)) : ℝ)|
  have hDelta : 2 * |omega.im| = Delta := by
    simpa only [omega, Delta] using
      two_mul_abs_im_shiftedSquareFixedBasis_imaginaryPlace_omega ha F
  have him : omega.im ≠ 0 := by
    intro himZero
    have hDeltaZero : Delta = 0 := by simp [hDelta.symm, himZero]
    have hdisc :
        (NumberField.discr (rationalQuadraticAlgebra (-a)) : ℝ) ≠ 0 := by
      exact_mod_cast NumberField.discr_ne_zero (rationalQuadraticAlgebra (-a))
    have hDeltaPos : 0 < Delta := by
      dsimp only [Delta]
      exact Real.sqrt_pos.2 (abs_pos.mpr hdisc)
    linarith
  have hcount := card_complexIntegralLinearForm_norm_le_linear_add_area
    T omega H him hH
      (fun y hy ↦ by
        simpa only [omega] using
          one_le_norm_main3IntegralTargetLinearForm_fixedBasis_imaginaryPlace
            ha F y hy)
      hnonzero
      (fun y hy ↦ by simpa only [omega] using hball y hy)
  calc
    (T.card : ℝ) ≤ 12 * H + 36 * H ^ 2 / |omega.im| := hcount
    _ = 12 * H + 72 * H ^ 2 / Delta := by
      rw [← hDelta]
      field_simp [abs_ne_zero.mpr him]
      ring

end

end PellPaper
