import Pell.Main3LargeAnalyticRealCoverShortestVectorBound
import Pell.SlopeLatticeBallGrowth
import Mathlib.Tactic

/-!
# Two-real-place integral lattice ball growth

The determinant-one rescaling by `c` does not change the covolume of the
two real embedding rows.  After triangularizing those rows, the resulting
integer lattice is one of the normalized slope lattices.  The integral norm
product gives a global unit lower bound for its actual first minimum.
-/

namespace PellPaper

open scoped ComplexConjugate

noncomputable section

local instance main3LargeAnalyticRealTwoPlaceLatticeBallGrowth_numberField
    (a : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

/-- At a real-valued basis parameter, the complex norm of the target linear
form is just the absolute value of its real coordinate. -/
private theorem norm_main3IntegralTargetLinearForm_eq_abs_realCoordinate
    (omega : ℂ) (homegaIm : omega.im = 0) (y : Fin 2 → ℤ) :
    ‖main3IntegralTargetLinearForm omega y‖ =
      |(y 0 : ℝ) + omega.re * (y 1 : ℝ)| := by
  rw [← Complex.abs_re_eq_norm.mpr]
  · simp [main3IntegralTargetLinearForm]
  · simp [main3IntegralTargetLinearForm, homegaIm]

/-- A unit lower bound for the product of the two unscaled embedding norms
gives the same unit lower bound for every determinant-one rescaling. -/
theorem one_le_main3RealScaledTwoPlaceTargetSupNorm_of_one_le_norm_product
    (c : ℝ) (omega omegaBar : ℂ) (y : Fin 2 → ℤ) (hc : c ≠ 0)
    (hproduct : 1 ≤ ‖main3IntegralTargetLinearForm omega y‖ *
      ‖main3IntegralTargetLinearForm omegaBar y‖) :
    1 ≤ main3RealScaledTwoPlaceTargetSupNorm c omega omegaBar y := by
  let C := |c|
  let A := C * ‖main3IntegralTargetLinearForm omega y‖
  let B := ‖main3IntegralTargetLinearForm omegaBar y‖ / C
  have hC : 0 < C := by dsimp only [C]; exact abs_pos.mpr hc
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hAB : A * B =
      ‖main3IntegralTargetLinearForm omega y‖ *
        ‖main3IntegralTargetLinearForm omegaBar y‖ := by
    dsimp only [A, B]
    field_simp [hC.ne']
  have hprodOne : 1 ≤ A * B := by rw [hAB]; exact hproduct
  have hAle : A ≤ max A B := le_max_left _ _
  have hBle : B ≤ max A B := le_max_right _ _
  have hmaxNonneg : 0 ≤ max A B := hA.trans hAle
  have hsquare : A * B ≤ (max A B) ^ 2 := by
    nlinarith [mul_le_mul hAle hBle hB hmaxNonneg]
  change 1 ≤ max A B
  nlinarith

/-- In the chart `1 ≤ |c|`, the triangularized two-place norm is a slope
lattice norm of determinant `4 * |omegaBar.re - omega.re|`. -/
theorem card_main3RealScaledTwoPlaceTargetSupNorm_le_linear_add_area_of_one_le_abs
    (T : Finset (Fin 2 → ℤ)) (c : ℝ) (omega omegaBar : ℂ) (H : ℝ)
    (hc : c ≠ 0) (hcOne : 1 ≤ |c|)
    (homegaIm : omega.im = 0) (homegaBarIm : omegaBar.im = 0)
    (hspacing : omegaBar.re ≠ omega.re) (hH : 1 ≤ H)
    (hproduct : ∀ y : Fin 2 → ℤ, y ≠ 0 →
      1 ≤ ‖main3IntegralTargetLinearForm omega y‖ *
        ‖main3IntegralTargetLinearForm omegaBar y‖)
    (hnonzero : ∀ y ∈ T, y ≠ 0)
    (hball : ∀ y ∈ T,
      main3RealScaledTwoPlaceTargetSupNorm c omega omegaBar y ≤ H) :
    (T.card : ℝ) ≤ 24 * H + 144 * H ^ 2 / |omegaBar.re - omega.re| := by
  classical
  let C := |c|
  let d := |omegaBar.re - omega.re|
  let U := C / (2 * d)
  let V : ℝ := 1
  let M := 2 * C
  let z := -(C ^ 2 * omega.re / d)
  have hC : 0 < C := by dsimp only [C]; exact abs_pos.mpr hc
  have hd : 0 < d := by dsimp only [d]; exact abs_pos.mpr (sub_ne_zero.mpr hspacing)
  have hU : 0 < U := by dsimp only [U]; positivity
  have hV : 0 < V := by dsimp only [V]; norm_num
  have hM : 0 < M := by dsimp only [M]; positivity
  have hRadius : (1 : ℝ) ≤ 4 * H := by nlinarith
  have hslopeFirst (y : Fin 2 → ℤ) :
      M * (y 0 : ℝ) / V - z * (y 1 : ℝ) / U =
        2 * C * ((y 0 : ℝ) + omega.re * (y 1 : ℝ)) := by
    dsimp only [M, V, z, U]
    field_simp [hC.ne', hd.ne']
    ring
  have hslopeSecond (y : Fin 2 → ℤ) :
      |(y 1 : ℝ) / U| =
        2 * d * |(y 1 : ℝ)| / C := by
    dsimp only [U]
    rw [abs_div, abs_of_pos (div_pos hC (mul_pos (by norm_num) hd))]
    field_simp [hC.ne', hd.ne']
  have hnormOne : ∀ y : Fin 2 → ℤ, y ≠ 0 →
      1 ≤ main3RealScaledTwoPlaceTargetSupNorm c omega omegaBar y := by
    intro y hy
    exact one_le_main3RealScaledTwoPlaceTargetSupNorm_of_one_le_norm_product
      c omega omegaBar y hc (hproduct y hy)
  have hnorm_le_slope (y : Fin 2 → ℤ) :
      main3RealScaledTwoPlaceTargetSupNorm c omega omegaBar y ≤
        slopeVectorSupNorm U V M z (y 0, y 1) := by
    let l₁ := (y 0 : ℝ) + omega.re * (y 1 : ℝ)
    let l₂ := (y 0 : ℝ) + omegaBar.re * (y 1 : ℝ)
    let R := slopeVectorSupNorm U V M z (y 0, y 1)
    have hR : 0 ≤ R := slopeVectorSupNorm_nonneg U V M z (y 0, y 1)
    have hfirstRaw :
        |M * (y 0 : ℝ) / V - z * (y 1 : ℝ) / U| ≤ R := by
      exact le_max_left _ _
    have hsecondRaw : |(y 1 : ℝ) / U| ≤ R := le_max_right _ _
    have hfirst : C * |l₁| ≤ R / 2 := by
      rw [hslopeFirst] at hfirstRaw
      rw [abs_mul, abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_pos hC] at hfirstRaw
      dsimp only [l₁]
      linarith
    have hdiff : d * |(y 1 : ℝ)| / C ≤ R / 2 := by
      rw [hslopeSecond] at hsecondRaw
      calc
        d * |(y 1 : ℝ)| / C =
            (2 * d * |(y 1 : ℝ)| / C) / 2 := by ring
        _ ≤ R / 2 := div_le_div_of_nonneg_right hsecondRaw (by norm_num)
    have hl₁Over : |l₁| / C ≤ R / 2 := by
      have hCOne : 1 ≤ C := by simpa only [C] using hcOne
      have hCC : 1 ≤ C ^ 2 := one_le_pow₀ hCOne
      have hrewrite : |l₁| / C = (C * |l₁|) / C ^ 2 := by
        field_simp [hC.ne']
      rw [hrewrite]
      exact (div_le_self (by positivity) hCC).trans hfirst
    have hl₂ : |l₂| / C ≤ R := by
      have htriangle : |l₂| / C ≤ |l₁| / C + d * |(y 1 : ℝ)| / C := by
        have heq : l₂ = l₁ + (omegaBar.re - omega.re) * (y 1 : ℝ) := by
          dsimp only [l₁, l₂]
          ring
        rw [heq]
        calc
          |l₁ + (omegaBar.re - omega.re) * (y 1 : ℝ)| / C ≤
              (|l₁| + |(omegaBar.re - omega.re) * (y 1 : ℝ)|) / C := by
                gcongr
                exact abs_add_le _ _
          _ = |l₁| / C + d * |(y 1 : ℝ)| / C := by
            rw [abs_mul]
            dsimp only [d]
            ring
      linarith
    rw [main3RealScaledTwoPlaceTargetSupNorm,
      norm_main3IntegralTargetLinearForm_eq_abs_realCoordinate omega homegaIm y,
      norm_main3IntegralTargetLinearForm_eq_abs_realCoordinate omegaBar homegaBarIm y]
    change max (C * |l₁|) (|l₂| / C) ≤ R
    exact max_le (hfirst.trans (by linarith)) hl₂
  have hmuOne : 1 ≤ firstSlopeSupNorm U V M z := by
    obtain ⟨p, hp, hpmin⟩ :=
      exists_nonzero_slopeVector_attaining_firstSupNorm U V M z hU hV hM
    let y : Fin 2 → ℤ := ![p.1, p.2]
    have hy : y ≠ 0 := by
      intro hyzero
      apply hp
      have hy0 : y 0 = 0 := by rw [hyzero]; rfl
      have hy1 : y 1 = 0 := by rw [hyzero]; rfl
      exact Prod.ext (by simpa [y] using hy0) (by simpa [y] using hy1)
    have hpairs : (y 0, y 1) = p := by
      simp only [y, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← hpmin]
    simpa only [hpairs] using (hnormOne y hy).trans (hnorm_le_slope y)
  have hslope_le_four_mul_norm (y : Fin 2 → ℤ) :
      slopeVectorSupNorm U V M z (y 0, y 1) ≤
        4 * main3RealScaledTwoPlaceTargetSupNorm c omega omegaBar y := by
    let l₁ := (y 0 : ℝ) + omega.re * (y 1 : ℝ)
    let l₂ := (y 0 : ℝ) + omegaBar.re * (y 1 : ℝ)
    let N := main3RealScaledTwoPlaceTargetSupNorm c omega omegaBar y
    have hN : 0 ≤ N := by
      dsimp only [N, main3RealScaledTwoPlaceTargetSupNorm]
      positivity
    have hfirstNorm : C * |l₁| ≤ N := by
      dsimp only [N]
      rw [main3RealScaledTwoPlaceTargetSupNorm,
        norm_main3IntegralTargetLinearForm_eq_abs_realCoordinate omega homegaIm y,
        norm_main3IntegralTargetLinearForm_eq_abs_realCoordinate omegaBar homegaBarIm y]
      exact le_max_left _ _
    have hsecondNorm : |l₂| / C ≤ N := by
      dsimp only [N]
      rw [main3RealScaledTwoPlaceTargetSupNorm,
        norm_main3IntegralTargetLinearForm_eq_abs_realCoordinate omega homegaIm y,
        norm_main3IntegralTargetLinearForm_eq_abs_realCoordinate omegaBar homegaBarIm y]
      exact le_max_right _ _
    have hl₁Over : |l₁| / C ≤ N := by
      have hCOne : 1 ≤ C := by simpa only [C] using hcOne
      have hCC : 1 ≤ C ^ 2 := one_le_pow₀ hCOne
      have hrewrite : |l₁| / C = (C * |l₁|) / C ^ 2 := by
        field_simp [hC.ne']
      rw [hrewrite]
      exact (div_le_self (by positivity) hCC).trans hfirstNorm
    have hfirstSlope :
        |M * (y 0 : ℝ) / V - z * (y 1 : ℝ) / U| ≤ 2 * N := by
      rw [hslopeFirst, abs_mul, abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_pos hC]
      dsimp only [l₁] at hfirstNorm ⊢
      nlinarith
    have hsecondSlope : |(y 1 : ℝ) / U| ≤ 4 * N := by
      rw [hslopeSecond]
      have hdiffTriangle : d * |(y 1 : ℝ)| / C ≤
          |l₂| / C + |l₁| / C := by
        have heq : (omegaBar.re - omega.re) * (y 1 : ℝ) = l₂ - l₁ := by
          dsimp only [l₁, l₂]
          ring
        dsimp only [d]
        rw [← abs_mul, heq]
        calc
          |l₂ - l₁| / C ≤ (|l₂| + |l₁|) / C :=
            div_le_div_of_nonneg_right (abs_sub _ _) hC.le
          _ = |l₂| / C + |l₁| / C := by ring
      calc
        2 * d * |(y 1 : ℝ)| / C =
            2 * (d * |(y 1 : ℝ)| / C) := by ring
        _ ≤ 2 * (|l₂| / C + |l₁| / C) := by gcongr
        _ ≤ 4 * N := by nlinarith
    rw [slopeVectorSupNorm]
    exact max_le (hfirstSlope.trans (by nlinarith)) hsecondSlope
  have hslopeBall : ∀ y ∈ T,
      slopeVectorSupNorm U V M z (y 0, y 1) ≤ 4 * H := by
    intro y hy
    exact (hslope_le_four_mul_norm y).trans
      (mul_le_mul_of_nonneg_left (hball y hy) (by norm_num))
  have hcount := card_slopeVectorSupNorm_le_linear_add_area
    T U V M z (4 * H) hU hV hM hRadius hmuOne hnonzero hslopeBall
  calc
    (T.card : ℝ) ≤ 6 * (4 * H) +
        36 * (4 * H) ^ 2 / (M / (U * V)) := hcount
    _ = 24 * H + 144 * H ^ 2 / |omegaBar.re - omega.re| := by
      dsimp only [M, U, V, C, d]
      field_simp [abs_ne_zero.mpr hc,
        abs_ne_zero.mpr (sub_ne_zero.mpr hspacing)]
      ring

/-- The chart-free two-place count.  If `|c| < 1`, swapping the two real
places and replacing `c` by `1/c` moves the norm into the chart above without
changing either the norm or the determinant spacing. -/
theorem card_main3RealScaledTwoPlaceTargetSupNorm_le_linear_add_area
    (T : Finset (Fin 2 → ℤ)) (c : ℝ) (omega omegaBar : ℂ) (H : ℝ)
    (hc : c ≠ 0)
    (homegaIm : omega.im = 0) (homegaBarIm : omegaBar.im = 0)
    (hspacing : omegaBar.re ≠ omega.re) (hH : 1 ≤ H)
    (hproduct : ∀ y : Fin 2 → ℤ, y ≠ 0 →
      1 ≤ ‖main3IntegralTargetLinearForm omega y‖ *
        ‖main3IntegralTargetLinearForm omegaBar y‖)
    (hnonzero : ∀ y ∈ T, y ≠ 0)
    (hball : ∀ y ∈ T,
      main3RealScaledTwoPlaceTargetSupNorm c omega omegaBar y ≤ H) :
    (T.card : ℝ) ≤ 24 * H + 144 * H ^ 2 / |omegaBar.re - omega.re| := by
  by_cases hchart : 1 ≤ |c|
  · exact card_main3RealScaledTwoPlaceTargetSupNorm_le_linear_add_area_of_one_le_abs
      T c omega omegaBar H hc hchart homegaIm homegaBarIm hspacing hH
        hproduct hnonzero hball
  · have hC : 0 < |c| := abs_pos.mpr hc
    have hCle : |c| ≤ 1 := le_of_lt (lt_of_not_ge hchart)
    have hcinv : (1 / c : ℝ) ≠ 0 := div_ne_zero one_ne_zero hc
    have hcinvOne : 1 ≤ |(1 / c : ℝ)| := by
      rw [abs_div, abs_one]
      exact (le_div_iff₀ hC).2 (by simpa using hCle)
    have hnormSwap (y : Fin 2 → ℤ) :
        main3RealScaledTwoPlaceTargetSupNorm (1 / c) omegaBar omega y =
          main3RealScaledTwoPlaceTargetSupNorm c omega omegaBar y := by
      unfold main3RealScaledTwoPlaceTargetSupNorm
      rw [abs_div, abs_one]
      have hleft :
          (1 / |c|) * ‖main3IntegralTargetLinearForm omegaBar y‖ =
            ‖main3IntegralTargetLinearForm omegaBar y‖ / |c| := by ring
      have hright :
          ‖main3IntegralTargetLinearForm omega y‖ / (1 / |c|) =
            |c| * ‖main3IntegralTargetLinearForm omega y‖ := by
        field_simp [ne_of_gt hC]
      rw [hleft, hright, max_comm]
    have hcount :=
      card_main3RealScaledTwoPlaceTargetSupNorm_le_linear_add_area_of_one_le_abs
        T (1 / c) omegaBar omega H hcinv hcinvOne homegaBarIm homegaIm
          (Ne.symm hspacing) hH
          (fun y hy ↦ by simpa only [mul_comm] using hproduct y hy)
          hnonzero (fun y hy ↦ by rw [hnormSwap]; exact hball y hy)
    simpa only [abs_sub_comm omega.re omegaBar.re] using hcount

/-- A fixed-basis target vector is evaluation of the corresponding integral
basis element at any embedding. -/
theorem main3IntegralTargetLinearForm_fixedBasis_embedding_eq
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (F : ShiftedSquareFixedExplicitIntegralBasisData a)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ)
    (y : Fin 2 → ℤ) :
    main3IntegralTargetLinearForm (sigma F.omega) y =
      sigma (shiftedSquareIntegralBasisElement F.basis y :
        rationalQuadraticAlgebra (-a)) := by
  have hcoord := congrArg Subtype.val
    (shiftedSquareIntegralBasisElement_eq_explicit
      F.basis F.omega F.basis_zero F.basis_one y)
  calc
    main3IntegralTargetLinearForm (sigma F.omega) y =
        sigma ((y 0 : rationalQuadraticAlgebra (-a)) +
          (y 1 : rationalQuadraticAlgebra (-a)) * F.omega) := by
      simp only [main3IntegralTargetLinearForm, map_add, map_mul, map_intCast]
      ring
    _ = sigma (shiftedSquareIntegralBasisElement F.basis y :
          rationalQuadraticAlgebra (-a)) := congrArg sigma hcoord.symm

/-- The product of the two real-place norms of a nonzero integral fixed-basis
vector is at least one.  This is the arithmetic input which makes the
determinant-one max norm nondegenerate uniformly in the rescaling `c`. -/
theorem one_le_mul_norm_main3IntegralTargetLinearForm_fixedBasis_positiveRealPlaces
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (ha : a < 0) (F : ShiftedSquareFixedExplicitIntegralBasisData a)
    (y : Fin 2 → ℤ) (hy : y ≠ 0) :
    1 ≤
      ‖main3IntegralTargetLinearForm
          (shiftedSquarePositiveRealPlaceEmbedding a ha F.omega) y‖ *
        ‖main3IntegralTargetLinearForm
          (shiftedSquarePositiveRealPlaceEmbedding a ha (star F.omega)) y‖ := by
  let z := shiftedSquareIntegralBasisElement F.basis y
  let sigma := shiftedSquarePositiveRealPlaceEmbedding a ha
  let q := shiftedSquareExplicitNormFormEval F.t F.c y
  have hz : z ≠ 0 := by
    intro hzZero
    apply hy
    apply F.basis.equivFun.symm.injective
    simpa only [z, shiftedSquareIntegralBasisElement, map_zero] using hzZero
  have hzField : (z : rationalQuadraticAlgebra (-a)) ≠ 0 := by
    intro hzZero
    apply hz
    exact Subtype.ext hzZero
  have hmul : (z : rationalQuadraticAlgebra (-a)) *
      star (z : rationalQuadraticAlgebra (-a)) =
      (q : rationalQuadraticAlgebra (-a)) := by
    simpa only [z, q] using
      shiftedSquare_integralBasisElement_mul_star_eq_explicitNormForm
        F.basis F.omega F.t F.c F.basis_zero F.basis_one F.omega_sq y
  have hq : q ≠ 0 := by
    intro hqZero
    have hprodZero : (z : rationalQuadraticAlgebra (-a)) *
        star (z : rationalQuadraticAlgebra (-a)) = 0 := by
      rw [hmul, hqZero]
      simp
    exact hzField (mul_eq_zero.mp hprodZero |>.resolve_right (by
      simpa only [star_eq_zero] using hzField))
  have hstarCoord :
      main3IntegralTargetLinearForm
          (sigma (star (F.omega : rationalQuadraticAlgebra (-a)))) y =
        sigma (star (z : rationalQuadraticAlgebra (-a))) := by
    have hcoord : (z : rationalQuadraticAlgebra (-a)) =
        (y 0 : rationalQuadraticAlgebra (-a)) +
          (y 1 : rationalQuadraticAlgebra (-a)) * F.omega := by
      exact congrArg Subtype.val
        (shiftedSquareIntegralBasisElement_eq_explicit
          F.basis F.omega F.basis_zero F.basis_one y)
    have hstar :
        star (z : rationalQuadraticAlgebra (-a)) =
          (y 0 : rationalQuadraticAlgebra (-a)) +
            (y 1 : rationalQuadraticAlgebra (-a)) *
              star (F.omega : rationalQuadraticAlgebra (-a)) := by
      rw [hcoord]
      simp only [star_add, star_mul, star_intCast]
      ring
    calc
      main3IntegralTargetLinearForm
          (sigma (star (F.omega : rationalQuadraticAlgebra (-a)))) y =
          sigma ((y 0 : rationalQuadraticAlgebra (-a)) +
            (y 1 : rationalQuadraticAlgebra (-a)) *
              star (F.omega : rationalQuadraticAlgebra (-a))) := by
        simp only [main3IntegralTargetLinearForm, map_add, map_mul, map_intCast]
        ring
      _ = sigma (star (z : rationalQuadraticAlgebra (-a))) :=
        congrArg sigma hstar.symm
  have hnormProduct :
      ‖sigma (z : rationalQuadraticAlgebra (-a))‖ *
          ‖sigma (star (z : rationalQuadraticAlgebra (-a)))‖ =
        |(q : ℝ)| := by
    rw [← norm_mul, ← map_mul, hmul, map_intCast, Complex.norm_intCast]
  have hqOneZ : (1 : ℤ) ≤ |q| := Int.one_le_abs hq
  have hqOneR : (1 : ℝ) ≤ |(q : ℝ)| := by exact_mod_cast hqOneZ
  rw [main3IntegralTargetLinearForm_fixedBasis_embedding_eq F sigma y,
    hstarCoord]
  rw [hnormProduct]
  exact hqOneR

/-- Every nonzero fixed-basis vector has determinant-one two-place norm at
least one, uniformly in the nonzero real scaling parameter. -/
theorem one_le_main3RealScaledTwoPlaceTargetSupNorm_fixedBasis_positiveRealPlaces
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (ha : a < 0) (F : ShiftedSquareFixedExplicitIntegralBasisData a)
    (c : ℝ) (hc : c ≠ 0) (y : Fin 2 → ℤ) (hy : y ≠ 0) :
    1 ≤ main3RealScaledTwoPlaceTargetSupNorm c
      (shiftedSquarePositiveRealPlaceEmbedding a ha F.omega)
      (shiftedSquarePositiveRealPlaceEmbedding a ha (star F.omega)) y := by
  apply one_le_main3RealScaledTwoPlaceTargetSupNorm_of_one_le_norm_product
    c _ _ y hc
  exact one_le_mul_norm_main3IntegralTargetLinearForm_fixedBasis_positiveRealPlaces
    ha F y hy

/-- At the two positive-real-place conjugates, the fixed integral basis has
spacing exactly the square root of the absolute field discriminant. -/
theorem abs_re_sub_re_shiftedSquareFixedBasis_positiveRealPlace_omega
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (ha : a < 0) (F : ShiftedSquareFixedExplicitIntegralBasisData a) :
    |(shiftedSquarePositiveRealPlaceEmbedding a ha (star F.omega)).re -
        (shiftedSquarePositiveRealPlaceEmbedding a ha F.omega).re| =
      Real.sqrt
        |(NumberField.discr (rationalQuadraticAlgebra (-a)) : ℝ)| := by
  let sigma := shiftedSquarePositiveRealPlaceEmbedding a ha
  let omega := sigma (F.omega : rationalQuadraticAlgebra (-a))
  let omegaBar := sigma (star (F.omega : rationalQuadraticAlgebra (-a)))
  let Delta := Real.sqrt
    |(NumberField.discr (rationalQuadraticAlgebra (-a)) : ℝ)|
  have hdiff : ‖omega - omegaBar‖ = Delta := by
    calc
      ‖omega - omegaBar‖ = Real.sqrt (‖omega - omegaBar‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Delta := by
        congr 1
        simpa only [omega, omegaBar, Delta, ← map_sub] using
          shiftedSquareFixedBasis_embeddingDifference_norm_sq F sigma
  have homegaIm : omega.im = 0 := by
    dsimp only [omega, sigma]
    simp [shiftedSquarePositiveRealPlaceEmbedding_apply]
  have homegaBarIm : omegaBar.im = 0 := by
    dsimp only [omegaBar, sigma]
    simp [shiftedSquarePositiveRealPlaceEmbedding_apply]
  have hdiffIm : (omega - omegaBar).im = 0 := by
    simp only [Complex.sub_im, homegaIm, homegaBarIm, sub_self]
  calc
    |omegaBar.re - omega.re| = |(omega - omegaBar).re| := by
      simp only [Complex.sub_re, abs_sub_comm]
    _ = ‖omega - omegaBar‖ := (Complex.abs_re_eq_norm.mpr hdiffIm)
    _ = Delta := hdiff

/-- Fixed-basis specialization of the two-real-place lattice count, with the
literal field-discriminant spacing required by Main3. -/
theorem card_shiftedSquareFixedBasis_positiveRealPlace_scaledTwoPlace_norm_le_linear_add_area
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (ha : a < 0) (F : ShiftedSquareFixedExplicitIntegralBasisData a)
    (T : Finset (Fin 2 → ℤ)) (c H : ℝ) (hc : c ≠ 0) (hH : 1 ≤ H)
    (hnonzero : ∀ y ∈ T, y ≠ 0)
    (hball : ∀ y ∈ T,
      main3RealScaledTwoPlaceTargetSupNorm c
        (shiftedSquarePositiveRealPlaceEmbedding a ha F.omega)
        (shiftedSquarePositiveRealPlaceEmbedding a ha (star F.omega)) y ≤ H) :
    (T.card : ℝ) ≤ 24 * H + 144 * H ^ 2 /
      Real.sqrt
        |(NumberField.discr (rationalQuadraticAlgebra (-a)) : ℝ)| := by
  let sigma := shiftedSquarePositiveRealPlaceEmbedding a ha
  let omega := sigma (F.omega : rationalQuadraticAlgebra (-a))
  let omegaBar := sigma (star (F.omega : rationalQuadraticAlgebra (-a)))
  let Delta := Real.sqrt
    |(NumberField.discr (rationalQuadraticAlgebra (-a)) : ℝ)|
  have homegaIm : omega.im = 0 := by
    dsimp only [omega, sigma]
    simp [shiftedSquarePositiveRealPlaceEmbedding_apply]
  have homegaBarIm : omegaBar.im = 0 := by
    dsimp only [omegaBar, sigma]
    simp [shiftedSquarePositiveRealPlaceEmbedding_apply]
  have hDelta : |omegaBar.re - omega.re| = Delta := by
    simpa only [omega, omegaBar, sigma, Delta] using
      abs_re_sub_re_shiftedSquareFixedBasis_positiveRealPlace_omega ha F
  have hDeltaPos : 0 < Delta := by
    have hdisc :
        (NumberField.discr (rationalQuadraticAlgebra (-a)) : ℝ) ≠ 0 := by
      exact_mod_cast NumberField.discr_ne_zero (rationalQuadraticAlgebra (-a))
    dsimp only [Delta]
    exact Real.sqrt_pos.2 (abs_pos.mpr hdisc)
  have hspacing : omegaBar.re ≠ omega.re := by
    exact sub_ne_zero.mp (abs_pos.mp (hDelta.symm ▸ hDeltaPos))
  have hcount := card_main3RealScaledTwoPlaceTargetSupNorm_le_linear_add_area
    T c omega omegaBar H hc homegaIm homegaBarIm hspacing hH
      (fun y hy ↦ by
        simpa only [omega, omegaBar, sigma] using
          one_le_mul_norm_main3IntegralTargetLinearForm_fixedBasis_positiveRealPlaces
            ha F y hy)
      hnonzero
      (fun y hy ↦ by simpa only [omega, omegaBar, sigma] using hball y hy)
  simpa only [hDelta, Delta] using hcount

/-- Filtering the image of a nonzero fixed-basis vector assignment by its
two-real-place norm inherits the Main3 discriminant-sensitive ball bound. -/
theorem card_fixedBasisVectorImage_filter_scaledTwoPlace_norm_le_linear_add_area
    {ι : Type*} {a : ℤ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (F : ShiftedSquareFixedExplicitIntegralBasisData a) (ha : a < 0)
    (I : Finset ι) (f : ι → Fin 2 → ℤ)
    (hnonzero : ∀ i ∈ I, f i ≠ 0)
    (c t : ℝ) (hc : c ≠ 0) (ht : 1 ≤ t) :
    (((I.image f).filter fun y ↦
        main3RealScaledTwoPlaceTargetSupNorm c
          (shiftedSquarePositiveRealPlaceEmbedding a ha F.omega)
          (shiftedSquarePositiveRealPlaceEmbedding a ha (star F.omega)) y ≤ t).card : ℝ) ≤
      24 * t + (144 /
        Real.sqrt |(NumberField.discr
          (rationalQuadraticAlgebra (-a)) : ℝ)|) * t ^ 2 := by
  classical
  let V := (I.image f).filter fun y ↦
    main3RealScaledTwoPlaceTargetSupNorm c
      (shiftedSquarePositiveRealPlaceEmbedding a ha F.omega)
      (shiftedSquarePositiveRealPlaceEmbedding a ha (star F.omega)) y ≤ t
  have hcount :=
    card_shiftedSquareFixedBasis_positiveRealPlace_scaledTwoPlace_norm_le_linear_add_area
      ha F V c t hc ht
        (by
          intro y hy
          have hyImage := (Finset.mem_filter.mp hy).1
          obtain ⟨i, hi, hify⟩ := Finset.mem_image.mp hyImage
          rw [← hify]
          exact hnonzero i hi)
        (by
          intro y hy
          exact (Finset.mem_filter.mp hy).2)
  calc
    (V.card : ℝ) ≤ 24 * t + 144 * t ^ 2 /
        Real.sqrt |(NumberField.discr
          (rationalQuadraticAlgebra (-a)) : ℝ)| := hcount
    _ = 24 * t + (144 /
        Real.sqrt |(NumberField.discr
          (rationalQuadraticAlgebra (-a)) : ℝ)|) * t ^ 2 := by ring

end

end PellPaper
