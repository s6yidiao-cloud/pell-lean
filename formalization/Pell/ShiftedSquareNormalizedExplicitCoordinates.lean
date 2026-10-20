import Pell.ShiftedSquareExplicitIntegralBasis
import Pell.ShiftedSquareMinkowskiCoordinates
import Pell.ShiftedSquareMinkowskiC0NuAbsBound
import Pell.ShiftedSquareSurfaceForm
import Mathlib.Tactic

/-!
# Normalized explicit coordinates for the shifted-square surface

This isolated candidate combines the reviewed Minkowski factorization with
the canonical explicit integral-basis module.  The explicit basis fixes the
nonzero zeta coordinate at index `1`, so the abstract selected-coordinate
choice is no longer needed.

All dependencies imported here are canonical modules.
-/

namespace PellPaper

noncomputable section

local instance shiftedSquareNormalizedExplicitCoordinates_numberField (a : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

/-- The quadratic norm polynomial in a basis `1, omega` satisfying
`omega^2 = t*omega + c`. -/
def shiftedSquareExplicitNormFormEval
    (t c : ℤ) (x : Fin 2 → ℤ) : ℤ :=
  x 0 ^ 2 + t * x 0 * x 1 - c * x 1 ^ 2

/-- Reconstruction in a displayed basis `1, omega`. -/
theorem shiftedSquareIntegralBasisElement_eq_explicit
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (b : Module.Basis (Fin 2) ℤ
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))))
    (omega : NumberField.RingOfIntegers
      (rationalQuadraticAlgebra (-a)))
    (hb0 : b 0 = 1) (hb1 : b 1 = omega) (x : Fin 2 → ℤ) :
    shiftedSquareIntegralBasisElement b x =
      (x 0 : NumberField.RingOfIntegers
        (rationalQuadraticAlgebra (-a))) + x 1 * omega := by
  rw [shiftedSquareIntegralBasisElement_eq, hb0, hb1]
  simp only [zsmul_eq_mul]
  ring

/-- Left multiplication in a displayed quadratic basis has the usual
two-by-two companion matrix. -/
theorem shiftedSquareExplicitBasis_leftMulMatrix
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (b : Module.Basis (Fin 2) ℤ
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))))
    (omega : NumberField.RingOfIntegers
      (rationalQuadraticAlgebra (-a))) (t c : ℤ)
    (hb0 : b 0 = 1) (hb1 : b 1 = omega)
    (homega : omega ^ 2 =
      (t : NumberField.RingOfIntegers
        (rationalQuadraticAlgebra (-a))) * omega + c)
    (x : Fin 2 → ℤ) :
    Algebra.leftMulMatrix b (shiftedSquareIntegralBasisElement b x) =
      !![x 0, c * x 1; x 1, x 0 + t * x 1] := by
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul, Matrix.of_apply]
  fin_cases j
  · simp only [Fin.zero_eta]
    rw [hb0, mul_one]
    have hcoordinates := shiftedSquareIntegralBasisCoordinates_element b x
    change shiftedSquareIntegralBasisCoordinates b
      (shiftedSquareIntegralBasisElement b x) i = _
    rw [hcoordinates]
    fin_cases i <;> rfl
  · change b.repr (shiftedSquareIntegralBasisElement b x * b 1) i =
      !![x 0, c * x 1; x 1, x 0 + t * x 1] i 1
    rw [hb1]
    have hmul : shiftedSquareIntegralBasisElement b x * omega =
        (c * x 1 : ℤ) • b 0 + (x 0 + t * x 1 : ℤ) • b 1 := by
      rw [shiftedSquareIntegralBasisElement_eq_explicit b omega hb0 hb1,
        hb0, hb1]
      simp only [zsmul_eq_mul]
      push_cast
      linear_combination (x 1 : NumberField.RingOfIntegers
        (rationalQuadraticAlgebra (-a))) * homega
    rw [hmul]
    simp only [map_add, map_zsmul, Finsupp.add_apply,
      Finsupp.smul_apply, smul_eq_mul, Module.Basis.repr_self_apply]
    fin_cases i <;> simp

/-- The integral norm in a displayed basis is the explicit quadratic norm
form determined by the generator relation. -/
theorem shiftedSquareIntegralBasisNormEval_eq_explicit
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (b : Module.Basis (Fin 2) ℤ
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))))
    (omega : NumberField.RingOfIntegers
      (rationalQuadraticAlgebra (-a))) (t c : ℤ)
    (hb0 : b 0 = 1) (hb1 : b 1 = omega)
    (homega : omega ^ 2 =
      (t : NumberField.RingOfIntegers
        (rationalQuadraticAlgebra (-a))) * omega + c)
    (x : Fin 2 → ℤ) :
    shiftedSquareIntegralBasisNormEval b x =
      shiftedSquareExplicitNormFormEval t c x := by
  rw [shiftedSquareIntegralBasisNormEval_eq_algebraNorm,
    Algebra.norm_eq_matrix_det b,
    shiftedSquareExplicitBasis_leftMulMatrix b omega t c hb0 hb1 homega,
    Matrix.det_fin_two]
  simp [shiftedSquareExplicitNormFormEval]
  ring

/-- At coordinate `1`, the generic bidegree-`(2,1)` multiplication form is
exactly the special surface form attached to `omega^2 = t*omega + c`. -/
theorem shiftedSquareIntegralBasisQuadraticLinear_eval_one_eq_surfaceForm
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (b : Module.Basis (Fin 2) ℤ
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))))
    (omega : NumberField.RingOfIntegers
      (rationalQuadraticAlgebra (-a))) (t c : ℤ)
    (hb0 : b 0 = 1) (hb1 : b 1 = omega)
    (homega : omega ^ 2 =
      (t : NumberField.RingOfIntegers
        (rationalQuadraticAlgebra (-a))) * omega + c)
    (x y : Fin 2 → ℤ) :
    quadraticLinearFormEval
        (shiftedSquareIntegralBasisQuadraticLinearCoefficients b 1) x y =
      (shiftedSquareSurfaceForm t c y).eval (x 0) (x 1) := by
  rw [← shiftedSquareIntegralBasis_sq_mul_coordinate b x y 1,
    shiftedSquareSurfaceForm_eval]
  let A0 : ℤ := x 0 ^ 2 + c * x 1 ^ 2
  let P : ℤ := shiftedSquareSurfaceP t x
  let A : ℤ := A0 * y 0 + c * P * y 1
  let B : ℤ := shiftedSquareSurfaceP t x * y 0 +
    shiftedSquareSurfaceQ t c x * y 1
  have hsquare : shiftedSquareIntegralBasisElement b x ^ 2 =
      (A0 : NumberField.RingOfIntegers
        (rationalQuadraticAlgebra (-a))) + P * omega := by
    rw [shiftedSquareIntegralBasisElement_eq_explicit b omega hb0 hb1]
    dsimp only [A0, P, shiftedSquareSurfaceP]
    push_cast
    linear_combination (x 1 : NumberField.RingOfIntegers
      (rationalQuadraticAlgebra (-a))) ^ 2 * homega
  have hproduct :
      shiftedSquareIntegralBasisElement b x ^ 2 *
          shiftedSquareIntegralBasisElement b y =
        (A : NumberField.RingOfIntegers
          (rationalQuadraticAlgebra (-a))) + B * omega := by
    rw [hsquare,
      shiftedSquareIntegralBasisElement_eq_explicit b omega hb0 hb1]
    simp only [A, B, A0, P, shiftedSquareSurfaceP,
      shiftedSquareSurfaceQ]
    push_cast
    linear_combination
      (2 * (x 0 : NumberField.RingOfIntegers
        (rationalQuadraticAlgebra (-a))) * x 1 + t * x 1 ^ 2) *
          (y 1 : NumberField.RingOfIntegers
            (rationalQuadraticAlgebra (-a))) * homega
  rw [hproduct]
  have hcomb :
      (A : NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))) +
          B * omega =
        A • b 0 + B • b 1 := by
    rw [hb0, hb1]
    simp only [zsmul_eq_mul]
    ring
  rw [hcomb]
  simp only [shiftedSquareIntegralBasisCoordinates, map_add, map_zsmul,
    Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
    Module.Basis.repr_self_apply]
  dsimp only [B]
  norm_num

/-! ## The normalized project-facing package -/

/-- The full explicit coordinate package used after the Minkowski step.
The selected coordinate is fixed literally at `1`; there is no abstract
coordinate selector in this structure. -/
structure ShiftedSquareNormalizedExplicitCoordinatePackage
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a) where
  basis : Module.Basis (Fin 2) ℤ
    (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a)))
  omega : NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))
  t : ℤ
  c : ℤ
  basis_zero : basis 0 = 1
  basis_one : basis 1 = omega
  t_zero_or_one : t = 0 ∨ t = 1
  omega_sq : omega ^ 2 =
    (t : NumberField.RingOfIntegers
      (rationalQuadraticAlgebra (-a))) * omega + c
  bζ : ℤ
  bζ_eq_coordinate : bζ = shiftedSquareIntegralBasisCoordinates basis
    (shiftedSquareZetaInteger heq) 1
  bζ_eq_one_or_two : bζ = 1 ∨ bζ = 2
  bζ_ne_zero : bζ ≠ 0
  abs_bζ_le_two : |bζ| ≤ 2
  mu : NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))
  C₀ : ℕ
  nu : NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))
  Q : Ideal (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a)))
  r : ℕ
  ell : ℕ
  x : Fin 2 → ℤ
  y : Fin 2 → ℤ
  mu_mem : mu ∈ shiftedSquareIdealDivisor heq
  mu_ne_zero : mu ≠ 0
  nu_ne_zero : nu ≠ 0
  C₀_pos : 0 < C₀
  C₀_le_two_mul_sqrt_abs : (C₀ : ℝ) ≤ 2 * Real.sqrt |a|
  mu_principal_eq_ideal_mul_Q :
    Ideal.span {mu} = shiftedSquareIdealDivisor heq * Q
  Q_absNorm : Ideal.absNorm Q = C₀
  C₀_ideal_mul_le_mu_principal :
    Ideal.span
        {(C₀ : NumberField.RingOfIntegers
          (rationalQuadraticAlgebra (-a)))} *
      shiftedSquareIdealDivisor heq ≤ Ideal.span {mu}
  r_pos : 0 < r
  ell_pos : 0 < ell
  x_primitive : IsCoprime (x 0) (x 1)
  y_primitive : IsCoprime (y 0) (y 1)
  mu_coordinates :
    mu = (r : ℤ) • shiftedSquareIntegralBasisElement basis x
  nu_coordinates :
    nu = (ell : ℤ) • shiftedSquareIntegralBasisElement basis y
  factorization :
    mu ^ 2 * nu =
      (C₀ : NumberField.RingOfIntegers
        (rationalQuadraticAlgebra (-a))) ^ 2 *
        shiftedSquareZetaInteger heq
  mu_norm_form :
    (r : ℤ) ^ 2 * |shiftedSquareExplicitNormFormEval t c x| =
      ((shiftedSquareD₀ d * C₀ : ℕ) : ℤ)
  nu_norm_form :
    (ell : ℤ) ^ 2 * shiftedSquareExplicitNormFormEval t c y =
      ((w * C₀ ^ 2 : ℕ) : ℤ)
  special_surface_relation :
    ((r : ℤ) ^ 2 * (ell : ℤ)) *
        (shiftedSquareSurfaceForm t c y).eval (x 0) (x 1) =
      (C₀ : ℤ) ^ 2 * bζ
  special_surface_level_ne_zero :
    (shiftedSquareSurfaceForm t c y).eval (x 0) (x 1) ≠ 0
  ell_sq_dvd : ell ^ 2 ∣ w * C₀ ^ 2
  ell_dvd_C₀ : ell ∣ C₀
  normalized_target_norm :
    shiftedSquareExplicitNormFormEval t c y =
      ((w * (C₀ / ell) ^ 2 : ℕ) : ℤ)
  surface_content_pos :
    0 < integralBinaryQuadraticFormContent
      (shiftedSquareSurfaceForm t c y)
  surface_content_dvd_two :
    integralBinaryQuadraticFormContent
      (shiftedSquareSurfaceForm t c y) ∣ 2
  primitive_surface :
    (integralBinaryQuadraticFormPrimitivePart
      (shiftedSquareSurfaceForm t c y)).Primitive
  primitive_surface_discriminant_pos :
    0 < (integralBinaryQuadraticFormPrimitivePart
      (shiftedSquareSurfaceForm t c y)).discriminant
  primitive_surface_discriminant_not_isSquare :
    ¬ IsSquare (integralBinaryQuadraticFormPrimitivePart
      (shiftedSquareSurfaceForm t c y)).discriminant
  primitive_surface_discriminant_scale :
    ∃ s : ℕ, 0 < s ∧
      (s = 2 * (C₀ / ell) ∨ s = C₀ / ell) ∧
      (integralBinaryQuadraticFormPrimitivePart
          (shiftedSquareSurfaceForm t c y)).discriminant =
        ((w * s ^ 2 : ℕ) : ℤ)

/-- For squarefree `w > 1`, the shifted-square Minkowski factorization has
normalized explicit coordinates with selected coordinate `1`, bounded
zeta coefficient, exact norm and special-surface equations, `ell | C₀`, and
a primitive positive nonsquare surface discriminant. -/
theorem exists_shiftedSquareNormalizedExplicitCoordinatePackage
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (ha : Squarefree a) (hd : 0 < d)
    (hw : Squarefree w) (hwone : 1 < w)
    (heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a) :
    Nonempty (ShiftedSquareNormalizedExplicitCoordinatePackage heq) := by
  obtain ⟨b, omega, t, c, hb0, hb1, ht, homega, hbζall⟩ :=
    exists_shiftedSquareExplicitIntegralBasis_package ha
  let bζ : ℤ := shiftedSquareIntegralBasisCoordinates b
    (shiftedSquareZetaInteger heq) 1
  have hbζdata : (bζ = 1 ∨ bζ = 2) ∧ bζ ≠ 0 ∧ |bζ| ≤ 2 := by
    simpa only [bζ, shiftedSquareIntegralBasisCoordinates] using hbζall heq
  obtain ⟨mu, C₀, nu, Q, hmu, hmu0, hC₀, hmuNorm, hfactor,
      hnuNorm, hC₀bound, hQ, hQnorm, hC₀I⟩ :=
    exists_shiftedSquareMinkowskiC₀Nu_package_abs_bound ha hd heq
  have hwpos : 0 < w := lt_trans Nat.zero_lt_one hwone
  have hnu0 : nu ≠ 0 :=
    shiftedSquareNu_ne_zero_of_norm hwpos hC₀ hnuNorm
  obtain ⟨r, hr, x, hx, hmuCoordinates⟩ :=
    exists_positive_content_primitive_shiftedSquareIntegralBasisCoordinates
      b hmu0
  obtain ⟨ell, hell, y, hy, hnuCoordinates⟩ :=
    exists_positive_content_primitive_shiftedSquareIntegralBasisCoordinates
      b hnu0
  have hmuForm :
      (r : ℤ) ^ 2 * |shiftedSquareExplicitNormFormEval t c x| =
        ((shiftedSquareD₀ d * C₀ : ℕ) : ℤ) := by
    have h := shiftedSquare_mu_primitive_norm_equation
      b hmuCoordinates hmuNorm
    rwa [shiftedSquareIntegralBasisNormEval_eq_explicit
      b omega t c hb0 hb1 homega] at h
  have hnuForm :
      (ell : ℤ) ^ 2 * shiftedSquareExplicitNormFormEval t c y =
        ((w * C₀ ^ 2 : ℕ) : ℤ) := by
    have h := shiftedSquare_nu_primitive_norm_equation
      b hnuCoordinates hnuNorm
    rwa [shiftedSquareIntegralBasisNormEval_eq_explicit
      b omega t c hb0 hb1 homega] at h
  have hcoordinate := shiftedSquareIntegralBasis_scaled_coordinate_relation
    b hmuCoordinates hnuCoordinates hfactor (1 : Fin 2)
  have heval :=
    shiftedSquareIntegralBasisQuadraticLinear_eval_one_eq_surfaceForm
      b omega t c hb0 hb1 homega x y
  have hsurface :
      ((r : ℤ) ^ 2 * (ell : ℤ)) *
          (shiftedSquareSurfaceForm t c y).eval (x 0) (x 1) =
        (C₀ : ℤ) ^ 2 * bζ := by
    calc
      ((r : ℤ) ^ 2 * (ell : ℤ)) *
          (shiftedSquareSurfaceForm t c y).eval (x 0) (x 1) =
          ((r : ℤ) ^ 2 * (ell : ℤ)) *
            quadraticLinearFormEval
              (shiftedSquareIntegralBasisQuadraticLinearCoefficients b 1) x y :=
        congrArg (fun z : ℤ => ((r : ℤ) ^ 2 * (ell : ℤ)) * z) heval.symm
      _ = (C₀ : ℤ) ^ 2 *
          shiftedSquareIntegralBasisCoordinates b
            (shiftedSquareZetaInteger heq) 1 := hcoordinate
      _ = (C₀ : ℤ) ^ 2 * bζ := rfl
  have hellSqDvdZ : (ell : ℤ) ^ 2 ∣
      ((w * C₀ ^ 2 : ℕ) : ℤ) :=
    ⟨shiftedSquareExplicitNormFormEval t c y, hnuForm.symm⟩
  have hsurface0 :
      (shiftedSquareSurfaceForm t c y).eval (x 0) (x 1) ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hsurface
    have hC₀ne : (C₀ : ℤ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hC₀)
    exact (mul_ne_zero (pow_ne_zero 2 hC₀ne) hbζdata.2.1)
      hsurface.symm
  have hellSqDvd : ell ^ 2 ∣ w * C₀ ^ 2 := by
    exact_mod_cast hellSqDvdZ
  have hellC₀ : ell ∣ C₀ :=
    dvd_of_sq_dvd_squarefree_mul_sq hwpos hw hellSqDvd
  have hnormalized :
      shiftedSquareExplicitNormFormEval t c y =
        ((w * (C₀ / ell) ^ 2 : ℕ) : ℤ) := by
    have hmul : ell * (C₀ / ell) = C₀ :=
      Nat.mul_div_cancel' hellC₀
    have hsq : C₀ ^ 2 = ell ^ 2 * (C₀ / ell) ^ 2 := by
      calc
        C₀ ^ 2 = (ell * (C₀ / ell)) ^ 2 := congrArg (· ^ 2) hmul.symm
        _ = ell ^ 2 * (C₀ / ell) ^ 2 := by ring
    apply mul_left_cancel₀ (pow_ne_zero 2 (by
      exact_mod_cast (Nat.ne_of_gt hell) : (ell : ℤ) ≠ 0))
    calc
      (ell : ℤ) ^ 2 * shiftedSquareExplicitNormFormEval t c y =
          ((w * C₀ ^ 2 : ℕ) : ℤ) := hnuForm
      _ = (ell : ℤ) ^ 2 * ((w * (C₀ / ell) ^ 2 : ℕ) : ℤ) := by
        exact_mod_cast (show w * C₀ ^ 2 =
            ell ^ 2 * (w * (C₀ / ell) ^ 2) by
          rw [hsq]
          ring)
  have hdisc :=
    shiftedSquareSurfacePrimitivePart_discriminant_pos_not_isSquare
      t c y hy ht hell hw hwone hC₀ hellSqDvd hnormalized
  refine ⟨{
    basis := b
    omega := omega
    t := t
    c := c
    basis_zero := hb0
    basis_one := hb1
    t_zero_or_one := ht
    omega_sq := homega
    bζ := bζ
    bζ_eq_coordinate := rfl
    bζ_eq_one_or_two := hbζdata.1
    bζ_ne_zero := hbζdata.2.1
    abs_bζ_le_two := hbζdata.2.2
    mu := mu
    C₀ := C₀
    nu := nu
    Q := Q
    r := r
    ell := ell
    x := x
    y := y
    mu_mem := hmu
    mu_ne_zero := hmu0
    nu_ne_zero := hnu0
    C₀_pos := hC₀
    C₀_le_two_mul_sqrt_abs := hC₀bound
    mu_principal_eq_ideal_mul_Q := hQ
    Q_absNorm := hQnorm
    C₀_ideal_mul_le_mu_principal := hC₀I
    r_pos := hr
    ell_pos := hell
    x_primitive := hx
    y_primitive := hy
    mu_coordinates := hmuCoordinates
    nu_coordinates := hnuCoordinates
    factorization := hfactor
    mu_norm_form := hmuForm
    nu_norm_form := hnuForm
    special_surface_relation := hsurface
    special_surface_level_ne_zero := hsurface0
    ell_sq_dvd := hellSqDvd
    ell_dvd_C₀ := hellC₀
    normalized_target_norm := hnormalized
    surface_content_pos := shiftedSquareSurfaceForm_content_pos t c y hy
    surface_content_dvd_two := shiftedSquareSurfaceForm_content_dvd_two t c y hy
    primitive_surface := hdisc.1
    primitive_surface_discriminant_pos := hdisc.2.2.1
    primitive_surface_discriminant_not_isSquare := hdisc.2.2.2.1
    primitive_surface_discriminant_scale := hdisc.2.2.2.2 }⟩

end

end PellPaper
