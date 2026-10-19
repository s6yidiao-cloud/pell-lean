import Pell.ShiftedSquareMinkowskiEmbeddingC0Nu
import Pell.ShiftedSquareNormalizedExplicitCoordinates
import Mathlib.Tactic

/-!
# Normalized coordinates from one simultaneous-box Minkowski element

This isolated candidate combines the reviewed simultaneous-embedding package
with the explicit integral basis.  The nested Minkowski record ensures that
the element used for every embedding bound is literally the element whose
coordinates, norm, ideal quotient, and `C₀`--`nu` factorization are used below.
-/

namespace PellPaper

noncomputable section

local instance shiftedSquareSimultaneousNormalizedCoordinates_numberField (a : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

/-- Explicit primitive coordinates and special-surface data attached to a
single simultaneous-box Minkowski package. -/
structure ShiftedSquareSimultaneousNormalizedCoordinatePackage
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a) where
  minkowski : ShiftedSquareMinkowskiEmbeddingC₀NuPackage heq
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
  nu_ne_zero : minkowski.nu ≠ 0
  r : ℕ
  ell : ℕ
  x : Fin 2 → ℤ
  y : Fin 2 → ℤ
  r_pos : 0 < r
  ell_pos : 0 < ell
  x_primitive : IsCoprime (x 0) (x 1)
  y_primitive : IsCoprime (y 0) (y 1)
  mu_coordinates :
    minkowski.mu = (r : ℤ) • shiftedSquareIntegralBasisElement basis x
  nu_coordinates :
    minkowski.nu = (ell : ℤ) • shiftedSquareIntegralBasisElement basis y
  mu_norm_form :
    (r : ℤ) ^ 2 * |shiftedSquareExplicitNormFormEval t c x| =
      ((shiftedSquareD₀ d * minkowski.C₀ : ℕ) : ℤ)
  nu_norm_form :
    (ell : ℤ) ^ 2 * shiftedSquareExplicitNormFormEval t c y =
      ((w * minkowski.C₀ ^ 2 : ℕ) : ℤ)
  special_surface_relation :
    ((r : ℤ) ^ 2 * (ell : ℤ)) *
        (shiftedSquareSurfaceForm t c y).eval (x 0) (x 1) =
      (minkowski.C₀ : ℤ) ^ 2 * bζ
  special_surface_level_ne_zero :
    (shiftedSquareSurfaceForm t c y).eval (x 0) (x 1) ≠ 0
  ell_sq_dvd : ell ^ 2 ∣ w * minkowski.C₀ ^ 2
  ell_dvd_C₀ : ell ∣ minkowski.C₀
  normalized_target_norm :
    shiftedSquareExplicitNormFormEval t c y =
      ((w * (minkowski.C₀ / ell) ^ 2 : ℕ) : ℤ)
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
      (s = 2 * (minkowski.C₀ / ell) ∨ s = minkowski.C₀ / ell) ∧
      (integralBinaryQuadraticFormPrimitivePart
          (shiftedSquareSurfaceForm t c y)).discriminant =
        ((w * s ^ 2 : ℕ) : ℤ)

/-- The simultaneous-box element admits the complete normalized explicit
coordinate package, while preserving the same element and all its embedding
bounds through the nested `minkowski` field. -/
theorem exists_shiftedSquareSimultaneousNormalizedCoordinatePackage
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (ha : Squarefree a) (hd : 0 < d)
    (hw : Squarefree w) (hwone : 1 < w)
    (heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a) :
    Nonempty (ShiftedSquareSimultaneousNormalizedCoordinatePackage heq) := by
  obtain ⟨b, omega, t, c, hb0, hb1, ht, homega, hbζall⟩ :=
    exists_shiftedSquareExplicitIntegralBasis_package ha
  let bζ : ℤ := shiftedSquareIntegralBasisCoordinates b
    (shiftedSquareZetaInteger heq) 1
  have hbζdata : (bζ = 1 ∨ bζ = 2) ∧ bζ ≠ 0 ∧ |bζ| ≤ 2 := by
    simpa only [bζ, shiftedSquareIntegralBasisCoordinates] using hbζall heq
  obtain ⟨M⟩ := exists_shiftedSquareMinkowskiEmbeddingC₀Nu_package ha hd heq
  have hwpos : 0 < w := lt_trans Nat.zero_lt_one hwone
  have hnu0 : M.nu ≠ 0 :=
    shiftedSquareNu_ne_zero_of_norm hwpos M.C₀_pos M.nu_norm
  obtain ⟨r, hr, x, hx, hmuCoordinates⟩ :=
    exists_positive_content_primitive_shiftedSquareIntegralBasisCoordinates
      b M.mu_ne_zero
  obtain ⟨ell, hell, y, hy, hnuCoordinates⟩ :=
    exists_positive_content_primitive_shiftedSquareIntegralBasisCoordinates
      b hnu0
  have hmuForm :
      (r : ℤ) ^ 2 * |shiftedSquareExplicitNormFormEval t c x| =
        ((shiftedSquareD₀ d * M.C₀ : ℕ) : ℤ) := by
    have h := shiftedSquare_mu_primitive_norm_equation
      b hmuCoordinates M.mu_norm
    rwa [shiftedSquareIntegralBasisNormEval_eq_explicit
      b omega t c hb0 hb1 homega] at h
  have hnuForm :
      (ell : ℤ) ^ 2 * shiftedSquareExplicitNormFormEval t c y =
        ((w * M.C₀ ^ 2 : ℕ) : ℤ) := by
    have h := shiftedSquare_nu_primitive_norm_equation
      b hnuCoordinates M.nu_norm
    rwa [shiftedSquareIntegralBasisNormEval_eq_explicit
      b omega t c hb0 hb1 homega] at h
  have hcoordinate := shiftedSquareIntegralBasis_scaled_coordinate_relation
    b hmuCoordinates hnuCoordinates M.factorization (1 : Fin 2)
  have heval :=
    shiftedSquareIntegralBasisQuadraticLinear_eval_one_eq_surfaceForm
      b omega t c hb0 hb1 homega x y
  have hsurface :
      ((r : ℤ) ^ 2 * (ell : ℤ)) *
          (shiftedSquareSurfaceForm t c y).eval (x 0) (x 1) =
        (M.C₀ : ℤ) ^ 2 * bζ := by
    calc
      ((r : ℤ) ^ 2 * (ell : ℤ)) *
          (shiftedSquareSurfaceForm t c y).eval (x 0) (x 1) =
          ((r : ℤ) ^ 2 * (ell : ℤ)) *
            quadraticLinearFormEval
              (shiftedSquareIntegralBasisQuadraticLinearCoefficients b 1) x y :=
        congrArg (fun z : ℤ => ((r : ℤ) ^ 2 * (ell : ℤ)) * z) heval.symm
      _ = (M.C₀ : ℤ) ^ 2 *
          shiftedSquareIntegralBasisCoordinates b
            (shiftedSquareZetaInteger heq) 1 := hcoordinate
      _ = (M.C₀ : ℤ) ^ 2 * bζ := rfl
  have hellSqDvdZ : (ell : ℤ) ^ 2 ∣
      ((w * M.C₀ ^ 2 : ℕ) : ℤ) :=
    ⟨shiftedSquareExplicitNormFormEval t c y, hnuForm.symm⟩
  have hsurface0 :
      (shiftedSquareSurfaceForm t c y).eval (x 0) (x 1) ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hsurface
    have hC₀ne : (M.C₀ : ℤ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt M.C₀_pos)
    exact (mul_ne_zero (pow_ne_zero 2 hC₀ne) hbζdata.2.1)
      hsurface.symm
  have hellSqDvd : ell ^ 2 ∣ w * M.C₀ ^ 2 := by
    exact_mod_cast hellSqDvdZ
  have hellC₀ : ell ∣ M.C₀ :=
    dvd_of_sq_dvd_squarefree_mul_sq hwpos hw hellSqDvd
  have hnormalized :
      shiftedSquareExplicitNormFormEval t c y =
        ((w * (M.C₀ / ell) ^ 2 : ℕ) : ℤ) := by
    have hmul : ell * (M.C₀ / ell) = M.C₀ := Nat.mul_div_cancel' hellC₀
    have hsq : M.C₀ ^ 2 = ell ^ 2 * (M.C₀ / ell) ^ 2 := by
      calc
        M.C₀ ^ 2 = (ell * (M.C₀ / ell)) ^ 2 := congrArg (· ^ 2) hmul.symm
        _ = ell ^ 2 * (M.C₀ / ell) ^ 2 := by ring
    apply mul_left_cancel₀ (pow_ne_zero 2 (by
      exact_mod_cast (Nat.ne_of_gt hell) : (ell : ℤ) ≠ 0))
    calc
      (ell : ℤ) ^ 2 * shiftedSquareExplicitNormFormEval t c y =
          ((w * M.C₀ ^ 2 : ℕ) : ℤ) := hnuForm
      _ = (ell : ℤ) ^ 2 * ((w * (M.C₀ / ell) ^ 2 : ℕ) : ℤ) := by
        exact_mod_cast (show w * M.C₀ ^ 2 =
            ell ^ 2 * (w * (M.C₀ / ell) ^ 2) by
          rw [hsq]
          ring)
  have hdisc :=
    shiftedSquareSurfacePrimitivePart_discriminant_pos_not_isSquare
      t c y hy ht hell hw hwone M.C₀_pos hellSqDvd hnormalized
  refine ⟨{
    minkowski := M
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
    nu_ne_zero := hnu0
    r := r
    ell := ell
    x := x
    y := y
    r_pos := hr
    ell_pos := hell
    x_primitive := hx
    y_primitive := hy
    mu_coordinates := hmuCoordinates
    nu_coordinates := hnuCoordinates
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
