import Pell.ShiftedSquareSimultaneousNormalizedCoordinates
import Mathlib.Tactic

/-!
# One fixed explicit integral basis for all shifted-square points

The determinant argument for a fixed shift must place every point in one
common integer coordinate space.  The earlier pointwise existence theorem
constructs the same kind of explicit basis inside each existential package,
but its statement does not expose that the basis can be fixed before the
point is chosen.

This module packages one explicit integral basis depending only on the shift
and reconstructs the simultaneous normalized-coordinate package relative to
an arbitrary such fixed basis.  Thus the final corollary chooses the basis
once, independently of `d`, `w`, and `n`.
-/

namespace PellPaper

noncomputable section

local instance shiftedSquareFixedBasisNormalizedCoordinates_numberField (a : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

/-- The point-independent explicit integral-basis data for a fixed shift. -/
structure ShiftedSquareFixedExplicitIntegralBasisData
    (a : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] where
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
  zeta_coordinate :
    ∀ {d w n : ℕ}
        (heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a),
      let bζ : ℤ := shiftedSquareIntegralBasisCoordinates basis
        (shiftedSquareZetaInteger heq) 1
      (bζ = 1 ∨ bζ = 2) ∧ bζ ≠ 0 ∧ |bζ| ≤ 2

/-- The explicit integral-basis theorem supplies point-independent data. -/
theorem nonempty_shiftedSquareFixedExplicitIntegralBasisData
    (a : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (ha : Squarefree a) :
    Nonempty (ShiftedSquareFixedExplicitIntegralBasisData a) := by
  obtain ⟨basis, omega, t, c, hb0, hb1, ht, homega, hzeta⟩ :=
    exists_shiftedSquareExplicitIntegralBasis_package ha
  exact ⟨{
    basis := basis
    omega := omega
    t := t
    c := c
    basis_zero := hb0
    basis_one := hb1
    t_zero_or_one := ht
    omega_sq := homega
    zeta_coordinate := hzeta }⟩

/-- Choose the explicit integral basis once from the shift and its
squarefreeness certificate.  No point variables occur in this definition. -/
noncomputable def shiftedSquareFixedExplicitIntegralBasisData
    (a : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (ha : Squarefree a) : ShiftedSquareFixedExplicitIntegralBasisData a :=
  Classical.choice (nonempty_shiftedSquareFixedExplicitIntegralBasisData a ha)

/-- Relative to any fixed explicit integral-basis datum, every admissible
shifted-square point has a simultaneous normalized-coordinate package whose
basis, generator, and structure constants are literally the prescribed
ones. -/
theorem exists_shiftedSquareSimultaneousNormalizedCoordinatePackage_usingBasis
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (B : ShiftedSquareFixedExplicitIntegralBasisData a)
    (ha : Squarefree a) (hd : 0 < d)
    (hw : Squarefree w) (hwone : 1 < w)
    (heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a) :
    ∃ P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq,
      P.basis = B.basis ∧ P.omega = B.omega ∧ P.t = B.t ∧ P.c = B.c := by
  let bζ : ℤ := shiftedSquareIntegralBasisCoordinates B.basis
    (shiftedSquareZetaInteger heq) 1
  have hbζdata : (bζ = 1 ∨ bζ = 2) ∧ bζ ≠ 0 ∧ |bζ| ≤ 2 := by
    simpa only [bζ] using B.zeta_coordinate heq
  obtain ⟨M⟩ := exists_shiftedSquareMinkowskiEmbeddingC₀Nu_package ha hd heq
  have hwpos : 0 < w := lt_trans Nat.zero_lt_one hwone
  have hnu0 : M.nu ≠ 0 :=
    shiftedSquareNu_ne_zero_of_norm hwpos M.C₀_pos M.nu_norm
  obtain ⟨r, hr, x, hx, hmuCoordinates⟩ :=
    exists_positive_content_primitive_shiftedSquareIntegralBasisCoordinates
      B.basis M.mu_ne_zero
  obtain ⟨ell, hell, y, hy, hnuCoordinates⟩ :=
    exists_positive_content_primitive_shiftedSquareIntegralBasisCoordinates
      B.basis hnu0
  have hmuForm :
      (r : ℤ) ^ 2 * |shiftedSquareExplicitNormFormEval B.t B.c x| =
        ((shiftedSquareD₀ d * M.C₀ : ℕ) : ℤ) := by
    have h := shiftedSquare_mu_primitive_norm_equation
      B.basis hmuCoordinates M.mu_norm
    rwa [shiftedSquareIntegralBasisNormEval_eq_explicit
      B.basis B.omega B.t B.c B.basis_zero B.basis_one B.omega_sq] at h
  have hnuForm :
      (ell : ℤ) ^ 2 * shiftedSquareExplicitNormFormEval B.t B.c y =
        ((w * M.C₀ ^ 2 : ℕ) : ℤ) := by
    have h := shiftedSquare_nu_primitive_norm_equation
      B.basis hnuCoordinates M.nu_norm
    rwa [shiftedSquareIntegralBasisNormEval_eq_explicit
      B.basis B.omega B.t B.c B.basis_zero B.basis_one B.omega_sq] at h
  have hcoordinate := shiftedSquareIntegralBasis_scaled_coordinate_relation
    B.basis hmuCoordinates hnuCoordinates M.factorization (1 : Fin 2)
  have heval :=
    shiftedSquareIntegralBasisQuadraticLinear_eval_one_eq_surfaceForm
      B.basis B.omega B.t B.c B.basis_zero B.basis_one B.omega_sq x y
  have hsurface :
      ((r : ℤ) ^ 2 * (ell : ℤ)) *
          (shiftedSquareSurfaceForm B.t B.c y).eval (x 0) (x 1) =
        (M.C₀ : ℤ) ^ 2 * bζ := by
    calc
      ((r : ℤ) ^ 2 * (ell : ℤ)) *
          (shiftedSquareSurfaceForm B.t B.c y).eval (x 0) (x 1) =
          ((r : ℤ) ^ 2 * (ell : ℤ)) *
            quadraticLinearFormEval
              (shiftedSquareIntegralBasisQuadraticLinearCoefficients
                B.basis 1) x y :=
        congrArg (fun z : ℤ => ((r : ℤ) ^ 2 * (ell : ℤ)) * z) heval.symm
      _ = (M.C₀ : ℤ) ^ 2 *
          shiftedSquareIntegralBasisCoordinates B.basis
            (shiftedSquareZetaInteger heq) 1 := hcoordinate
      _ = (M.C₀ : ℤ) ^ 2 * bζ := rfl
  have hellSqDvdZ : (ell : ℤ) ^ 2 ∣
      ((w * M.C₀ ^ 2 : ℕ) : ℤ) :=
    ⟨shiftedSquareExplicitNormFormEval B.t B.c y, hnuForm.symm⟩
  have hsurface0 :
      (shiftedSquareSurfaceForm B.t B.c y).eval (x 0) (x 1) ≠ 0 := by
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
      shiftedSquareExplicitNormFormEval B.t B.c y =
        ((w * (M.C₀ / ell) ^ 2 : ℕ) : ℤ) := by
    have hmul : ell * (M.C₀ / ell) = M.C₀ := Nat.mul_div_cancel' hellC₀
    have hsq : M.C₀ ^ 2 = ell ^ 2 * (M.C₀ / ell) ^ 2 := by
      calc
        M.C₀ ^ 2 = (ell * (M.C₀ / ell)) ^ 2 := congrArg (· ^ 2) hmul.symm
        _ = ell ^ 2 * (M.C₀ / ell) ^ 2 := by ring
    apply mul_left_cancel₀ (pow_ne_zero 2 (by
      exact_mod_cast (Nat.ne_of_gt hell) : (ell : ℤ) ≠ 0))
    calc
      (ell : ℤ) ^ 2 * shiftedSquareExplicitNormFormEval B.t B.c y =
          ((w * M.C₀ ^ 2 : ℕ) : ℤ) := hnuForm
      _ = (ell : ℤ) ^ 2 * ((w * (M.C₀ / ell) ^ 2 : ℕ) : ℤ) := by
        exact_mod_cast (show w * M.C₀ ^ 2 =
            ell ^ 2 * (w * (M.C₀ / ell) ^ 2) by
          rw [hsq]
          ring)
  have hdisc :=
    shiftedSquareSurfacePrimitivePart_discriminant_pos_not_isSquare
      B.t B.c y hy B.t_zero_or_one hell hw hwone M.C₀_pos hellSqDvd
        hnormalized
  let P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq := {
    minkowski := M
    basis := B.basis
    omega := B.omega
    t := B.t
    c := B.c
    basis_zero := B.basis_zero
    basis_one := B.basis_one
    t_zero_or_one := B.t_zero_or_one
    omega_sq := B.omega_sq
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
    surface_content_pos := shiftedSquareSurfaceForm_content_pos B.t B.c y hy
    surface_content_dvd_two :=
      shiftedSquareSurfaceForm_content_dvd_two B.t B.c y hy
    primitive_surface := hdisc.1
    primitive_surface_discriminant_pos := hdisc.2.2.1
    primitive_surface_discriminant_not_isSquare := hdisc.2.2.2.1
    primitive_surface_discriminant_scale := hdisc.2.2.2.2 }
  refine ⟨P, ?_⟩
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Choosing the basis datum once gives a point-independent coordinate frame:
all admissible triples for the fixed shift can be represented in this same
literal basis with the same generator and structure constants. -/
theorem exists_shiftedSquareSimultaneousNormalizedCoordinatePackage_fixedBasis
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (ha : Squarefree a) (hd : 0 < d)
    (hw : Squarefree w) (hwone : 1 < w)
    (heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a) :
    let B := shiftedSquareFixedExplicitIntegralBasisData a ha
    ∃ P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq,
      P.basis = B.basis ∧ P.omega = B.omega ∧ P.t = B.t ∧ P.c = B.c := by
  let B := shiftedSquareFixedExplicitIntegralBasisData a ha
  exact exists_shiftedSquareSimultaneousNormalizedCoordinatePackage_usingBasis
    B ha hd hw hwone heq

end

end PellPaper
