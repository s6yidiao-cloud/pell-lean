import Pell.ShiftedSquareMinkowskiC0Nu
import Pell.BinaryQuadraticLinearEliminant
import Pell.QuadraticIdealNormalizedNormForm
import Mathlib.Tactic

/-!
# Primitive integral-basis coordinates for the shifted-square Minkowski package

This file chooses an actual rank-two integer basis of the quadratic field's
ring of integers, removes the coordinate contents of the nonzero elements
`mu` and `nu`, and expresses multiplication in that basis by the existing
six-coefficient bidegree-`(2,1)` interface `quadraticLinearFormEval`.

The selected integral basis is deliberately abstract.  Consequently this
slice proves exact integral polynomial identities, but does not yet bound the
basis structure constants or the selected coordinate of `zeta`.
-/

namespace PellPaper

noncomputable section

local instance shiftedSquareMinkowskiCoordinates_numberField (a : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

/-- A fixed actual rank-two integer basis of the ring of integers of the
shifted-square quadratic field. -/
noncomputable def shiftedSquareRingOfIntegersBasis (a : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    Module.Basis (Fin 2) ℤ
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))) := by
  apply Module.finBasisOfFinrankEq ℤ
    (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a)))
  rw [NumberField.RingOfIntegers.rank]
  exact QuadraticAlgebra.finrank_eq_two ((-a : ℤ) : ℚ) 0

/-- The two integer coordinates of a ring-of-integers element in a specified
actual integer basis. -/
def shiftedSquareIntegralBasisCoordinates
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (b : Module.Basis (Fin 2) ℤ
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))))
    (z : NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))) :
    Fin 2 → ℤ :=
  fun i => b.repr z i

/-- Reconstruct a ring-of-integers element from a pair of integer
coordinates in the specified basis. -/
def shiftedSquareIntegralBasisElement
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (b : Module.Basis (Fin 2) ℤ
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))))
    (x : Fin 2 → ℤ) :
    NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a)) :=
  b.equivFun.symm x

@[simp]
theorem shiftedSquareIntegralBasisCoordinates_element
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (b : Module.Basis (Fin 2) ℤ
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))))
    (x : Fin 2 → ℤ) :
    shiftedSquareIntegralBasisCoordinates b
        (shiftedSquareIntegralBasisElement b x) = x := by
  funext i
  change b.repr (b.equivFun.symm x) i = x i
  rw [← b.equivFun_apply]
  exact congrFun (b.equivFun.apply_symm_apply x) i

@[simp]
theorem shiftedSquareIntegralBasisElement_coordinates
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (b : Module.Basis (Fin 2) ℤ
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))))
    (z : NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))) :
    shiftedSquareIntegralBasisElement b
        (shiftedSquareIntegralBasisCoordinates b z) = z := by
  apply b.repr.injective
  ext i
  have h := congrFun
    (shiftedSquareIntegralBasisCoordinates_element b
      (shiftedSquareIntegralBasisCoordinates b z)) i
  simpa only [shiftedSquareIntegralBasisCoordinates] using h

/-- The inverse coordinate map is the displayed two-term integer linear
combination. -/
theorem shiftedSquareIntegralBasisElement_eq
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (b : Module.Basis (Fin 2) ℤ
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))))
    (x : Fin 2 → ℤ) :
    shiftedSquareIntegralBasisElement b x = x 0 • b 0 + x 1 • b 1 := by
  have hcoordinates := shiftedSquareIntegralBasisCoordinates_element b x
  calc
    shiftedSquareIntegralBasisElement b x =
        ∑ i, b.repr (shiftedSquareIntegralBasisElement b x) i • b i :=
      (b.sum_repr (shiftedSquareIntegralBasisElement b x)).symm
    _ = x 0 • b 0 + x 1 • b 1 := by
      rw [Fin.sum_univ_two]
      change
        shiftedSquareIntegralBasisCoordinates b
              (shiftedSquareIntegralBasisElement b x) 0 • b 0 +
            shiftedSquareIntegralBasisCoordinates b
              (shiftedSquareIntegralBasisElement b x) 1 • b 1 = _
      rw [hcoordinates]

/-- Every nonzero ring-of-integers element is a positive natural content
times an element with a primitive integer coordinate pair. -/
theorem exists_positive_content_primitive_shiftedSquareIntegralBasisCoordinates
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (b : Module.Basis (Fin 2) ℤ
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))))
    {z : NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))}
    (hz : z ≠ 0) :
    ∃ r : ℕ, 0 < r ∧ ∃ x : Fin 2 → ℤ,
      IsCoprime (x 0) (x 1) ∧
      z = (r : ℤ) • shiftedSquareIntegralBasisElement b x := by
  let u := shiftedSquareIntegralBasisCoordinates b z
  have hgpos : 0 < Int.gcd (u 0) (u 1) := by
    apply Nat.pos_of_ne_zero
    intro hgzero
    obtain ⟨hu0, hu1⟩ := Int.gcd_eq_zero_iff.mp hgzero
    apply hz
    have hu : u = 0 := by
      funext i
      fin_cases i
      · exact hu0
      · exact hu1
    calc
      z = shiftedSquareIntegralBasisElement b
          (shiftedSquareIntegralBasisCoordinates b z) :=
        (shiftedSquareIntegralBasisElement_coordinates b z).symm
      _ = shiftedSquareIntegralBasisElement b u := by rfl
      _ = shiftedSquareIntegralBasisElement b 0 :=
        congrArg (shiftedSquareIntegralBasisElement b) hu
      _ = 0 := b.equivFun.symm.map_zero
  obtain ⟨x0, x1, hcop, hu0, hu1⟩ := Int.exists_gcd_one hgpos
  let x : Fin 2 → ℤ := ![x0, x1]
  have hcoordinates : u =
      (Int.gcd (u 0) (u 1) : ℤ) • x := by
    funext i
    fin_cases i
    · change u 0 = (Int.gcd (u 0) (u 1) : ℤ) * x0
      calc
        u 0 = x0 * (Int.gcd (u 0) (u 1) : ℤ) := hu0
        _ = (Int.gcd (u 0) (u 1) : ℤ) * x0 := by ring
    · change u 1 = (Int.gcd (u 0) (u 1) : ℤ) * x1
      calc
        u 1 = x1 * (Int.gcd (u 0) (u 1) : ℤ) := hu1
        _ = (Int.gcd (u 0) (u 1) : ℤ) * x1 := by ring
  have helement : z = (Int.gcd (u 0) (u 1) : ℤ) •
      shiftedSquareIntegralBasisElement b x := by
    calc
      z = shiftedSquareIntegralBasisElement b u := by
        change z = shiftedSquareIntegralBasisElement b
          (shiftedSquareIntegralBasisCoordinates b z)
        exact (shiftedSquareIntegralBasisElement_coordinates b z).symm
      _ = shiftedSquareIntegralBasisElement b
          ((Int.gcd (u 0) (u 1) : ℤ) • x) :=
        congrArg (shiftedSquareIntegralBasisElement b) hcoordinates
      _ = (Int.gcd (u 0) (u 1) : ℤ) •
          shiftedSquareIntegralBasisElement b x :=
        b.equivFun.symm.map_smul
          (Int.gcd (u 0) (u 1) : ℤ) x
  exact ⟨Int.gcd (u 0) (u 1), hgpos, x,
    Int.isCoprime_iff_gcd_eq_one.mpr hcop, helement⟩

/-- The explicit integral quadratic norm polynomial attached to an actual
integer basis. -/
def shiftedSquareIntegralBasisNormEval
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (b : Module.Basis (Fin 2) ℤ
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))))
    (x : Fin 2 → ℤ) : ℤ :=
  Algebra.norm ℤ (b 0) * x 0 ^ 2 +
    (Algebra.norm ℤ (b 0 + b 1) -
      Algebra.norm ℤ (b 0) - Algebra.norm ℤ (b 1)) * x 0 * x 1 +
    Algebra.norm ℤ (b 1) * x 1 ^ 2

theorem shiftedSquareIntegralBasisNormEval_eq_algebraNorm
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (b : Module.Basis (Fin 2) ℤ
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))))
    (x : Fin 2 → ℤ) :
    shiftedSquareIntegralBasisNormEval b x =
      Algebra.norm ℤ (shiftedSquareIntegralBasisElement b x) := by
  symm
  simpa only [shiftedSquareIntegralBasisElement_eq, zsmul_eq_mul,
    shiftedSquareIntegralBasisNormEval, mul_comm] using
    (IntegralBinaryQuadraticForm.algebraNorm_integer_linearCombination
      (-a) (b 0) (b 1) (x 0) (x 1))

/-- The six structure constants for one output coordinate of
`alpha^2 * gamma` in an actual integral basis.  The first index is the
exponent of the second `alpha` coordinate, exactly as in
`quadraticLinearFormEval`; the middle coefficient contains the symmetric
factor two. -/
def shiftedSquareIntegralBasisQuadraticLinearCoefficients
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (b : Module.Basis (Fin 2) ℤ
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))))
    (k : Fin 2) : Fin 3 → Fin 2 → ℤ :=
  ![
    fun t => shiftedSquareIntegralBasisCoordinates b (b 0 * b 0 * b t) k,
    fun t => 2 * shiftedSquareIntegralBasisCoordinates b (b 0 * b 1 * b t) k,
    fun t => shiftedSquareIntegralBasisCoordinates b (b 1 * b 1 * b t) k]

/-- Coordinatewise multiplication is literally the existing integral
bidegree-`(2,1)` polynomial evaluation. -/
theorem shiftedSquareIntegralBasis_sq_mul_coordinate
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (b : Module.Basis (Fin 2) ℤ
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))))
    (x y : Fin 2 → ℤ) (k : Fin 2) :
    shiftedSquareIntegralBasisCoordinates b
        ((shiftedSquareIntegralBasisElement b x) ^ 2 *
          shiftedSquareIntegralBasisElement b y) k =
      quadraticLinearFormEval
        (shiftedSquareIntegralBasisQuadraticLinearCoefficients b k) x y := by
  let O := NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))
  have hexpand :
      (shiftedSquareIntegralBasisElement b x) ^ 2 *
          shiftedSquareIntegralBasisElement b y =
        (x 0 ^ 2 * y 0) • (b 0 * b 0 * b 0) +
        (x 0 ^ 2 * y 1) • (b 0 * b 0 * b 1) +
        (2 * x 0 * x 1 * y 0) • (b 0 * b 1 * b 0) +
        (2 * x 0 * x 1 * y 1) • (b 0 * b 1 * b 1) +
        (x 1 ^ 2 * y 0) • (b 1 * b 1 * b 0) +
        (x 1 ^ 2 * y 1) • (b 1 * b 1 * b 1) := by
    rw [shiftedSquareIntegralBasisElement_eq,
      shiftedSquareIntegralBasisElement_eq]
    simp only [zsmul_eq_mul]
    change _ = (_ : O)
    push_cast
    ring
  rw [hexpand]
  simp only [shiftedSquareIntegralBasisCoordinates, map_add, map_zsmul,
    Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  simp [shiftedSquareIntegralBasisCoordinates, quadraticLinearFormEval,
    shiftedSquareIntegralBasisQuadraticLinearCoefficients,
    Fin.sum_univ_succ]
  ring

@[simp]
theorem shiftedSquareIntegralBasisCoordinates_zsmul
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (b : Module.Basis (Fin 2) ℤ
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))))
    (m : ℤ)
    (z : NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a)))
    (k : Fin 2) :
    shiftedSquareIntegralBasisCoordinates b (m • z) k =
      m * shiftedSquareIntegralBasisCoordinates b z k := by
  change b.repr (m • z) k = m * b.repr z k
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]

/-- After removing the two coordinate contents, the exact factorization
becomes two integral bidegree-`(2,1)` coordinate equations. -/
theorem shiftedSquareIntegralBasis_scaled_coordinate_relation
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (b : Module.Basis (Fin 2) ℤ
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))))
    {mu nu zeta :
      NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))}
    {C₀ r ell : ℕ} {x y : Fin 2 → ℤ}
    (hmu : mu = (r : ℤ) • shiftedSquareIntegralBasisElement b x)
    (hnu : nu = (ell : ℤ) • shiftedSquareIntegralBasisElement b y)
    (hfactor : mu ^ 2 * nu =
      (C₀ : NumberField.RingOfIntegers
        (rationalQuadraticAlgebra (-a))) ^ 2 * zeta)
    (k : Fin 2) :
    ((r : ℤ) ^ 2 * (ell : ℤ)) *
        quadraticLinearFormEval
          (shiftedSquareIntegralBasisQuadraticLinearCoefficients b k) x y =
      (C₀ : ℤ) ^ 2 * shiftedSquareIntegralBasisCoordinates b zeta k := by
  have hscaled :
      ((r : ℤ) ^ 2 * (ell : ℤ)) •
          ((shiftedSquareIntegralBasisElement b x) ^ 2 *
            shiftedSquareIntegralBasisElement b y) =
        ((C₀ : ℤ) ^ 2) • zeta := by
    calc
      ((r : ℤ) ^ 2 * (ell : ℤ)) •
            ((shiftedSquareIntegralBasisElement b x) ^ 2 *
              shiftedSquareIntegralBasisElement b y) =
          (((r : ℤ) • shiftedSquareIntegralBasisElement b x) ^ 2 *
            ((ell : ℤ) • shiftedSquareIntegralBasisElement b y)) := by
              simp only [zsmul_eq_mul]
              push_cast
              ring
      _ = mu ^ 2 * nu := by rw [← hmu, ← hnu]
      _ = (C₀ : NumberField.RingOfIntegers
            (rationalQuadraticAlgebra (-a))) ^ 2 * zeta := hfactor
      _ = ((C₀ : ℤ) ^ 2) • zeta := by
        simp only [zsmul_eq_mul]
        push_cast
        rfl
  have hcoordinate := congrArg
    (fun q => shiftedSquareIntegralBasisCoordinates b q k) hscaled
  simpa only [shiftedSquareIntegralBasisCoordinates_zsmul,
    shiftedSquareIntegralBasis_sq_mul_coordinate] using hcoordinate

/-- A positive shifted-square norm makes the distinguished integral element
nonzero.  This is the nonvanishing input needed before removing its content. -/
theorem shiftedSquareZetaInteger_ne_zero_of_pos
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (hd : 0 < d) (hw : 0 < w)
    (heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a) :
    shiftedSquareZetaInteger heq ≠ 0 := by
  intro hzeta
  have hnorm := shiftedSquareZetaInteger_algebraNorm heq
  rw [hzeta, Algebra.norm_zero] at hnorm
  have hpositive :
      (0 : ℤ) < (((shiftedSquareD₀ d) ^ 2 * w : ℕ) : ℤ) := by
    exact_mod_cast Nat.mul_pos (pow_pos (shiftedSquareD₀_pos hd) 2) hw
  omega

/-- The positive norm supplied by the C₀--`nu` package proves `nu ≠ 0`
before its coordinate content is removed. -/
theorem shiftedSquareNu_ne_zero_of_norm
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {w C₀ : ℕ}
    {nu : NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))}
    (hw : 0 < w) (hC₀ : 0 < C₀)
    (hnorm : Algebra.norm ℤ nu = ((w * C₀ ^ 2 : ℕ) : ℤ)) :
    nu ≠ 0 := by
  intro hnu
  rw [hnu, Algebra.norm_zero] at hnorm
  have hpositive : (0 : ℤ) < ((w * C₀ ^ 2 : ℕ) : ℤ) := by
    exact_mod_cast Nat.mul_pos hw (pow_pos hC₀ 2)
  omega

/-- Integer content scales the quadratic norm polynomial by its square. -/
theorem shiftedSquareIntegralBasisNormEval_content
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (b : Module.Basis (Fin 2) ℤ
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))))
    (r : ℕ) (x : Fin 2 → ℤ) :
    Algebra.norm ℤ
        ((r : ℤ) • shiftedSquareIntegralBasisElement b x) =
      (r : ℤ) ^ 2 * shiftedSquareIntegralBasisNormEval b x := by
  have hrank : Module.finrank ℤ
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))) = 2 := by
    rw [NumberField.RingOfIntegers.rank]
    exact QuadraticAlgebra.finrank_eq_two ((-a : ℤ) : ℚ) 0
  rw [zsmul_eq_mul, Int.cast_natCast, map_mul, Algebra.norm_natCast, hrank,
    ← shiftedSquareIntegralBasisNormEval_eq_algebraNorm]

/-- Pull an absolute rational norm identity back to the exact absolute
integer norm identity for a ring-of-integers element. -/
theorem shiftedSquare_integerNorm_abs_of_rationalNorm_abs
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {z : NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))}
    {M : ℕ}
    (hnorm :
      |Algebra.norm ℚ (z : rationalQuadraticAlgebra (-a))| = (M : ℚ)) :
    |Algebra.norm ℤ z| = (M : ℤ) := by
  have hnormCast :
      ((Algebra.norm ℤ z : ℤ) : ℚ) =
        Algebra.norm ℚ (z : rationalQuadraticAlgebra (-a)) := by
    rw [← Algebra.intNorm_eq_norm ℤ
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a)))]
    exact Algebra.algebraMap_intNorm
      (A := ℤ) (K := ℚ) (L := rationalQuadraticAlgebra (-a))
      (B := NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))) z
  apply (Int.cast_injective (α := ℚ))
  simpa only [Int.cast_abs, Int.cast_natCast, hnormCast] using hnorm

/-- Content removal turns the absolute norm of `mu` into an exact quadratic
form equation for its primitive coordinate pair. -/
theorem shiftedSquare_mu_primitive_norm_equation
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (b : Module.Basis (Fin 2) ℤ
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))))
    {mu : NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))}
    {r M : ℕ} {x : Fin 2 → ℤ}
    (hmu : mu = (r : ℤ) • shiftedSquareIntegralBasisElement b x)
    (hnorm :
      |Algebra.norm ℚ (mu : rationalQuadraticAlgebra (-a))| = (M : ℚ)) :
    (r : ℤ) ^ 2 * |shiftedSquareIntegralBasisNormEval b x| = (M : ℤ) := by
  have hnormZ := shiftedSquare_integerNorm_abs_of_rationalNorm_abs hnorm
  rw [hmu, shiftedSquareIntegralBasisNormEval_content, abs_mul,
    abs_of_nonneg (sq_nonneg (r : ℤ))] at hnormZ
  exact hnormZ

/-- Content removal turns the signed norm of `nu` into an exact quadratic
form equation for its primitive coordinate pair. -/
theorem shiftedSquare_nu_primitive_norm_equation
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (b : Module.Basis (Fin 2) ℤ
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))))
    {nu : NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))}
    {ell M : ℕ} {y : Fin 2 → ℤ}
    (hnu : nu = (ell : ℤ) • shiftedSquareIntegralBasisElement b y)
    (hnorm : Algebra.norm ℤ nu = (M : ℤ)) :
    (ell : ℤ) ^ 2 * shiftedSquareIntegralBasisNormEval b y = (M : ℤ) := by
  calc
    (ell : ℤ) ^ 2 * shiftedSquareIntegralBasisNormEval b y =
        Algebra.norm ℤ
          ((ell : ℤ) • shiftedSquareIntegralBasisElement b y) :=
      (shiftedSquareIntegralBasisNormEval_content b ell y).symm
    _ = Algebra.norm ℤ nu := by rw [← hnu]
    _ = (M : ℤ) := hnorm

/-- A nonzero integral element has a nonzero coordinate in every actual
integral basis. -/
theorem exists_ne_zero_shiftedSquareIntegralBasisCoordinate
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (b : Module.Basis (Fin 2) ℤ
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))))
    {z : NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))}
    (hz : z ≠ 0) :
    ∃ k : Fin 2, shiftedSquareIntegralBasisCoordinates b z k ≠ 0 := by
  by_contra h
  push Not at h
  apply hz
  have hcoordinates : shiftedSquareIntegralBasisCoordinates b z = 0 := by
    funext k
    exact h k
  calc
    z = shiftedSquareIntegralBasisElement b
          (shiftedSquareIntegralBasisCoordinates b z) :=
      (shiftedSquareIntegralBasisElement_coordinates b z).symm
    _ = shiftedSquareIntegralBasisElement b 0 := by rw [hcoordinates]
    _ = 0 := b.equivFun.symm.map_zero

/-- The complete basis-independent coordinate package extracted from the
exact shifted-square Minkowski factorization.  Its two primitive coordinate
pairs satisfy exact quadratic norm equations and an exact pair of
bidegree-`(2,1)` equations.  One of those equations has a certified nonzero
integral level. -/
structure ShiftedSquareMinkowskiPrimitiveCoordinatePackage
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a) where
  basis : Module.Basis (Fin 2) ℤ
    (NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a)))
  mu : NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))
  C₀ : ℕ
  nu : NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))
  r : ℕ
  ell : ℕ
  x : Fin 2 → ℤ
  y : Fin 2 → ℤ
  selectedCoordinate : Fin 2
  level : ℤ
  mu_mem : mu ∈ shiftedSquareIdealDivisor heq
  mu_ne_zero : mu ≠ 0
  nu_ne_zero : nu ≠ 0
  C₀_pos : 0 < C₀
  r_pos : 0 < r
  ell_pos : 0 < ell
  x_primitive : IsCoprime (x 0) (x 1)
  y_primitive : IsCoprime (y 0) (y 1)
  mu_coordinates :
    mu = (r : ℤ) • shiftedSquareIntegralBasisElement basis x
  nu_coordinates :
    nu = (ell : ℤ) • shiftedSquareIntegralBasisElement basis y
  mu_norm :
    |Algebra.norm ℚ (mu : rationalQuadraticAlgebra (-a))| =
      ((shiftedSquareD₀ d * C₀ : ℕ) : ℚ)
  nu_norm : Algebra.norm ℤ nu = ((w * C₀ ^ 2 : ℕ) : ℤ)
  factorization :
    mu ^ 2 * nu =
      (C₀ : NumberField.RingOfIntegers
        (rationalQuadraticAlgebra (-a))) ^ 2 *
        shiftedSquareZetaInteger heq
  C₀_le_sqrt_discr :
    (C₀ : ℝ) ≤
      Real.sqrt |NumberField.discr (rationalQuadraticAlgebra (-a))|
  mu_primitive_norm :
    (r : ℤ) ^ 2 * |shiftedSquareIntegralBasisNormEval basis x| =
      ((shiftedSquareD₀ d * C₀ : ℕ) : ℤ)
  nu_primitive_norm :
    (ell : ℤ) ^ 2 * shiftedSquareIntegralBasisNormEval basis y =
      ((w * C₀ ^ 2 : ℕ) : ℤ)
  coordinate_relation : ∀ k : Fin 2,
    ((r : ℤ) ^ 2 * (ell : ℤ)) *
        quadraticLinearFormEval
          (shiftedSquareIntegralBasisQuadraticLinearCoefficients basis k) x y =
      (C₀ : ℤ) ^ 2 *
        shiftedSquareIntegralBasisCoordinates basis
          (shiftedSquareZetaInteger heq) k
  selected_zeta_coordinate_ne_zero :
    shiftedSquareIntegralBasisCoordinates basis
      (shiftedSquareZetaInteger heq) selectedCoordinate ≠ 0
  level_eq :
    level = quadraticLinearFormEval
      (shiftedSquareIntegralBasisQuadraticLinearCoefficients
        basis selectedCoordinate) x y
  level_ne_zero : level ≠ 0
  selected_coordinate_relation :
    ((r : ℤ) ^ 2 * (ell : ℤ)) * level =
      (C₀ : ℤ) ^ 2 *
        shiftedSquareIntegralBasisCoordinates basis
          (shiftedSquareZetaInteger heq) selectedCoordinate
  content_dvd_selected_zeta_level :
    ((r : ℤ) ^ 2 * (ell : ℤ)) ∣
      (C₀ : ℤ) ^ 2 *
        shiftedSquareIntegralBasisCoordinates basis
          (shiftedSquareZetaInteger heq) selectedCoordinate

/-- Extract primitive integral coordinates, their exact norm equations, and
the explicit nonzero bidegree-`(2,1)` level from the canonical C₀--`nu`
Minkowski package. -/
theorem exists_shiftedSquareMinkowskiPrimitiveCoordinatePackage
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (ha : Squarefree a) (hd : 0 < d) (hw : 0 < w)
    (heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a) :
    Nonempty (ShiftedSquareMinkowskiPrimitiveCoordinatePackage heq) := by
  obtain ⟨mu, C₀, nu, _, hmu, hmu0, hC₀, hmuNorm, hfactor,
      hnuNorm, hC₀bound, _, _, _⟩ :=
    exists_shiftedSquareMinkowskiC₀Nu_package ha hd heq
  have hnu0 : nu ≠ 0 :=
    shiftedSquareNu_ne_zero_of_norm hw hC₀ hnuNorm
  let b := shiftedSquareRingOfIntegersBasis a
  obtain ⟨r, hr, x, hx, hmuCoordinates⟩ :=
    exists_positive_content_primitive_shiftedSquareIntegralBasisCoordinates
      b hmu0
  obtain ⟨ell, hell, y, hy, hnuCoordinates⟩ :=
    exists_positive_content_primitive_shiftedSquareIntegralBasisCoordinates
      b hnu0
  have hcoordinate : ∀ k : Fin 2,
      ((r : ℤ) ^ 2 * (ell : ℤ)) *
          quadraticLinearFormEval
            (shiftedSquareIntegralBasisQuadraticLinearCoefficients b k) x y =
        (C₀ : ℤ) ^ 2 *
          shiftedSquareIntegralBasisCoordinates b
            (shiftedSquareZetaInteger heq) k :=
    fun k => shiftedSquareIntegralBasis_scaled_coordinate_relation
      b hmuCoordinates hnuCoordinates hfactor k
  have hzeta0 : shiftedSquareZetaInteger heq ≠ 0 :=
    shiftedSquareZetaInteger_ne_zero_of_pos hd hw heq
  obtain ⟨k, hk⟩ :=
    exists_ne_zero_shiftedSquareIntegralBasisCoordinate b hzeta0
  let c := quadraticLinearFormEval
    (shiftedSquareIntegralBasisQuadraticLinearCoefficients b k) x y
  have hselected :
      ((r : ℤ) ^ 2 * (ell : ℤ)) * c =
        (C₀ : ℤ) ^ 2 *
          shiftedSquareIntegralBasisCoordinates b
            (shiftedSquareZetaInteger heq) k := hcoordinate k
  have hc0 : c ≠ 0 := by
    intro hc
    rw [hc, mul_zero] at hselected
    have hC₀ne : (C₀ : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hC₀)
    exact (mul_ne_zero (pow_ne_zero 2 hC₀ne) hk) hselected.symm
  refine ⟨{
    basis := b
    mu := mu
    C₀ := C₀
    nu := nu
    r := r
    ell := ell
    x := x
    y := y
    selectedCoordinate := k
    level := c
    mu_mem := hmu
    mu_ne_zero := hmu0
    nu_ne_zero := hnu0
    C₀_pos := hC₀
    r_pos := hr
    ell_pos := hell
    x_primitive := hx
    y_primitive := hy
    mu_coordinates := hmuCoordinates
    nu_coordinates := hnuCoordinates
    mu_norm := hmuNorm
    nu_norm := hnuNorm
    factorization := hfactor
    C₀_le_sqrt_discr := hC₀bound
    mu_primitive_norm :=
      shiftedSquare_mu_primitive_norm_equation b hmuCoordinates hmuNorm
    nu_primitive_norm :=
      shiftedSquare_nu_primitive_norm_equation b hnuCoordinates hnuNorm
    coordinate_relation := hcoordinate
    selected_zeta_coordinate_ne_zero := hk
    level_eq := rfl
    level_ne_zero := hc0
    selected_coordinate_relation := hselected
    content_dvd_selected_zeta_level := ⟨c, hselected.symm⟩ }⟩

end


end PellPaper
