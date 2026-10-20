import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.NumberTheory.Zsqrtd.Basic

/-!
# The standard quadratic order inside a rational quadratic algebra

For every integer `d`, this file maps the concrete order `ℤ√d` into the
two-dimensional rational quadratic algebra with distinguished element
`ω` satisfying `ω^2 = d`.  The map is the direct coordinatewise inclusion
of integer coefficients into rational coefficients, constructed through the
universal property `Zsqrtd.lift`.

This is an algebraic bridge only.  It does not identify `ℤ√d` with the full
ring of integers of a quadratic field, and makes no assertion about maximal
orders, fundamental units, class numbers, or moments.
-/

namespace PellPaper

/-- The concrete rational quadratic algebra used for the polynomial
`X^2 - d`.  It is deliberately an algebra, rather than a field: no
nonsquareness assumption is needed for the construction below. -/
abbrev rationalQuadraticAlgebra (d : ℤ) : Type :=
  QuadraticAlgebra ℚ (d : ℚ) 0

/-- The canonical root in `rationalQuadraticAlgebra d` squares to the image
of the integer `d`. -/
theorem rationalQuadraticAlgebra_omega_sq (d : ℤ) :
    (QuadraticAlgebra.omega : rationalQuadraticAlgebra d) * QuadraticAlgebra.omega =
      (d : rationalQuadraticAlgebra d) := by
  simpa using
    (QuadraticAlgebra.omega_mul_omega_eq_algebraMap (R := ℚ) (a := (d : ℚ)) (b := 0))

/-- The coefficientwise map from the standard quadratic order `ℤ√d` into
the rational quadratic algebra. -/
def quadraticOrderPellEmbedding (d : ℤ) :
    ℤ√d →+* rationalQuadraticAlgebra d :=
  Zsqrtd.lift ⟨QuadraticAlgebra.omega, rationalQuadraticAlgebra_omega_sq d⟩

/-- The quadratic generator is sent to the canonical rational-algebra root. -/
@[simp]
theorem quadraticOrderPellEmbedding_sqrtd (d : ℤ) :
    quadraticOrderPellEmbedding d Zsqrtd.sqrtd = QuadraticAlgebra.omega := by
  simp [quadraticOrderPellEmbedding]

/-- The image of an element of `ℤ√d` has its two integer coordinates cast
to rationals. -/
theorem quadraticOrderPellEmbedding_coordinates (d : ℤ) (z : ℤ√d) :
    quadraticOrderPellEmbedding d z =
      ⟨(z.re : ℚ), (z.im : ℚ)⟩ := by
  ext <;> simp [quadraticOrderPellEmbedding, Zsqrtd.lift]

/-- The concrete coefficientwise quadratic-order map is injective for every
integer `d`, including square and zero values. -/
theorem quadraticOrderPellEmbedding_injective (d : ℤ) :
    Function.Injective (quadraticOrderPellEmbedding d) := by
  intro x y hxy
  apply Zsqrtd.ext
  · have hre := congrArg QuadraticAlgebra.re hxy
    simp [quadraticOrderPellEmbedding_coordinates] at hre
    exact_mod_cast hre
  · have him := congrArg QuadraticAlgebra.im hxy
    simp [quadraticOrderPellEmbedding_coordinates] at him
    exact_mod_cast him

/-- The defining Pell relation holds after applying the quadratic-order
embedding. -/
theorem quadraticOrderPellEmbedding_sqrtd_mul_sqrtd (d : ℤ) :
    quadraticOrderPellEmbedding d Zsqrtd.sqrtd *
        quadraticOrderPellEmbedding d Zsqrtd.sqrtd =
      (d : rationalQuadraticAlgebra d) := by
  rw [quadraticOrderPellEmbedding_sqrtd]
  exact rationalQuadraticAlgebra_omega_sq d

/-- Natural-number version of `quadraticOrderPellEmbedding`. -/
def quadraticOrderPellEmbeddingNat (d : ℕ) :
    ℤ√(d : ℤ) →+* QuadraticAlgebra ℚ (d : ℚ) 0 :=
  quadraticOrderPellEmbedding (d : ℤ)

/-- The natural-number version sends its quadratic generator to `ω`. -/
@[simp]
theorem quadraticOrderPellEmbeddingNat_sqrtd (d : ℕ) :
    quadraticOrderPellEmbeddingNat d Zsqrtd.sqrtd = QuadraticAlgebra.omega := by
  change quadraticOrderPellEmbedding (d : ℤ) Zsqrtd.sqrtd =
    (QuadraticAlgebra.omega : rationalQuadraticAlgebra (d : ℤ))
  exact quadraticOrderPellEmbedding_sqrtd (d : ℤ)

/-- The natural-number version preserves the defining quadratic relation. -/
theorem quadraticOrderPellEmbeddingNat_sqrtd_mul_sqrtd (d : ℕ) :
    quadraticOrderPellEmbeddingNat d Zsqrtd.sqrtd *
        quadraticOrderPellEmbeddingNat d Zsqrtd.sqrtd =
      (d : QuadraticAlgebra ℚ (d : ℚ) 0) := by
  change quadraticOrderPellEmbedding (d : ℤ) Zsqrtd.sqrtd *
      quadraticOrderPellEmbedding (d : ℤ) Zsqrtd.sqrtd =
      ((d : ℤ) : rationalQuadraticAlgebra (d : ℤ))
  exact quadraticOrderPellEmbedding_sqrtd_mul_sqrtd (d : ℤ)

/-- The natural-number version is injective. -/
theorem quadraticOrderPellEmbeddingNat_injective (d : ℕ) :
    Function.Injective (quadraticOrderPellEmbeddingNat d) := by
  simpa [quadraticOrderPellEmbeddingNat] using
    quadraticOrderPellEmbedding_injective (d : ℤ)

end PellPaper
