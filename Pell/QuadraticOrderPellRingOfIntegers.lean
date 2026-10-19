import Pell.QuadraticOrderPellEmbedding
import Pell.FundamentalDiscriminantPellBridge
import Mathlib.NumberTheory.NumberField.Basic

/-!
# The standard quadratic order inside a quadratic field's ring of integers

Under Mathlib's explicit no-rational-root condition for `X^2 - d`, the
rational quadratic algebra is a field.  This module restricts the concrete
embedding from `QuadraticOrderPellEmbedding` to an injective map
`ℤ√d →+* NumberField.RingOfIntegers (rationalQuadraticAlgebra d)`.

It proves an inclusion into the integral closure only.  In particular, it
does not identify `ℤ√d` with the full ring of integers, calculate an
order-index, compare fundamental units, or prove a class-number formula.
-/

namespace PellPaper

/-- The no-rational-root condition needed by Mathlib's `QuadraticAlgebra`
field instance, written in the exact form of its defining relation. -/
abbrev rationalQuadraticAlgebraNoRationalRoot (d : ℤ) : Prop :=
  ∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + (0 : ℚ) * r

/-- An integer which is not an integer square cannot acquire a rational
square root.  This supplies the no-rational-root condition required by the
quadratic-algebra field instance. -/
theorem rationalQuadraticAlgebraNoRationalRoot_of_not_isSquare (d : ℤ)
    (hd : ¬ IsSquare d) : rationalQuadraticAlgebraNoRationalRoot d := by
  intro r hr
  apply hd
  rw [← Rat.isSquare_intCast_iff]
  exact ⟨r, by simpa [pow_two] using hr.symm⟩

/-- The project's positive fundamental-discriminant condition supplies the
no-rational-root hypothesis for its associated quadratic algebra. -/
theorem rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant
    {D : ℕ} (hD : PositiveFundamentalDiscriminant D) :
    rationalQuadraticAlgebraNoRationalRoot (D : ℤ) :=
  rationalQuadraticAlgebraNoRationalRoot_of_not_isSquare (D : ℤ)
    (int_not_isSquare_of_positiveFundamentalDiscriminant hD)

/-- Under the explicit no-rational-root condition, the rational quadratic
algebra is a number field. -/
theorem rationalQuadraticAlgebra_numberField (d : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot d)] :
    NumberField (rationalQuadraticAlgebra d) :=
  NumberField.of_module_finite ℚ (rationalQuadraticAlgebra d)

/-- The distinguished rational-algebra root is integral over the integers:
it is a root of the monic polynomial `X^2 - d`. -/
theorem rationalQuadraticAlgebra_omega_isIntegral (d : ℤ) :
    IsIntegral ℤ (QuadraticAlgebra.omega : rationalQuadraticAlgebra d) := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C d,
    Polynomial.monic_X_pow_sub_C _ (by decide), ?_⟩
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
  rw [pow_two, rationalQuadraticAlgebra_omega_sq]
  simp

/-- Every image of the standard quadratic order is integral over `ℤ`. -/
theorem quadraticOrderPellEmbedding_isIntegral (d : ℤ) (z : ℤ√d) :
    IsIntegral ℤ (quadraticOrderPellEmbedding d z) := by
  rw [quadraticOrderPellEmbedding_coordinates]
  convert (isIntegral_intCast z.re).add
    ((isIntegral_intCast z.im).mul (rationalQuadraticAlgebra_omega_isIntegral d)) using 1
  ext <;> simp

/-- Under the no-rational-root condition, the concrete quadratic-order map
lands in the ring of integers of the associated rational quadratic field.
This is an inclusion into the integral closure, not an equality of orders. -/
def quadraticOrderPellEmbeddingToRingOfIntegers (d : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot d)] :
    ℤ√d →+* NumberField.RingOfIntegers (rationalQuadraticAlgebra d) where
  toFun z := NumberField.RingOfIntegers.restrict (quadraticOrderPellEmbedding d)
    (quadraticOrderPellEmbedding_isIntegral d) z
  map_zero' := by
    apply NumberField.RingOfIntegers.ext
    change quadraticOrderPellEmbedding d 0 = 0
    exact (quadraticOrderPellEmbedding d).map_zero
  map_one' := by
    apply NumberField.RingOfIntegers.ext
    change quadraticOrderPellEmbedding d 1 = 1
    exact (quadraticOrderPellEmbedding d).map_one
  map_add' x y := by
    apply NumberField.RingOfIntegers.ext
    change quadraticOrderPellEmbedding d (x + y) =
      quadraticOrderPellEmbedding d x + quadraticOrderPellEmbedding d y
    exact (quadraticOrderPellEmbedding d).map_add x y
  map_mul' x y := by
    apply NumberField.RingOfIntegers.ext
    change quadraticOrderPellEmbedding d (x * y) =
      quadraticOrderPellEmbedding d x * quadraticOrderPellEmbedding d y
    exact (quadraticOrderPellEmbedding d).map_mul x y

/-- Coercing the restricted ring-of-integers map back to the quadratic field
recovers the original concrete embedding. -/
@[simp]
theorem coe_quadraticOrderPellEmbeddingToRingOfIntegers (d : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot d)] (z : ℤ√d) :
    (quadraticOrderPellEmbeddingToRingOfIntegers d z : rationalQuadraticAlgebra d) =
      quadraticOrderPellEmbedding d z := rfl

/-- The restricted inclusion into the ring of integers remains injective. -/
theorem quadraticOrderPellEmbeddingToRingOfIntegers_injective (d : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot d)] :
    Function.Injective (quadraticOrderPellEmbeddingToRingOfIntegers d) := by
  intro x y hxy
  apply quadraticOrderPellEmbedding_injective d
  exact congrArg
    (fun z : NumberField.RingOfIntegers (rationalQuadraticAlgebra d) =>
      (z : rationalQuadraticAlgebra d)) hxy

end PellPaper
