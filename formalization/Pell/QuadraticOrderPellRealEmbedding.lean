import Pell.QuadraticOrderPellEmbedding
import Pell.QuadraticOrderPellUnitEmbedding
import Pell.Definitions

/-!
# The positive real embedding of the concrete Pell quadratic algebra

For a nonnegative radicand, this module constructs the explicitly chosen real
embedding of the rational quadratic algebra that sends its distinguished root
to `sqrt d`. It then identifies the real value of the embedded Pell-order
element with the project's `epsilon`.

This is a concrete numerical embedding only. It does not identify all real
places of the number field, the maximal order, a regulator, or a fundamental
unit.
-/

namespace PellPaper

/-- The real embedding of the concrete rational quadratic algebra which sends
the distinguished root to the nonnegative square root of `d`. -/
noncomputable def rationalQuadraticAlgebraRealEmbedding (d : ℤ) (hd : 0 ≤ d) :
    rationalQuadraticAlgebra d →ₐ[ℚ] ℝ :=
  QuadraticAlgebra.lift ⟨Real.sqrt (d : ℝ), by
    rw [zero_smul, add_zero]
    simp only [Algebra.smul_def, mul_one]
    exact Real.mul_self_sqrt (by exact_mod_cast hd)⟩

/-- The distinguished quadratic-algebra generator evaluates to `sqrt d`. -/
@[simp]
theorem rationalQuadraticAlgebraRealEmbedding_omega (d : ℤ) (hd : 0 ≤ d) :
    rationalQuadraticAlgebraRealEmbedding d hd QuadraticAlgebra.omega =
      Real.sqrt (d : ℝ) := by
  simp [rationalQuadraticAlgebraRealEmbedding]

/-- The concrete real embedding sends an arbitrary Pell-order element to the
obvious coefficient expression. -/
theorem rationalQuadraticAlgebraRealEmbedding_quadraticOrderPellEmbedding
    (d : ℤ) (hd : 0 ≤ d) (z : ℤ√d) :
    rationalQuadraticAlgebraRealEmbedding d hd (quadraticOrderPellEmbedding d z) =
      (z.re : ℝ) + (z.im : ℝ) * Real.sqrt (d : ℝ) := by
  rw [quadraticOrderPellEmbedding_coordinates]
  simp [rationalQuadraticAlgebraRealEmbedding, Algebra.smul_def]

/-- In particular, the real value of an embedded Pell solution is exactly the
project's `epsilon` quantity. -/
theorem rationalQuadraticAlgebraRealEmbedding_pellSolution
    {d : ℤ} (hd : 0 ≤ d) (a : Pell.Solution₁ d) :
    rationalQuadraticAlgebraRealEmbedding d hd
      (quadraticOrderPellEmbedding d (a : ℤ√d)) = epsilon a := by
  simpa [epsilon, Pell.Solution₁.x, Pell.Solution₁.y] using
    rationalQuadraticAlgebraRealEmbedding_quadraticOrderPellEmbedding d hd (a : ℤ√d)

/-- The real value of the norm-one Pell unit inside the ring of integers is
still exactly `epsilon`. This evaluates only the explicitly embedded Pell
subgroup; it makes no statement about arbitrary maximal-order units. -/
theorem rationalQuadraticAlgebraRealEmbedding_quadraticOrderPellUnit
    {d : ℤ} (hd : 0 ≤ d) [Fact (rationalQuadraticAlgebraNoRationalRoot d)]
    (a : Pell.Solution₁ d) :
    rationalQuadraticAlgebraRealEmbedding d hd
      (((quadraticOrderPellUnitEmbedding d a :
        (NumberField.RingOfIntegers (rationalQuadraticAlgebra d))ˣ) :
          NumberField.RingOfIntegers (rationalQuadraticAlgebra d)) :
            rationalQuadraticAlgebra d) = epsilon a := by
  rw [coe_coe_quadraticOrderPellUnitEmbedding]
  exact rationalQuadraticAlgebraRealEmbedding_pellSolution hd a

/-- The two elementary real conjugate values of a norm-one Pell solution have
product one. This is the numerical norm identity behind the embedded unit. -/
theorem epsilon_mul_realConjugate_eq_one
    {d : ℤ} (hd : 0 ≤ d) (a : Pell.Solution₁ d) :
    epsilon a * ((a.x : ℝ) - (a.y : ℝ) * Real.sqrt (d : ℝ)) = 1 := by
  have hroot : (Real.sqrt (d : ℝ)) ^ 2 = (d : ℝ) := by
    rw [Real.sq_sqrt]
    exact_mod_cast hd
  have hpell : (a.x : ℝ) ^ 2 - (d : ℝ) * (a.y : ℝ) ^ 2 = 1 := by
    exact_mod_cast a.prop
  rw [epsilon]
  calc
    ((a.x : ℝ) + (a.y : ℝ) * Real.sqrt (d : ℝ)) *
        ((a.x : ℝ) - (a.y : ℝ) * Real.sqrt (d : ℝ)) =
        (a.x : ℝ) ^ 2 - (d : ℝ) * (a.y : ℝ) ^ 2 := by
          nlinarith
    _ = 1 := hpell

end PellPaper
