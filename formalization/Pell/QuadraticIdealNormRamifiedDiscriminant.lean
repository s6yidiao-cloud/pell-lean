import Pell.QuadraticAlgebraFieldDiscriminantEquality
import Mathlib.NumberTheory.NumberField.Discriminant.Different

/-!
# Ramification at a discriminant prime of a concrete quadratic algebra

For the rational quadratic algebra attached to a positive fundamental
discriminant `D`, a rational prime `p` dividing `D` is not unramified in the
ring of integers.  The proof uses the project's proved equality between the
field discriminant and `D`, together with Mathlib's discriminant/unramified
criterion.

This is a concrete reduction of the ramified local ideal-norm frontier.  It
does not yet select the prime over `p`, prove that it is unique, calculate its
inertia degree or absolute norm, or identify any Euler factor.
-/

namespace PellPaper

noncomputable section

local instance rationalQuadraticAlgebra_ramifiedDiscriminant_numberField_instance (d : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot d)] :
    NumberField (rationalQuadraticAlgebra d) :=
  rationalQuadraticAlgebra_numberField d

/-- A prime divisor of a positive fundamental discriminant is ramified in the
ring of integers of the corresponding rational quadratic algebra. -/
theorem rationalQuadraticAlgebra_not_isUnramifiedIn_of_prime_dvd_positiveFundamentalDiscriminant
    (D p : ℕ) (hD : PositiveFundamentalDiscriminant D)
    (hp : Nat.Prime p) (hpD : p ∣ D) :
    let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
      ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
    ¬ Algebra.IsUnramifiedIn
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ)))
      (Ideal.span ({(p : ℤ)} : Set ℤ)) := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  dsimp only
  have hpz : Prime (p : ℤ) := by
    rw [Int.prime_iff_natAbs_prime]
    simpa using hp
  rw [← NumberField.not_dvd_discr_iff_isUnramifiedIn
    (rationalQuadraticAlgebra (D : ℤ))
    (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))) hpz]
  have hdisc : NumberField.discr (rationalQuadraticAlgebra (D : ℤ)) = (D : ℤ) := by
    change rationalQuadraticAlgebraFieldDiscriminantAtPositiveFundamentalDiscriminant D hD =
      (D : ℤ)
    exact rationalQuadraticAlgebraFieldDiscriminantAtPositiveFundamentalDiscriminant_eq D hD
  rw [hdisc]
  exact not_not.mpr (by exact_mod_cast hpD)

end

end PellPaper
