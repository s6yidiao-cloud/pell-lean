import Pell.QuadraticIdealNormPrimePowerGeometric
import Pell.QuadraticIdealNormEulerActualAssembly
import Pell.QuadraticDedekindZetaLFactorization

/-!
# Concrete quadratic ideal coefficients and the zeta--L factorization

For the actual quadratic field at a positive fundamental discriminant, the
proved prime-power counts and ideal-norm multiplicativity identify the
zero-normalized ideal coefficient arithmetic function with the divisor-sum
coefficient of the selected complex character.  The raw ideal-norm fibre
identity is stated only at nonzero norms, since its value at zero is not
the zero-normalized arithmetic-function value.

The resulting Dedekind-zeta factorization holds for `Re(s) > 1`, without
supplied coefficient, splitting, or character-value hypotheses.  This
module does not assert primitivity, a conductor formula, a residue formula
at `s = 1`, or a class-number formula.
-/

namespace PellPaper

noncomputable section

local instance rationalQuadraticAlgebra_eulerConcrete_numberField_instance (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    NumberField (rationalQuadraticAlgebra D) :=
  rationalQuadraticAlgebra_numberField D

/-- The complete zero-normalized ideal coefficient arithmetic function is
the divisor-sum Euler coefficient of the actual selected character. -/
theorem rationalQuadraticAlgebra_idealNormCoefficient_eq_zetaMul
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) :
    let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
      ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
    let _ : NeZero D := ⟨by have := hD.1; omega⟩
    idealNormCoefficient (rationalQuadraticAlgebra (D : ℤ)) =
      (kroneckerCharacterAtPositiveFundamentalDiscriminantC D hD).zetaMul := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  let _ : NeZero D := ⟨by have := hD.1; omega⟩
  dsimp only
  exact idealNormCoefficient_eq_zetaMul_of_primePowerGeometricSum
    (rationalQuadraticAlgebra (D : ℤ))
    (kroneckerCharacterAtPositiveFundamentalDiscriminantC D hD)
    (fun p k hp => rationalQuadraticAlgebra_idealNormPrimePowerGeometricSum D p k hD hp)

/-- At every nonzero norm, the actual ideal fibre has the selected
character's divisor-sum coefficient.  The raw norm-zero fibre is excluded. -/
theorem rationalQuadraticAlgebra_raw_idealNormCoefficient_eq_zetaMul
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) {n : ℕ} (hn : n ≠ 0) :
    let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
      ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
    let _ : NeZero D := ⟨by have := hD.1; omega⟩
    (Nat.card {I : Ideal (NumberField.RingOfIntegers
      (rationalQuadraticAlgebra (D : ℤ))) // Ideal.absNorm I = n} : ℂ) =
      (kroneckerCharacterAtPositiveFundamentalDiscriminantC D hD).zetaMul n := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  let _ : NeZero D := ⟨by have := hD.1; omega⟩
  dsimp only
  have hcoeff := rationalQuadraticAlgebra_idealNormCoefficient_eq_zetaMul D hD
  dsimp only at hcoeff
  rw [← idealNormCoefficient_apply_of_ne_zero (rationalQuadraticAlgebra (D : ℤ)) hn]
  exact congrArg (fun f : ArithmeticFunction ℂ => f n) hcoeff

/-- In the half-plane of absolute convergence, the concrete quadratic
Dedekind zeta function factors using the actual selected complex character.
No local arithmetic or coefficient premise remains. -/
theorem rationalQuadraticAlgebra_dedekindZeta_eq_riemannZeta_mul_LFunction
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) {s : ℂ} (hs : 1 < s.re) :
    let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
      ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
    let _ : NeZero D := ⟨by have := hD.1; omega⟩
    NumberField.dedekindZeta (rationalQuadraticAlgebra (D : ℤ)) s =
      riemannZeta s * DirichletCharacter.LFunction
        (kroneckerCharacterAtPositiveFundamentalDiscriminantC D hD) s := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  let _ : NeZero D := ⟨by have := hD.1; omega⟩
  dsimp only
  exact dedekindZeta_eq_riemannZeta_mul_LFunction_of_idealNormCoefficient_eq_zetaMul
    (rationalQuadraticAlgebra (D : ℤ))
    (kroneckerCharacterAtPositiveFundamentalDiscriminantC D hD) hs
    (fun n hn => rationalQuadraticAlgebra_raw_idealNormCoefficient_eq_zetaMul D hD hn)

end

end PellPaper
