import Pell.QuadraticAlgebraDedekindZetaResidue
import Pell.QuadraticDedekindZetaResidueBridge

/-!
# A conditional class-number/Dirichlet-`L`-value bridge

This file combines the concrete real-quadratic Dedekind-zeta residue formula
with the conditional zeta-factorization residue bridge.  The ideal-norm
coefficient identity and the right-hand limit of the chosen Dirichlet
`L`-function remain hypotheses.  In particular, no assertion of character
reality, primitivity, a regulator identification, or a form-class comparison
is made here.
-/

namespace PellPaper

noncomputable section

open Filter Topology NumberField

local instance rationalQuadraticAlgebra_classNumberLValueBridge_numberField_instance
    (d : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot d)] :
    NumberField (rationalQuadraticAlgebra d) :=
  rationalQuadraticAlgebra_numberField d

/-- The exact ideal-norm coefficient identity for the quadratic algebra
selected by a positive fundamental discriminant, with its nonsquare-field
instance internalized. -/
noncomputable def rationalQuadraticAlgebraIdealNormCoefficientEqZetaMulAtPositiveFundamentalDiscriminant
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : Prop :=
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  ∀ n : ℕ, n ≠ 0 →
    (Nat.card {I : Ideal (𝓞 (rationalQuadraticAlgebra (D : ℤ))) //
      Ideal.absNorm I = n} : ℂ) = χ.zetaMul n

/-- Under the exact ideal-norm coefficient identity and the displayed
right-hand limit of the `L`-function, the concrete real quadratic
class-number/residue formula has `Re L(1, χ)` on its right-hand side.

This is an actual-number-field statement; the following endpoint will
internalize the nonsquare-field instance supplied by a positive fundamental
discriminant. -/
theorem rationalQuadraticAlgebra_regulator_mul_classNumber_eq_sqrt_mul_LFunction_apply_one_re_of_idealNormCoefficient_eq_zetaMul
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ))]
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hcoeff : ∀ n : ℕ, n ≠ 0 →
      (Nat.card {I : Ideal (𝓞 (rationalQuadraticAlgebra (D : ℤ))) //
        Ideal.absNorm I = n} : ℂ) = χ.zetaMul n)
    (hL : Tendsto (fun s : ℝ ↦ DirichletCharacter.LFunction χ (s : ℂ))
      (𝓝[>] 1) (𝓝 (DirichletCharacter.LFunction χ 1))) :
    NumberField.Units.regulator (rationalQuadraticAlgebra (D : ℤ)) *
        NumberField.classNumber (rationalQuadraticAlgebra (D : ℤ)) =
      Real.sqrt (D : ℝ) / 2 * (DirichletCharacter.LFunction χ 1).re := by
  have hresidue :
      (NumberField.dedekindZeta_residue (rationalQuadraticAlgebra (D : ℤ)) : ℂ) =
        DirichletCharacter.LFunction χ 1 :=
    dedekindZeta_residue_eq_LFunction_apply_one_of_idealNormCoefficient_eq_zetaMul
      (rationalQuadraticAlgebra (D : ℤ)) χ hcoeff hL
  have hresidueRe :
      NumberField.dedekindZeta_residue (rationalQuadraticAlgebra (D : ℤ)) =
        (DirichletCharacter.LFunction χ 1).re := by
    simpa using congrArg Complex.re hresidue
  rw [rationalQuadraticAlgebra_regulator_mul_classNumber_eq_sqrt_mul_dedekindZeta_residue
    D hD, hresidueRe]

/-- **Caller-instance-free conditional quadratic class-number/Dirichlet-`L`-value bridge.**
For a positive fundamental discriminant, the exact ideal-norm coefficient
identity and the displayed right-hand `L`-limit give the concrete
regulator--class-number formula with `(LFunction χ 1).re` on the right.

The coefficient identity is named above only to internalize the already
proved nonsquare-field instance; its body is the literal ideal-norm fibre
identity.  No character-reality, primitivity, regulator, form-class, or
averaging assertion is added. -/
theorem rationalQuadraticAlgebraRegulatorAtPositiveFundamentalDiscriminant_mul_classNumber_eq_sqrt_mul_LFunction_apply_one_re_of_idealNormCoefficient_eq_zetaMul
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hcoeff :
      rationalQuadraticAlgebraIdealNormCoefficientEqZetaMulAtPositiveFundamentalDiscriminant
        D hD χ)
    (hL : Tendsto (fun s : ℝ ↦ DirichletCharacter.LFunction χ (s : ℂ))
      (𝓝[>] 1) (𝓝 (DirichletCharacter.LFunction χ 1))) :
    rationalQuadraticAlgebraRegulatorAtPositiveFundamentalDiscriminant D hD *
        rationalQuadraticAlgebraClassNumberAtPositiveFundamentalDiscriminant D hD =
      Real.sqrt (D : ℝ) / 2 * (DirichletCharacter.LFunction χ 1).re := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  have hcoeff' : ∀ n : ℕ, n ≠ 0 →
      (Nat.card {I : Ideal (𝓞 (rationalQuadraticAlgebra (D : ℤ))) //
        Ideal.absNorm I = n} : ℂ) = χ.zetaMul n := by
    simpa [rationalQuadraticAlgebraIdealNormCoefficientEqZetaMulAtPositiveFundamentalDiscriminant]
      using hcoeff
  have hresidue :
      (NumberField.dedekindZeta_residue (rationalQuadraticAlgebra (D : ℤ)) : ℂ) =
        DirichletCharacter.LFunction χ 1 :=
    dedekindZeta_residue_eq_LFunction_apply_one_of_idealNormCoefficient_eq_zetaMul
      (rationalQuadraticAlgebra (D : ℤ)) χ hcoeff' hL
  have hresidueRe :
      NumberField.dedekindZeta_residue (rationalQuadraticAlgebra (D : ℤ)) =
        (DirichletCharacter.LFunction χ 1).re := by
    simpa using congrArg Complex.re hresidue
  calc
    rationalQuadraticAlgebraRegulatorAtPositiveFundamentalDiscriminant D hD *
        rationalQuadraticAlgebraClassNumberAtPositiveFundamentalDiscriminant D hD =
      Real.sqrt (D : ℝ) / 2 *
        rationalQuadraticAlgebraDedekindZetaResidueAtPositiveFundamentalDiscriminant D hD :=
      rationalQuadraticAlgebraRegulatorAtPositiveFundamentalDiscriminant_mul_classNumber_eq_sqrt_mul_dedekindZetaResidue
        D hD
    _ = Real.sqrt (D : ℝ) / 2 * (DirichletCharacter.LFunction χ 1).re := by
      have hresidueAtRe :
          rationalQuadraticAlgebraDedekindZetaResidueAtPositiveFundamentalDiscriminant D hD =
            (DirichletCharacter.LFunction χ 1).re := by
        change NumberField.dedekindZeta_residue (rationalQuadraticAlgebra (D : ℤ)) =
          (DirichletCharacter.LFunction χ 1).re
        exact hresidueRe
      rw [hresidueAtRe]

end

end PellPaper
