import Pell.MathlibRegulatorSelectedUnitBridge
import Pell.QuadraticAlgebraClassNumberLValueBridge

/-!
# Conditional class-number formula with the selected fundamental unit

The actual Mathlib-regulator identity and the previously established
conditional Dedekind-zeta/Dirichlet-`L` class-number bridge compose directly.
This file makes that precise without adding any character, coefficient,
analytic, or form-class input.
-/

namespace PellPaper

noncomputable section

open Filter Topology

/-- Under the existing exact ideal-norm coefficient identity and real-right
`L`-limit, the actual class-number formula can be written using the logarithm
of the selected oriented fundamental unit.  The ideal-norm and analytic
inputs remain explicit, and this is not an average or form-class theorem. -/
theorem selectedFundamentalUnitLog_mul_classNumber_eq_sqrt_mul_LFunction_apply_one_re_of_idealNormCoefficient_eq_zetaMul
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hcoeff :
      rationalQuadraticAlgebraIdealNormCoefficientEqZetaMulAtPositiveFundamentalDiscriminant
        D hD χ)
    (hL : Tendsto (fun s : ℝ ↦ DirichletCharacter.LFunction χ (s : ℂ))
      (𝓝[>] 1) (𝓝 (DirichletCharacter.LFunction χ 1))) :
    (let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
      ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩;
      Real.log (concreteFundamentalUnitRealModel D hD).eta) *
        rationalQuadraticAlgebraClassNumberAtPositiveFundamentalDiscriminant D hD =
      Real.sqrt (D : ℝ) / 2 * (DirichletCharacter.LFunction χ 1).re := by
  rw [← rationalQuadraticAlgebraRegulatorAtPositiveFundamentalDiscriminant_eq_log_concreteFundamentalUnitRealModel
    D hD]
  exact
    rationalQuadraticAlgebraRegulatorAtPositiveFundamentalDiscriminant_mul_classNumber_eq_sqrt_mul_LFunction_apply_one_re_of_idealNormCoefficient_eq_zetaMul
      D hD χ hcoeff hL

end

end PellPaper
