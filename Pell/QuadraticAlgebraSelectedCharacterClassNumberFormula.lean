import Pell.QuadraticIdealNormEulerConcrete
import Pell.QuadraticDedekindZetaCharacterNontrivial
import Pell.QuadraticAlgebraSelectedUnitClassNumberLValueBridge

/-!
# The actual quadratic class-number formula for the selected character

The full ideal-coefficient identity and zeta factorization now supply all
arithmetic inputs. The factorization forces character nontriviality and
the L-function right limit at one. Combining with the actual Dedekind-zeta
residue gives the regulator/class-number formula for the selected complex
character, also with the selected fundamental unit logarithm.

Only positive fundamentality is assumed. This is a pointwise formula for
the actual ideal class number, not a form-class equality or an average
estimate; no conductor or primitivity assertion is made.
-/

namespace PellPaper

noncomputable section

open Filter Topology

local instance rationalQuadraticAlgebra_selectedCharacterFormula_numberField_instance (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    NumberField (rationalQuadraticAlgebra D) :=
  rationalQuadraticAlgebra_numberField D

/-- The actual selected complex character is nontrivial. -/
theorem kroneckerCharacterAtPositiveFundamentalDiscriminantC_ne_one
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) :
    kroneckerCharacterAtPositiveFundamentalDiscriminantC D hD ≠ 1 := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  let _ : NeZero D := ⟨by have := hD.1; omega⟩
  apply dirichletCharacter_ne_one_of_dedekindZeta_rightHalfPlaneFactorization
    (rationalQuadraticAlgebra (D : ℤ))
    (kroneckerCharacterAtPositiveFundamentalDiscriminantC D hD)
  intro s hs
  exact rationalQuadraticAlgebra_dedekindZeta_eq_riemannZeta_mul_LFunction D hD
    (by simpa using hs)

/-- No separate continuity input is required at one for the selected
character's L-function. -/
theorem tendsto_selectedKroneckerLFunction_ofReal_nhdsGT_one
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) :
    let _ : NeZero D := ⟨by have := hD.1; omega⟩
    Tendsto (fun s : ℝ ↦ DirichletCharacter.LFunction
      (kroneckerCharacterAtPositiveFundamentalDiscriminantC D hD) (s : ℂ))
      (𝓝[>] 1) (𝓝 (DirichletCharacter.LFunction
        (kroneckerCharacterAtPositiveFundamentalDiscriminantC D hD) 1)) := by
  let _ : NeZero D := ⟨by have := hD.1; omega⟩
  dsimp only
  have hcontinuous := (DirichletCharacter.differentiable_LFunction
    (kroneckerCharacterAtPositiveFundamentalDiscriminantC_ne_one D hD)).continuous
  simpa only [Function.comp_def, Complex.ofReal_one] using
    ((hcontinuous.comp Complex.continuous_ofReal).tendsto (1 : ℝ)).mono_left
      nhdsWithin_le_nhds

/-- The pointwise real-quadratic class-number formula for the actual
regulator, actual ideal class number and selected complex character. -/
theorem rationalQuadraticAlgebraRegulator_mul_classNumber_eq_sqrt_mul_selected_LFunction_re
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) :
    let _ : NeZero D := ⟨by have := hD.1; omega⟩
    rationalQuadraticAlgebraRegulatorAtPositiveFundamentalDiscriminant D hD *
        rationalQuadraticAlgebraClassNumberAtPositiveFundamentalDiscriminant D hD =
      Real.sqrt (D : ℝ) / 2 * (DirichletCharacter.LFunction
        (kroneckerCharacterAtPositiveFundamentalDiscriminantC D hD) 1).re := by
  let _ : NeZero D := ⟨by have := hD.1; omega⟩
  dsimp only
  apply
    rationalQuadraticAlgebraRegulatorAtPositiveFundamentalDiscriminant_mul_classNumber_eq_sqrt_mul_LFunction_apply_one_re_of_idealNormCoefficient_eq_zetaMul
      D hD (kroneckerCharacterAtPositiveFundamentalDiscriminantC D hD)
  · unfold rationalQuadraticAlgebraIdealNormCoefficientEqZetaMulAtPositiveFundamentalDiscriminant
    dsimp only
    intro n hn
    exact rationalQuadraticAlgebra_raw_idealNormCoefficient_eq_zetaMul D hD hn
  · exact tendsto_selectedKroneckerLFunction_ofReal_nhdsGT_one D hD

/-- The same actual class-number formula uses the logarithm of the
selected oriented fundamental unit. -/
theorem selectedFundamentalUnitLog_mul_classNumber_eq_sqrt_mul_selected_LFunction_re
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) :
    let _ : NeZero D := ⟨by have := hD.1; omega⟩
    (let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
      ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩;
      Real.log (concreteFundamentalUnitRealModel D hD).eta) *
        rationalQuadraticAlgebraClassNumberAtPositiveFundamentalDiscriminant D hD =
      Real.sqrt (D : ℝ) / 2 * (DirichletCharacter.LFunction
        (kroneckerCharacterAtPositiveFundamentalDiscriminantC D hD) 1).re := by
  let _ : NeZero D := ⟨by have := hD.1; omega⟩
  dsimp only
  rw [← rationalQuadraticAlgebraRegulatorAtPositiveFundamentalDiscriminant_eq_log_concreteFundamentalUnitRealModel
    D hD]
  exact rationalQuadraticAlgebraRegulator_mul_classNumber_eq_sqrt_mul_selected_LFunction_re D hD

end
end PellPaper
