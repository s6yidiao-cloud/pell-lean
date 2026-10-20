import Pell.ConcreteQuadraticAlgebraClassNumberModel
import Pell.QuadraticAlgebraClassNumberLValueBridge

/-!
# A conditional final class-average bridge for the concrete quadratic algebra

This module makes one algebraic handoff from the actual quadratic-algebra
class-number formula to the finite form-sum shape used at the end of
`main.tex`.  It deliberately uses the project's *surrogate*
`rationalQuadraticAlgebraClassNumberModel`, whose form coordinate is the
Mathlib ideal class number by definition.  It does **not** construct proper
indefinite form classes or identify their class number with this surrogate.

The first theorem below is an exact finite identity conditional on a
pointwise regulator--`L`-value formula.  The next theorem turns a separately
supplied weighted `L`/regulator sum estimate into the manuscript's displayed
class-average scale.  The final interface shows that the already formalized
conditional Dedekind-zeta/Dirichlet-`L` bridge supplies the required
pointwise formula for a family of characters with varying moduli.

Thus no moment estimate, coefficient identity, right-hand `L`-limit,
regulator identification, or genuine form-class realization is hidden here.
-/

namespace PellPaper

noncomputable section

open Filter Topology
open scoped BigOperators

/-- The exact weighted finite sum naturally produced by the concrete
regulator--class-number formula.  The `if` makes the expression total; on
`fundamentalDiscriminantsBelow X` its positive-fundamental branch is the only
one used. -/
noncomputable def rationalQuadraticAlgebraWeightedLRegulatorSum
    (L : ℕ → ℝ) (X : ℝ) : ℝ := by
  classical
  exact ∑ D ∈ fundamentalDiscriminantsBelow X,
    if hD : PositiveFundamentalDiscriminant D then
      Real.sqrt (D : ℝ) * L D /
        rationalQuadraticAlgebraRegulatorAtPositiveFundamentalDiscriminant D hD
    else 0

/-- A pointwise class-number formula in precisely the shape needed by the
finite final bridge.  This is an interface proposition, not an additional
assumption declaration: the last theorem in this file obtains it from the
existing conditional Dedekind-zeta/Dirichlet-`L` bridge. -/
def RationalQuadraticAlgebraClassNumberFormulaInput (L : ℕ → ℝ) : Prop :=
  ∀ D (hD : PositiveFundamentalDiscriminant D),
    rationalQuadraticAlgebraRegulatorAtPositiveFundamentalDiscriminant D hD *
        rationalQuadraticAlgebraClassNumberAtPositiveFundamentalDiscriminant D hD =
      Real.sqrt (D : ℝ) / 2 * L D

/-- The concrete regulator is strictly positive on the intended family. -/
theorem rationalQuadraticAlgebraRegulatorAtPositiveFundamentalDiscriminant_pos
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) :
    0 < rationalQuadraticAlgebraRegulatorAtPositiveFundamentalDiscriminant D hD := by
  unfold rationalQuadraticAlgebraRegulatorAtPositiveFundamentalDiscriminant
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  let _ : NumberField (rationalQuadraticAlgebra (D : ℤ)) :=
    rationalQuadraticAlgebra_numberField (D : ℤ)
  exact NumberField.Units.regulator_pos _

/-- The form coordinate of the concrete surrogate is exactly one half of the
weighted class-number-formula expression.  This is only an identity for the
surrogate coordinate; it is not a form-class realization. -/
theorem rationalQuadraticAlgebraClassNumberModel_form_eq_half_weightedLValue_div_regulator
    (L : ℕ → ℝ) (hformula : RationalQuadraticAlgebraClassNumberFormulaInput L)
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) :
    (rationalQuadraticAlgebraClassNumberModel.formClassNumber D : ℝ) =
      (1 / 2 : ℝ) *
        (Real.sqrt (D : ℝ) * L D /
          rationalQuadraticAlgebraRegulatorAtPositiveFundamentalDiscriminant D hD) := by
  rw [rationalQuadraticAlgebraClassNumberModel_form_eq hD]
  have hR := rationalQuadraticAlgebraRegulatorAtPositiveFundamentalDiscriminant_pos D hD
  calc
    (rationalQuadraticAlgebraClassNumberAtPositiveFundamentalDiscriminant D hD : ℝ) =
        (rationalQuadraticAlgebraRegulatorAtPositiveFundamentalDiscriminant D hD *
          rationalQuadraticAlgebraClassNumberAtPositiveFundamentalDiscriminant D hD) /
          rationalQuadraticAlgebraRegulatorAtPositiveFundamentalDiscriminant D hD := by
            field_simp
    _ = (Real.sqrt (D : ℝ) / 2 * L D) /
          rationalQuadraticAlgebraRegulatorAtPositiveFundamentalDiscriminant D hD := by
            rw [hformula D hD]
    _ = (1 / 2 : ℝ) *
        (Real.sqrt (D : ℝ) * L D /
          rationalQuadraticAlgebraRegulatorAtPositiveFundamentalDiscriminant D hD) := by
            ring

/-- Exact finite-sum form of the conditional class-number formula for the
concrete surrogate model. -/
theorem rationalQuadraticAlgebraClassNumberModel_formClassSum_eq_half_weightedLRegulatorSum
    (L : ℕ → ℝ) (hformula : RationalQuadraticAlgebraClassNumberFormulaInput L)
    (X : ℝ) :
    rationalQuadraticAlgebraClassNumberModel.formClassSum X =
      (1 / 2 : ℝ) * rationalQuadraticAlgebraWeightedLRegulatorSum L X := by
  unfold ClassNumberModel.formClassSum rationalQuadraticAlgebraWeightedLRegulatorSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro D hDX
  have hD : PositiveFundamentalDiscriminant D :=
    (mem_fundamentalDiscriminantsBelow.mp hDX).1
  simp only [dif_pos hD]
  exact rationalQuadraticAlgebraClassNumberModel_form_eq_half_weightedLValue_div_regulator
    L hformula D hD

/-- A weighted `L`/regulator sum estimate transfers directly to the exact
class-average scale for the concrete surrogate model.  The analytic weighted
sum estimate is deliberately an explicit hypothesis. -/
theorem rationalQuadraticAlgebraClassNumberModel_formClassSum_le_classAverageScale_of_weightedLRegulatorSum
    (L : ℕ → ℝ) (hformula : RationalQuadraticAlgebraClassNumberFormulaInput L)
    (C X : ℝ)
    (hweighted : rationalQuadraticAlgebraWeightedLRegulatorSum L X ≤
      2 * C * classAverageScale X) :
    rationalQuadraticAlgebraClassNumberModel.formClassSum X ≤
      C * classAverageScale X := by
  rw [rationalQuadraticAlgebraClassNumberModel_formClassSum_eq_half_weightedLRegulatorSum
    L hformula X]
  nlinarith

/-- A varying-modulus family of complex Dirichlet characters.  The modulus
is retained as part of the data so that a later arithmetic development can
use the genuine conductor for each discriminant rather than forcing an
artificial common modulus. -/
structure RationalQuadraticAlgebraLValueFamily where
  modulus : ℕ → ℕ
  modulus_ne_zero : ∀ D, modulus D ≠ 0
  character : ∀ D, DirichletCharacter ℂ (modulus D)

/-- The real part of the `L`-value attached to a member of a varying-modulus
character family. -/
noncomputable def RationalQuadraticAlgebraLValueFamily.value
    (F : RationalQuadraticAlgebraLValueFamily) (D : ℕ) : ℝ := by
  letI : NeZero (F.modulus D) := ⟨F.modulus_ne_zero D⟩
  exact (DirichletCharacter.LFunction (F.character D) 1).re

/-- The literal ideal-norm coefficient interface, indexed by the varying
character family. -/
def RationalQuadraticAlgebraLValueFamily.CoefficientInput
    (F : RationalQuadraticAlgebraLValueFamily) : Prop :=
  ∀ D (hD : PositiveFundamentalDiscriminant D),
    letI : NeZero (F.modulus D) := ⟨F.modulus_ne_zero D⟩
    rationalQuadraticAlgebraIdealNormCoefficientEqZetaMulAtPositiveFundamentalDiscriminant
      D hD (F.character D)

/-- The right-hand real-ray limit interface needed to take the residue in
the existing Dedekind-zeta factorization bridge. -/
def RationalQuadraticAlgebraLValueFamily.RightLimitInput
    (F : RationalQuadraticAlgebraLValueFamily) : Prop :=
  ∀ D (_ : PositiveFundamentalDiscriminant D),
    letI : NeZero (F.modulus D) := ⟨F.modulus_ne_zero D⟩
    Tendsto (fun s : ℝ ↦ DirichletCharacter.LFunction (F.character D) (s : ℂ))
      (𝓝[>] 1) (𝓝 (DirichletCharacter.LFunction (F.character D) 1))

/-- The existing conditional concrete class-number/`L`-value bridge yields
the pointwise formula consumed by the finite final bridge.  The coefficient
identity and `L`-limit remain explicit inputs, as they should. -/
theorem rationalQuadraticAlgebraClassNumberFormulaInput_of_lValueFamilyInputs
    (F : RationalQuadraticAlgebraLValueFamily)
    (hcoeff : F.CoefficientInput) (hlimit : F.RightLimitInput) :
    RationalQuadraticAlgebraClassNumberFormulaInput F.value := by
  intro D hD
  let _ : NeZero (F.modulus D) := ⟨F.modulus_ne_zero D⟩
  have h :=
    rationalQuadraticAlgebraRegulatorAtPositiveFundamentalDiscriminant_mul_classNumber_eq_sqrt_mul_LFunction_apply_one_re_of_idealNormCoefficient_eq_zetaMul
      D hD (F.character D) (hcoeff D hD) (hlimit D hD)
  simpa [RationalQuadraticAlgebraLValueFamily.value] using h

/-- Fully composed conditional final reduction: a literal ideal-norm
coefficient family, real-ray `L` limits, and one weighted sum estimate imply
the manuscript-shaped scale for the concrete surrogate's finite form sum.
It does not assert the headline theorem or interpret this surrogate as the
manuscript's proper form-class number. -/
theorem rationalQuadraticAlgebraClassNumberModel_formClassSum_le_classAverageScale_of_lValueFamilyInputs
    (F : RationalQuadraticAlgebraLValueFamily)
    (hcoeff : F.CoefficientInput) (hlimit : F.RightLimitInput)
    (C X : ℝ)
    (hweighted : rationalQuadraticAlgebraWeightedLRegulatorSum F.value X ≤
      2 * C * classAverageScale X) :
    rationalQuadraticAlgebraClassNumberModel.formClassSum X ≤
      C * classAverageScale X := by
  exact rationalQuadraticAlgebraClassNumberModel_formClassSum_le_classAverageScale_of_weightedLRegulatorSum
    F.value (rationalQuadraticAlgebraClassNumberFormulaInput_of_lValueFamilyInputs
      F hcoeff hlimit) C X hweighted

end

end PellPaper
