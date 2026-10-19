import Pell.QuadraticAlgebraClassNumber
import Pell.QuadraticAlgebraFieldDiscriminantEquality
import Pell.QuadraticOrderPellUnitRank
import Pell.QuadraticAlgebraTorsionOrder
import Mathlib.NumberTheory.NumberField.DedekindZeta

/-!
# Dedekind-zeta residue for the concrete real quadratic algebra

This specializes Mathlib's Dirichlet class-number formula for the residue of
the Dedekind zeta function to the actual quadratic algebra at a positive
fundamental discriminant.  The field discriminant and signature are both
proved elsewhere in the formalization, so the resulting formula has the
source discriminant `D` in its denominator.

This is deliberately a Dedekind-zeta statement.  It does not prove a
factorization into a Riemann zeta function and a quadratic Dirichlet
`L`-function, identify a primitive character, or compare ideal and form
class numbers.
-/

namespace PellPaper

noncomputable section

open NumberField NumberField.InfinitePlace

local instance rationalQuadraticAlgebra_dedekindZeta_numberField_instance (d : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot d)] :
    NumberField (rationalQuadraticAlgebra d) :=
  rationalQuadraticAlgebra_numberField d

/-- The Dedekind-zeta residue of the concrete field selected by a positive
fundamental discriminant, with its nonsquare-field instance internalized. -/
noncomputable def rationalQuadraticAlgebraDedekindZetaResidueAtPositiveFundamentalDiscriminant
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) : ℝ :=
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  NumberField.dedekindZeta_residue (rationalQuadraticAlgebra (D : ℤ))

/-- The regulator in the same internally scoped positive-fundamental field. -/
noncomputable def rationalQuadraticAlgebraRegulatorAtPositiveFundamentalDiscriminant
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) : ℝ :=
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  NumberField.Units.regulator (rationalQuadraticAlgebra (D : ℤ))

/-- At every positive fundamental discriminant, the residue in Mathlib's
Dirichlet class-number formula specializes to the real-quadratic expression
with two real places and field discriminant exactly `D`. -/
theorem rationalQuadraticAlgebra_dedekindZeta_residue_eq_at_positiveFundamentalDiscriminant
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ))] :
    NumberField.dedekindZeta_residue (rationalQuadraticAlgebra (D : ℤ)) =
      (4 * NumberField.Units.regulator (rationalQuadraticAlgebra (D : ℤ)) *
          NumberField.classNumber (rationalQuadraticAlgebra (D : ℤ))) /
        (NumberField.Units.torsionOrder (rationalQuadraticAlgebra (D : ℤ)) *
          Real.sqrt (D : ℝ)) := by
  rw [NumberField.dedekindZeta_residue_def]
  obtain ⟨hreal, hcomplex⟩ :=
    rationalQuadraticAlgebra_signature_of_nonneg (D : ℤ)
      (int_pos_of_positiveFundamentalDiscriminant hD).le
  have hdiscr : NumberField.discr (rationalQuadraticAlgebra (D : ℤ)) = (D : ℤ) := by
    change rationalQuadraticAlgebraFieldDiscriminantAtPositiveFundamentalDiscriminant D hD =
      (D : ℤ)
    exact rationalQuadraticAlgebraFieldDiscriminantAtPositiveFundamentalDiscriminant_eq D hD
  rw [hreal, hcomplex, hdiscr]
  norm_num

/-- The residue specialization in a caller-instance-free form. -/
theorem rationalQuadraticAlgebraDedekindZetaResidueAtPositiveFundamentalDiscriminant_eq
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) :
    rationalQuadraticAlgebraDedekindZetaResidueAtPositiveFundamentalDiscriminant D hD =
      (4 * rationalQuadraticAlgebraRegulatorAtPositiveFundamentalDiscriminant D hD *
          rationalQuadraticAlgebraClassNumberAtPositiveFundamentalDiscriminant D hD) /
        (2 * Real.sqrt (D : ℝ)) := by
  unfold rationalQuadraticAlgebraDedekindZetaResidueAtPositiveFundamentalDiscriminant
    rationalQuadraticAlgebraRegulatorAtPositiveFundamentalDiscriminant
    rationalQuadraticAlgebraClassNumberAtPositiveFundamentalDiscriminant
    rationalQuadraticAlgebraClassNumber
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  rw [rationalQuadraticAlgebra_dedekindZeta_residue_eq_at_positiveFundamentalDiscriminant D hD,
    rationalQuadraticAlgebra_torsionOrder_eq_two_at_positiveFundamentalDiscriminant D hD]
  norm_num

/-- Rearranging the specialized residue formula using the exact two-element
torsion subgroup.  This is the concrete Dedekind-zeta form of the real
quadratic class-number formula. -/
theorem rationalQuadraticAlgebra_regulator_mul_classNumber_eq_sqrt_mul_dedekindZeta_residue
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ))] :
    NumberField.Units.regulator (rationalQuadraticAlgebra (D : ℤ)) *
        NumberField.classNumber (rationalQuadraticAlgebra (D : ℤ)) =
      Real.sqrt (D : ℝ) / 2 *
        NumberField.dedekindZeta_residue (rationalQuadraticAlgebra (D : ℤ)) := by
  rw [rationalQuadraticAlgebra_dedekindZeta_residue_eq_at_positiveFundamentalDiscriminant D hD,
    rationalQuadraticAlgebra_torsionOrder_eq_two_at_positiveFundamentalDiscriminant D hD]
  have hDpos : 0 < (D : ℝ) := by
    exact_mod_cast int_pos_of_positiveFundamentalDiscriminant hD
  have hsqrt : Real.sqrt (D : ℝ) ≠ 0 := (Real.sqrt_pos.2 hDpos).ne'
  field_simp [hsqrt]
  ring

/-- The concrete caller-instance-free Dedekind-zeta class-number formula. -/
theorem rationalQuadraticAlgebraRegulatorAtPositiveFundamentalDiscriminant_mul_classNumber_eq_sqrt_mul_dedekindZetaResidue
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) :
    rationalQuadraticAlgebraRegulatorAtPositiveFundamentalDiscriminant D hD *
        rationalQuadraticAlgebraClassNumberAtPositiveFundamentalDiscriminant D hD =
      Real.sqrt (D : ℝ) / 2 *
        rationalQuadraticAlgebraDedekindZetaResidueAtPositiveFundamentalDiscriminant D hD := by
  rw [rationalQuadraticAlgebraDedekindZetaResidueAtPositiveFundamentalDiscriminant_eq D hD]
  have hDpos : 0 < (D : ℝ) := by
    exact_mod_cast int_pos_of_positiveFundamentalDiscriminant hD
  have hsqrt : Real.sqrt (D : ℝ) ≠ 0 := (Real.sqrt_pos.2 hDpos).ne'
  field_simp [hsqrt]
  ring

end

end PellPaper
