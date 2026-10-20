import Pell.QuadraticOrderPellUnitRank
import Mathlib.NumberTheory.NumberField.Discriminant.Basic

/-!
# Sign of the concrete quadratic field discriminant

For a nonnegative nonsquare rational quadratic algebra, the explicit real
embedding proves that both infinite places are real.  Mathlib's sign formula
then gives positivity of the *field* discriminant of its ring of integers.

This is deliberately only a sign result.  It does not identify that field
discriminant with the input radicand or with the source fundamental
discriminant `D`; proving that equality requires a maximal-order integral
basis construction in the two parity branches.
-/

namespace PellPaper

noncomputable section

local instance rationalQuadraticAlgebra_fieldDiscriminant_numberField_instance (d : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot d)] :
    NumberField (rationalQuadraticAlgebra d) :=
  rationalQuadraticAlgebra_numberField d

/-- A nonnegative nonsquare rational quadratic algebra has positive Mathlib
field discriminant. -/
theorem rationalQuadraticAlgebra_fieldDiscriminant_pos_of_nonneg
    (d : ℤ) (hd : 0 ≤ d)
    [Fact (rationalQuadraticAlgebraNoRationalRoot d)] :
    0 < NumberField.discr (rationalQuadraticAlgebra d) := by
  rw [← Int.sign_eq_one_iff_pos, NumberField.sign_discr]
  obtain ⟨_, hcomplex⟩ := rationalQuadraticAlgebra_signature_of_nonneg d hd
  simp [hcomplex]

/-- The Mathlib field discriminant of the concrete quadratic algebra at a
positive fundamental-discriminant index.  This definition has an internally
scoped nonsquare-field instance; it is not asserted to equal `D`. -/
noncomputable def rationalQuadraticAlgebraFieldDiscriminantAtPositiveFundamentalDiscriminant
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) : ℤ :=
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  NumberField.discr (rationalQuadraticAlgebra (D : ℤ))

/-- The concrete quadratic algebra selected by a positive fundamental index
has positive field discriminant.  This remains a sign statement, not the
unproved equality of its discriminant with the index. -/
theorem rationalQuadraticAlgebraFieldDiscriminantAtPositiveFundamentalDiscriminant_pos
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) :
    0 < rationalQuadraticAlgebraFieldDiscriminantAtPositiveFundamentalDiscriminant D hD := by
  unfold rationalQuadraticAlgebraFieldDiscriminantAtPositiveFundamentalDiscriminant
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  exact rationalQuadraticAlgebra_fieldDiscriminant_pos_of_nonneg (D : ℤ)
    (int_pos_of_positiveFundamentalDiscriminant hD).le

end

end PellPaper
