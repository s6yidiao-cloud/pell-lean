import Pell.QuadraticOrderPellRingOfIntegers
import Mathlib.NumberTheory.NumberField.ClassNumber

/-!
# Class numbers of the concrete rational quadratic algebras

This module names Mathlib's actual `NumberField.classNumber` for the concrete
quadratic field `QuadraticAlgebra ℚ (d : ℚ) 0`, under the established
no-rational-root condition.  The field and number-field instances are
installed locally from the corresponding proved facts.

The positive-fundamental-discriminant specialization uses `D` only as the
radicand `(D : ℤ)`.  It does not prove that the field discriminant is `D`,
identify ideal and form class groups, construct a `ClassNumberModel`, or use
a class-number formula.
-/

namespace PellPaper

/-- The actual Mathlib class number of the rational quadratic field with
radicand `d`, under the no-rational-root condition. -/
noncomputable def rationalQuadraticAlgebraClassNumber (d : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot d)] : ℕ :=
  let _ : NumberField (rationalQuadraticAlgebra d) :=
    rationalQuadraticAlgebra_numberField d
  NumberField.classNumber (rationalQuadraticAlgebra d)

/-- The concrete rational quadratic algebra has positive class number. -/
theorem rationalQuadraticAlgebraClassNumber_pos (d : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot d)] :
    0 < rationalQuadraticAlgebraClassNumber d := by
  unfold rationalQuadraticAlgebraClassNumber
  let _ : NumberField (rationalQuadraticAlgebra d) :=
    rationalQuadraticAlgebra_numberField d
  exact NumberField.classNumber_pos (rationalQuadraticAlgebra d)

/-- At a positive fundamental-discriminant index, this is the actual class
number of the quadratic algebra with radicand `(D : ℤ)`.  The definition does
not assert that `D` is the discriminant of this number field. -/
noncomputable def rationalQuadraticAlgebraClassNumberAtPositiveFundamentalDiscriminant
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) : ℕ :=
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  rationalQuadraticAlgebraClassNumber (D : ℤ)

/-- Positivity of the actual quadratic-algebra class number at a positive
fundamental-discriminant index. -/
theorem rationalQuadraticAlgebraClassNumberAtPositiveFundamentalDiscriminant_pos
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) :
    0 < rationalQuadraticAlgebraClassNumberAtPositiveFundamentalDiscriminant D hD := by
  unfold rationalQuadraticAlgebraClassNumberAtPositiveFundamentalDiscriminant
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  exact rationalQuadraticAlgebraClassNumber_pos (D : ℤ)

end PellPaper
