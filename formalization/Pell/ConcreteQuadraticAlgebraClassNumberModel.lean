import Pell.ClassAverage
import Pell.QuadraticAlgebraClassNumber

/-!
# A concrete quadratic-algebra class-number model

`QuadraticAlgebraClassNumber` supplies Mathlib's actual ideal class number for
the rational quadratic algebra with radicand `D`.  This file packages those
values into the generic `ClassNumberModel` interface at positive fundamental
discriminants.

The two coordinates of the resulting model are deliberately identical.  It
is therefore a concrete, kernel-checked *surrogate* for the generic finite
class-sum machinery, not an identification of ordinary and narrow ideal
class numbers with the manuscript's proper indefinite form-class number.
In particular, it does not establish that the algebra's field discriminant is
`D`, nor the source comparison `h(K) ≤ H(D) ≤ 2 h(K)`.
-/

namespace PellPaper

noncomputable section

/-- A total discriminant-indexed class-number model built from Mathlib's
actual ideal class number of the concrete rational quadratic algebra.  Away
from positive fundamental discriminants its values are set to zero.  On the
intended family the two model coordinates are equal by construction; this is
an interface model rather than the source's form-class interpretation. -/
noncomputable def rationalQuadraticAlgebraClassNumberModel : ClassNumberModel := by
  classical
  exact
    { ordinaryClassNumber := fun D => if hD : PositiveFundamentalDiscriminant D then
        rationalQuadraticAlgebraClassNumberAtPositiveFundamentalDiscriminant D hD else 0
      formClassNumber := fun D => if hD : PositiveFundamentalDiscriminant D then
        rationalQuadraticAlgebraClassNumberAtPositiveFundamentalDiscriminant D hD else 0
      ordinaryClassNumber_pos := fun D hD => by
        simp only [dif_pos hD]
        exact rationalQuadraticAlgebraClassNumberAtPositiveFundamentalDiscriminant_pos D hD
      formClassNumber_pos := fun D hD => by
        simp only [dif_pos hD]
        exact rationalQuadraticAlgebraClassNumberAtPositiveFundamentalDiscriminant_pos D hD
      ordinary_le_form := fun D hD => by
        simp only [dif_pos hD]
        exact le_rfl
      form_le_twice_ordinary := fun D hD => by
        simp only [dif_pos hD]
        omega }

/-- On a positive fundamental discriminant, each coordinate of the concrete
surrogate model is the Mathlib ideal class number of the chosen quadratic
algebra. -/
theorem rationalQuadraticAlgebraClassNumberModel_ordinary_eq
    {D : ℕ} (hD : PositiveFundamentalDiscriminant D) :
    rationalQuadraticAlgebraClassNumberModel.ordinaryClassNumber D =
      rationalQuadraticAlgebraClassNumberAtPositiveFundamentalDiscriminant D hD := by
  simp [rationalQuadraticAlgebraClassNumberModel, hD]

theorem rationalQuadraticAlgebraClassNumberModel_form_eq
    {D : ℕ} (hD : PositiveFundamentalDiscriminant D) :
    rationalQuadraticAlgebraClassNumberModel.formClassNumber D =
      rationalQuadraticAlgebraClassNumberAtPositiveFundamentalDiscriminant D hD := by
  simp [rationalQuadraticAlgebraClassNumberModel, hD]

end

end PellPaper
