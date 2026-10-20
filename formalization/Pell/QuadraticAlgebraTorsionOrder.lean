import Pell.QuadraticOrderPellRealTorsion
import Mathlib.NumberTheory.NumberField.Units.Basic

/-!
# Torsion order of the concrete real quadratic field

The real-place torsion rigidity already proves that every finite-order unit
of the concrete positive real quadratic field is `1` or `-1`.  This module
converts that elementwise statement into the exact torsion order needed by
Mathlib's Dedekind-zeta class-number formula.
-/

namespace PellPaper

noncomputable section

open NumberField

local instance rationalQuadraticAlgebra_torsionOrder_numberField_instance (d : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot d)] :
    NumberField (rationalQuadraticAlgebra d) :=
  rationalQuadraticAlgebra_numberField d

/-- A positive fundamental discriminant gives a real quadratic field with
exactly the two torsion units `1` and `-1`. -/
theorem rationalQuadraticAlgebra_torsionOrder_eq_two_at_positiveFundamentalDiscriminant
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ))] :
    NumberField.Units.torsionOrder (rationalQuadraticAlgebra (D : ℤ)) = 2 := by
  classical
  let _ := Fintype.ofFinite
    (NumberField.Units.torsion (rationalQuadraticAlgebra (D : ℤ)))
  rw [NumberField.Units.torsionOrder, Nat.card_eq_fintype_card]
  refine Finset.card_eq_two.2 ⟨1,
    ⟨-1, neg_one_mem_torsion⟩,
    by simp [← Subtype.coe_ne_coe],
    Finset.ext fun x => ⟨fun _ => ?_, fun _ => Finset.mem_univ _⟩⟩
  rw [Finset.mem_insert, Finset.mem_singleton, ← Subtype.val_inj, ← Subtype.val_inj]
  exact quadraticOrderPellUnit_eq_one_or_neg_one_of_mem_torsion_at_positiveFundamentalDiscriminant
    D hD x x.2

end

end PellPaper
