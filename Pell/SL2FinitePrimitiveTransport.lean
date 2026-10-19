import Pell.PrimitiveSourceLinearFibre
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.Real.Basic

/-!
# Finite primitive targets in actual determinant-one inverse coordinates

The finite image uses the inverse of the actual integer linear equivalence.
Thus cardinality, recovery and primitivity are retained without supplied
injectivity or coordinate certificates. A strict second-coordinate width
below one forces a primitive family onto the integer axis, which has at most
two points. Width one and nonprimitive families are not covered by that bound.
-/

namespace PellPaper
open scoped MatrixGroups

/-- The finite target family in the genuine inverse coordinates of `W`. -/
def sl2InverseTargetImage (W : SL(2, ℤ)) (T : Finset (Fin 2 → ℤ)) :
    Finset (Fin 2 → ℤ) :=
  T.map W.toLin'.symm.toEmbedding

@[simp]
theorem card_sl2InverseTargetImage (W : SL(2, ℤ)) (T : Finset (Fin 2 → ℤ)) :
    (sl2InverseTargetImage W T).card = T.card := by
  exact Finset.card_map _

/-- Exact recovery of original target membership from inverse coordinates. -/
@[simp]
theorem mem_sl2InverseTargetImage_iff (W : SL(2, ℤ))
    (T : Finset (Fin 2 → ℤ)) (x : Fin 2 → ℤ) :
    x ∈ sl2InverseTargetImage W T ↔ W.toLin' x ∈ T := by
  change x ∈ T.map W.toLin'.symm.toEquiv.toEmbedding ↔ _
  exact Finset.mem_map_equiv

/-- Integral determinant-one inverse coordinates preserve primitive vectors. -/
theorem isCoprime_sl2_inverse_coordinates (W : SL(2, ℤ))
    (v : Fin 2 → ℤ) (hv : IsCoprime (v 0) (v 1)) :
    IsCoprime (W.toLin'.symm v 0) (W.toLin'.symm v 1) := by
  exact hv.mulVecSL W⁻¹

/-- Every point of the inverse image is primitive if the original targets are. -/
theorem primitive_sl2InverseTargetImage (W : SL(2, ℤ))
    (T : Finset (Fin 2 → ℤ))
    (hT : ∀ v ∈ T, IsCoprime (v 0) (v 1)) :
    ∀ x ∈ sl2InverseTargetImage W T, IsCoprime (x 0) (x 1) := by
  intro x hx
  obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hx
  exact isCoprime_sl2_inverse_coordinates W v (hT v hv)

/-- A real absolute-value bound strictly below one forces an integer to zero.
No nonnegative-width hypothesis is needed; negative widths have no inputs. -/
theorem int_eq_zero_of_abs_cast_le_lt_one (a : ℤ) (B : ℝ)
    (ha : |(a : ℝ)| ≤ B) (hB : B < 1) : a = 0 := by
  have hlt : |(a : ℝ)| < 1 := ha.trans_lt hB
  have habs : |a| < 1 := by exact_mod_cast hlt
  have hbounds := abs_lt.mp habs
  omega

/-- A primitive finite target family with inverse second-coordinate width
strictly below one contains at most two targets. This counts distinct target
vectors, not another family projecting to them. -/
theorem card_targets_le_two_of_sl2_inverse_thin (W : SL(2, ℤ))
    (T : Finset (Fin 2 → ℤ)) (B : ℝ)
    (hT : ∀ v ∈ T, IsCoprime (v 0) (v 1))
    (hwidth : ∀ v ∈ T, |((W.toLin'.symm v 1 : ℤ) : ℝ)| ≤ B)
    (hB : B < 1) : T.card ≤ 2 := by
  rw [← card_sl2InverseTargetImage W T]
  apply card_primitive_linear_solutions_le_two 0 1 (by simp)
  intro x hx
  refine ⟨primitive_sl2InverseTargetImage W T hT x hx, ?_⟩
  obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hx
  have hz := int_eq_zero_of_abs_cast_le_lt_one (W.toLin'.symm v 1) B
    (hwidth v hv) hB
  change W.toLin'.symm v 0 * 0 + W.toLin'.symm v 1 * 1 = 0
  simpa only [mul_zero, mul_one, zero_add] using hz

end PellPaper
