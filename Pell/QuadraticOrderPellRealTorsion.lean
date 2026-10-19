import Pell.QuadraticOrderPellFundamentalUnitComparison
import Mathlib.Analysis.Normed.Ring.Finite

/-!
# Torsion rigidity at the positive real place of a quadratic order

For a positive nonsquare radicand, the concrete real embedding of the maximal
order is injective.  A torsion unit maps to a finite-order real unit, hence to
`1` or `-1`; injectivity then identifies the original unit with `1` or `-1`.

This is only the torsion part of the fundamental-unit story.  It does not
construct a positive generator for the nontorsion quotient or establish the
unit rank.
-/

namespace PellPaper

noncomputable section

/-- A finite-order real number is one of the two real roots of unity. -/
theorem real_eq_one_or_neg_one_of_isOfFinOrder
    (x : ℝ) (hx : IsOfFinOrder x) : x = 1 ∨ x = -1 := by
  have hnorm : ‖x‖ = 1 := hx.norm_eq_one
  rw [Real.norm_eq_abs, abs_eq (zero_le_one : (0 : ℝ) ≤ 1)] at hnorm
  exact hnorm

/-- The concrete positive real embedding of the quadratic algebra is
injective when the algebra is a field. -/
theorem rationalQuadraticAlgebraRealEmbedding_injective
    (d : ℤ) (hd : 0 ≤ d) [Fact (rationalQuadraticAlgebraNoRationalRoot d)] :
    Function.Injective (rationalQuadraticAlgebraRealEmbedding d hd) := by
  exact RingHom.injective (rationalQuadraticAlgebraRealEmbedding d hd).toRingHom

/-- Restricting the concrete real embedding to the maximal order remains
injective. -/
theorem quadraticOrderPellRealEval_injective
    (d : ℤ) (hd : 0 ≤ d) [Fact (rationalQuadraticAlgebraNoRationalRoot d)] :
    Function.Injective (quadraticOrderPellRealEval d hd) := by
  intro x y hxy
  apply NumberField.RingOfIntegers.ext
  apply rationalQuadraticAlgebraRealEmbedding_injective d hd
  simpa [quadraticOrderPellRealEval] using hxy

/-- A finite-order maximal-order unit has real value `1` or `-1` under the
concrete positive embedding. -/
theorem quadraticOrderPellRealEval_eq_one_or_neg_one_of_isOfFinOrder
    (d : ℤ) (hd : 0 ≤ d) [Fact (rationalQuadraticAlgebraNoRationalRoot d)]
    (u : (NumberField.RingOfIntegers (rationalQuadraticAlgebra d))ˣ)
    (hu : IsOfFinOrder u) :
    quadraticOrderPellRealEval d hd (u : NumberField.RingOfIntegers
      (rationalQuadraticAlgebra d)) = 1 ∨
    quadraticOrderPellRealEval d hd (u : NumberField.RingOfIntegers
      (rationalQuadraticAlgebra d)) = -1 := by
  let evalUnits : (NumberField.RingOfIntegers (rationalQuadraticAlgebra d))ˣ →* ℝˣ :=
    Units.map (quadraticOrderPellRealEval d hd).toMonoidHom
  have hfinite : IsOfFinOrder (evalUnits u) := evalUnits.isOfFinOrder hu
  have hfinite_val : IsOfFinOrder ((evalUnits u : ℝˣ) : ℝ) :=
    Units.isOfFinOrder_val.mpr hfinite
  have hroot := real_eq_one_or_neg_one_of_isOfFinOrder ((evalUnits u : ℝˣ) : ℝ)
    hfinite_val
  simpa [evalUnits] using hroot

/-- The concrete real embedding detects torsion units: every finite-order
maximal-order unit is literally `1` or `-1`. -/
theorem quadraticOrderPellUnit_eq_one_or_neg_one_of_isOfFinOrder
    (d : ℤ) (hd : 0 ≤ d) [Fact (rationalQuadraticAlgebraNoRationalRoot d)]
    (u : (NumberField.RingOfIntegers (rationalQuadraticAlgebra d))ˣ)
    (hu : IsOfFinOrder u) : u = 1 ∨ u = -1 := by
  rcases quadraticOrderPellRealEval_eq_one_or_neg_one_of_isOfFinOrder d hd u hu with h | h
  · left
    apply Units.ext
    apply quadraticOrderPellRealEval_injective d hd
    simpa using h
  · right
    apply Units.ext
    apply quadraticOrderPellRealEval_injective d hd
    simpa using h

/-- Membership in the ordinary commutative-group torsion subgroup is enough
for the preceding rigidity theorem. -/
theorem quadraticOrderPellUnit_eq_one_or_neg_one_of_mem_torsion
    (d : ℤ) (hd : 0 ≤ d) [Fact (rationalQuadraticAlgebraNoRationalRoot d)]
    (u : (NumberField.RingOfIntegers (rationalQuadraticAlgebra d))ˣ)
    (hu : u ∈ CommGroup.torsion
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra d))ˣ) :
    u = 1 ∨ u = -1 := by
  apply quadraticOrderPellUnit_eq_one_or_neg_one_of_isOfFinOrder d hd u
  exact (CommGroup.mem_torsion u).mp hu

/-- Positive fundamental discriminants provide the nonnegative radicand
needed by the concrete real embedding. -/
theorem quadraticOrderPellUnit_eq_one_or_neg_one_of_mem_torsion_at_positiveFundamentalDiscriminant
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ))]
    (u : (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ)))ˣ)
    (hu : u ∈ CommGroup.torsion
      (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ)) )ˣ) :
    u = 1 ∨ u = -1 := by
  exact quadraticOrderPellUnit_eq_one_or_neg_one_of_mem_torsion (D : ℤ)
    (int_pos_of_positiveFundamentalDiscriminant hD).le u hu

end

end PellPaper
