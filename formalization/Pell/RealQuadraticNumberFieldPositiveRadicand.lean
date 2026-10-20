import Pell.QuadraticNumberFieldSquareGenerator
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic

/-!
# Positive rational and integral radicands for real quadratic number fields

An explicit real embedding of a degree-two number field forces the
nonsquare rational radicand from its actual quadratic-algebra presentation
to be positive.  Clearing its denominator by a square yields an actual
presentation with positive integer radicand.

The integer radicand here is not asserted squarefree or fundamental.  This
module does not classify the integral basis or field discriminant.
-/

namespace PellPaper

noncomputable section

/-- Rescaling the quadratic generator by a nonzero rational gives an actual
algebra equivalence, including for radicands which are not nonsquares. -/
def quadraticAlgebraScaleAlgEquiv (a s : ℚ) (hs : s ≠ 0) :
    QuadraticAlgebra ℚ (a * s ^ 2) 0 ≃ₐ[ℚ] QuadraticAlgebra ℚ a 0 where
  toFun z := ⟨z.re, s * z.im⟩
  invFun z := ⟨z.re, z.im / s⟩
  left_inv z := by
    ext <;> simp
    field_simp [hs]
  right_inv z := by
    ext <;> simp
    field_simp [hs]
  map_mul' z w := by
    ext <;> simp <;> ring
  map_add' z w := by
    ext <;> simp
    ring
  commutes' r := by
    ext <;> simp

/-- A real embedding forces positivity of any nonsquare rational radicand
in an actual rational-algebra presentation of the field. -/
theorem rationalQuadraticRadicand_pos_of_realEmbedding
    (K : Type*) [Field K] [NumberField K] (σ : K →+* ℝ)
    (a : ℚ) (hns : ∀ r : ℚ, r ^ 2 ≠ a)
    (e : K ≃ₐ[ℚ] QuadraticAlgebra ℚ a 0) : 0 < a := by
  let x := e.symm (QuadraticAlgebra.omega : QuadraticAlgebra ℚ a 0)
  have hω : (QuadraticAlgebra.omega : QuadraticAlgebra ℚ a 0) ^ 2 =
      algebraMap ℚ (QuadraticAlgebra ℚ a 0) a := by
    rw [pow_two, QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
    simp
  have hsq : x ^ 2 = algebraMap ℚ K a := by
    dsimp [x]
    rw [← map_pow, hω, e.symm.commutes]
  have hreal := congrArg σ hsq
  simp only [map_pow] at hreal
  change (σ x) ^ 2 = σ (a : K) at hreal
  rw [map_ratCast] at hreal
  have ha0 : a ≠ 0 := by
    intro h
    exact hns 0 (by simp [h])
  have haR0 : (a : ℝ) ≠ 0 := by exact_mod_cast ha0
  have haRnonneg : (0 : ℝ) ≤ a := by
    rw [← hreal]
    exact sq_nonneg _
  exact_mod_cast (lt_of_le_of_ne haRnonneg haR0.symm)

/-- A degree-two number field with an actual real embedding has a positive
nonsquare rational radicand, with no supplied generator hypothesis. -/
theorem exists_realQuadraticNumberField_positive_rational_radicand
    (K : Type*) [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2)
    (σ : K →+* ℝ) :
    ∃ a : ℚ, 0 < a ∧ (∀ r : ℚ, r ^ 2 ≠ a) ∧
      Nonempty (K ≃ₐ[ℚ] QuadraticAlgebra ℚ a 0) := by
  obtain ⟨a, hns, ⟨e⟩⟩ := exists_quadraticNumberField_quadraticAlgebra_algEquiv K hK
  exact ⟨a, rationalQuadraticRadicand_pos_of_realEmbedding K σ a hns e, hns, ⟨e⟩⟩

/-- Clearing the denominator gives an actual presentation with positive
integer radicand.  No squarefree or fundamental-discriminant claim is made. -/
theorem exists_realQuadraticNumberField_positive_integer_radicand
    (K : Type*) [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2)
    (σ : K →+* ℝ) :
    ∃ d : ℤ, 0 < d ∧ (∀ r : ℚ, r ^ 2 ≠ (d : ℚ)) ∧
      Nonempty (K ≃ₐ[ℚ] QuadraticAlgebra ℚ (d : ℚ) 0) := by
  obtain ⟨a, ha, hns, ⟨e⟩⟩ :=
    exists_realQuadraticNumberField_positive_rational_radicand K hK σ
  let d : ℤ := a.num * a.den
  have hd : 0 < d := mul_pos (Rat.num_pos.mpr ha) (by exact_mod_cast a.den_pos)
  have hq : (a.den : ℚ) ≠ 0 := by exact_mod_cast a.den_ne_zero
  have hn : (a.num : ℚ) = a * (a.den : ℚ) := (div_eq_iff hq).mp a.num_div_den
  have hdq : (d : ℚ) = a * (a.den : ℚ) ^ 2 := by
    dsimp [d]
    simp only [Int.cast_mul, Int.cast_natCast]
    rw [hn]
    ring
  have hdns : ∀ r : ℚ, r ^ 2 ≠ (d : ℚ) := by
    intro r hr
    apply hns (r / a.den)
    rw [div_pow, div_eq_iff (pow_ne_zero 2 hq)]
    exact hr.trans hdq
  refine ⟨d, hd, hdns, ?_⟩
  rw [hdq]
  exact ⟨e.trans (quadraticAlgebraScaleAlgEquiv a a.den hq).symm⟩

end
end PellPaper
