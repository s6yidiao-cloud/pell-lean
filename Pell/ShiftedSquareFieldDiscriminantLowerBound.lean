import Pell.ShiftedSquareFieldDiscriminantBound
import Pell.ShiftedSquareSurfaceForm
import Mathlib.Tactic

/-!
# The lower field-discriminant comparison for squarefree shifted radicands

The existing exact index-square identity says that `-4*a` is an integral
square times the field discriminant.  Squarefreeness of `a` forces that
index to divide two, yielding the reverse comparison

`|a| <= |discr Q(sqrt(-a))|`.

This isolated candidate contains no coordinate or counting assertion.
-/

namespace PellPaper

noncomputable section

local instance shiftedSquareFieldDiscriminantLowerBound_numberField (a : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

/-- For a signed squarefree radicand, its absolute value is at most the
absolute field discriminant of the associated quadratic algebra. -/
theorem abs_le_abs_rationalQuadraticAlgebra_neg_fieldDiscriminant_of_squarefree
    (a : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (ha : Squarefree a) :
    |a| ≤ |NumberField.discr (rationalQuadraticAlgebra (-a))| := by
  obtain ⟨c, hc0, hchange⟩ :=
    exists_nonzero_sq_mul_rationalQuadraticAlgebra_neg_fieldDiscriminant_eq a
  have ha0 : a ≠ 0 := by
    intro ha0
    have hnoRoot :=
      Fact.out (p := rationalQuadraticAlgebraNoRationalRoot (-a)) 0
    apply hnoRoot
    simp [ha0]
  have haAbsPos : 0 < a.natAbs := Int.natAbs_pos.mpr ha0
  have hcD : c ^ 2 ∣ -4 * a := ⟨_, hchange⟩
  have hcDnat : c.natAbs ^ 2 ∣ a.natAbs * 2 ^ 2 := by
    have h := Int.natAbs_dvd_natAbs.mpr hcD
    simp only [Int.natAbs_pow, Int.natAbs_mul, Int.natAbs_neg] at h
    norm_num at h ⊢
    simpa only [Nat.mul_comm] using h
  have hcDvdTwo : c.natAbs ∣ 2 :=
    dvd_of_sq_dvd_squarefree_mul_sq haAbsPos
      (Int.squarefree_natAbs.mpr ha) hcDnat
  have hcLeTwo : c.natAbs ≤ 2 :=
    Nat.le_of_dvd (by decide) hcDvdTwo
  have hcSqLeFour : c.natAbs ^ 2 ≤ 4 := by
    simpa using Nat.pow_le_pow_left hcLeTwo 2
  have habsEquality :
      4 * a.natAbs = c.natAbs ^ 2 *
        (NumberField.discr (rationalQuadraticAlgebra (-a))).natAbs := by
    have h := congrArg Int.natAbs hchange
    simp only [Int.natAbs_mul, Int.natAbs_neg, Int.natAbs_pow] at h
    norm_num at h ⊢
    simpa only [Nat.mul_comm] using h
  have hfour :
      4 * a.natAbs ≤
        4 * (NumberField.discr (rationalQuadraticAlgebra (-a))).natAbs := by
    calc
      4 * a.natAbs = c.natAbs ^ 2 *
          (NumberField.discr (rationalQuadraticAlgebra (-a))).natAbs :=
        habsEquality
      _ ≤ 4 * (NumberField.discr
          (rationalQuadraticAlgebra (-a))).natAbs := by
        exact Nat.mul_le_mul_right _ hcSqLeFour
  have hnat : a.natAbs ≤
      (NumberField.discr (rationalQuadraticAlgebra (-a))).natAbs := by
    omega
  have hcast : (a.natAbs : ℤ) ≤
      ((NumberField.discr
        (rationalQuadraticAlgebra (-a))).natAbs : ℤ) := by
    exact_mod_cast hnat
  simpa only [Int.natCast_natAbs] using hcast

end

end PellPaper
