import Pell.LinearDirichletRectangleBound
import Pell.JacobiDirichletCharacterNonprincipal
import Mathlib.Tactic

/-!
# Linear Jacobi sums on integer-shifted rectangles

This file specializes the generic nonprincipal Dirichlet-character rectangle
bound to the actual numerator-Jacobi character of a positive odd nonsquare
modulus.  The offsets and coefficients are literal integers; reduction
modulo the modulus is discharged internally.
-/

open scoped BigOperators

namespace PellPaper

noncomputable section

private theorem jacobiDirichletCharacterC_apply_intCast
    (q : ℕ) [NeZero q] [Fact (1 < q)] (z : ℤ) :
    jacobiDirichletCharacterC q (z : ZMod q) = (jacobiSym z q : ℂ) := by
  rw [jacobiDirichletCharacterC, MulChar.ringHomComp_apply]
  change (jacobiSym ((z : ZMod q).val : ℤ) q : ℂ) = _
  rw [ZMod.val_intCast]
  exact_mod_cast (jacobiSym.mod_left z q).symm

/-- A literal integer linear form summed over a shifted range rectangle has
the Pólya--Vinogradov rectangle bound when its positive odd modulus is
nonsquare and at least one coefficient is a unit modulo that modulus.
Empty rectangles, long ranges, and negative integer offsets are included. -/
theorem abs_sum_jacobiSym_linear_shifted_rectangle_le
    (q : ℕ) (hq : 0 < q) (hodd : Odd q) (hns : ¬ IsSquare q)
    (a b x0 y0 : ℤ) (L1 L2 S : ℕ)
    (hunit : IsUnit (a : ZMod q) ∨ IsUnit (b : ZMod q))
    (hL1 : L1 ≤ S) (hL2 : L2 ≤ S) :
    |∑ x ∈ Finset.range L1, ∑ y ∈ Finset.range L2,
        (jacobiSym
          (a * ((x : ℤ) + x0) + b * ((y : ℤ) + y0)) q : ℝ)| ≤
      4 * (S : ℝ) * Real.sqrt (q : ℝ) *
        (1 + Real.log (q : ℝ)) := by
  have hq1 : 1 < q := by
    have hqne : q ≠ 1 := by
      intro h
      exact hns (h ▸ IsSquare.one)
    omega
  let _ : NeZero q := ⟨hq.ne'⟩
  let _ : Fact (1 < q) := ⟨hq1⟩
  let chi : DirichletCharacter ℂ q := jacobiDirichletCharacterC q
  have hchi : chi ≠ 1 :=
    jacobiDirichletCharacterC_ne_one_of_odd_not_isSquare q hq hodd hns
  have hbound := nonprincipalDirichletCharacter_linear_shifted_rectangle_norm_le
    chi hchi (a : ZMod q) (b : ZMod q) (x0 : ZMod q) (y0 : ZMod q)
      L1 L2 S hunit hL1 hL2
  have hterm (x y : ℕ) :
      chi ((a : ZMod q) * ((x : ZMod q) + (x0 : ZMod q)) +
        (b : ZMod q) * ((y : ZMod q) + (y0 : ZMod q))) =
        (jacobiSym
          (a * ((x : ℤ) + x0) + b * ((y : ℤ) + y0)) q : ℂ) := by
    change jacobiDirichletCharacterC q _ = _
    rw [show (a : ZMod q) * ((x : ZMod q) + (x0 : ZMod q)) +
          (b : ZMod q) * ((y : ZMod q) + (y0 : ZMod q)) =
        (a * ((x : ℤ) + x0) + b * ((y : ℤ) + y0) : ℤ) by
          push_cast
          ring]
    exact jacobiDirichletCharacterC_apply_intCast q _
  have hsum :
      (∑ x ∈ Finset.range L1, ∑ y ∈ Finset.range L2,
        chi ((a : ZMod q) * ((x : ZMod q) + (x0 : ZMod q)) +
          (b : ZMod q) * ((y : ZMod q) + (y0 : ZMod q)))) =
        ((∑ x ∈ Finset.range L1, ∑ y ∈ Finset.range L2,
          (jacobiSym
            (a * ((x : ℤ) + x0) + b * ((y : ℤ) + y0)) q : ℝ) : ℝ) : ℂ) := by
    push_cast
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    rw [hterm]
  rw [hsum, Complex.norm_real] at hbound
  simpa only [Real.norm_eq_abs] using hbound

end
end PellPaper
