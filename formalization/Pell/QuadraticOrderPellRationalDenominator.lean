import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-!
# A squarefree denominator lemma for quadratic coordinates

The elementary arithmetic fact in this file is the denominator calculation
needed when identifying the integral closure of a squarefree quadratic
algebra.  If `D` is squarefree and `D * q^2` is an integer for a rational
number `q`, then `q` is already an integer.

The proof works directly with the reduced numerator and denominator supplied
by `Rat`: its denominator square divides `D`, and squarefreeness forces that
denominator to be a unit.  This is independent of any choice of quadratic
ring of integers.
-/

namespace PellPaper

/-- A rational number whose square becomes integral after multiplication by
a squarefree natural number has no nontrivial denominator. -/
theorem rat_eq_int_of_squarefree_mul_sq_eq_int
    {D : ℕ} (hD : Squarefree D) (q : ℚ)
    (h : ∃ z : ℤ, (D : ℚ) * q ^ 2 = (z : ℚ)) :
    ∃ a : ℤ, (a : ℚ) = q := by
  obtain ⟨z, hz⟩ := h
  have hdiv : q.den ^ 2 ∣ D * q.num.natAbs ^ 2 := by
    have hEq : (D : ℤ) * q.num ^ 2 = z * q.den ^ 2 := by
      rw [← Rat.num_div_den q] at hz
      field_simp at hz
      have h' : (D : ℤ) * q.num ^ 2 = (q.den : ℤ) ^ 2 * z := by
        exact_mod_cast hz
      simpa [mul_comm] using h'
    have hdivZ : ((q.den : ℤ) ^ 2) ∣ (D : ℤ) * q.num ^ 2 := by
      refine ⟨z, ?_⟩
      simpa [mul_comm] using hEq
    have habs := Int.natAbs_dvd_natAbs.mpr hdivZ
    simpa [Int.natAbs_mul, Int.natAbs_pow] using habs
  have hcop : (q.den ^ 2).Coprime (q.num.natAbs ^ 2) :=
    q.reduced.symm.pow 2 2
  have hdenSq : q.den ^ 2 ∣ D :=
    (hcop.dvd_mul_right).mp hdiv
  have hunit : IsUnit q.den := hD q.den (by simpa [pow_two] using hdenSq)
  have hden : q.den = 1 := Nat.isUnit_iff.mp hunit
  exact ⟨q.num, Rat.coe_int_num_of_den_eq_one hden⟩

end PellPaper
