import Pell.ClassAverage
import Pell.Definitions

/-!
# From positive fundamental discriminants to Pell parameters

The class-number side of the paper is indexed by positive fundamental
discriminants, while the Pell API is indexed by positive nonsquare integers.
This file verifies the elementary bridge between those two indexing conditions.
It deliberately does not identify a discriminant with a quadratic field or use
any class-number formula.
-/

namespace PellPaper

/-- A positive fundamental discriminant is positive as a natural number. -/
theorem positive_of_positiveFundamentalDiscriminant {D : ℕ}
    (hD : PositiveFundamentalDiscriminant D) : 0 < D := by
  rcases hD with ⟨hD_gt, _⟩
  omega

/-- The same positivity statement in the integer type used by `Pell.Solution₁`. -/
theorem int_pos_of_positiveFundamentalDiscriminant {D : ℕ}
    (hD : PositiveFundamentalDiscriminant D) : 0 < (D : ℤ) := by
  exact_mod_cast positive_of_positiveFundamentalDiscriminant hD

/-- A squarefree natural square is equal to one. -/
private theorem squarefree_eq_one_of_isSquare {n : ℕ} (hn : Squarefree n)
    (hsq : IsSquare n) : n = 1 := by
  obtain ⟨k, hk⟩ := hsq
  have hk_unit : IsUnit k := hn k (by rw [hk])
  calc
    n = k * k := hk
    _ = 1 := by simp [Nat.isUnit_iff.mp hk_unit]

/-- If `4 * d` is a natural square, then so is `d`.

The point is that a square root of a multiple of four is even; cancellation of
the resulting factor four produces a square root of `d`. -/
private theorem isSquare_of_four_mul_isSquare {d : ℕ}
    (hsq : IsSquare (4 * d)) : IsSquare d := by
  obtain ⟨k, hk⟩ := hsq
  have htwo_sq : 2 ∣ k ^ 2 := by
    rw [pow_two, ← hk]
    exact ⟨2 * d, by ring⟩
  obtain ⟨t, ht⟩ := Nat.prime_two.dvd_of_dvd_pow htwo_sq
  refine ⟨t, ?_⟩
  apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < 4)
  calc
    4 * d = k * k := hk
    _ = 4 * (t * t) := by rw [ht]; ring

/-- The `d ≡ 2, 3 (mod 4)` branch in the fundamental-discriminant
characterization is nonsquare. -/
private theorem not_isSquare_of_squarefree_mod_four {d : ℕ} (hd_sqfree : Squarefree d)
    (hd_mod : d % 4 = 2 ∨ d % 4 = 3) : ¬ IsSquare d := by
  intro hsq
  have hd_one := squarefree_eq_one_of_isSquare hd_sqfree hsq
  rcases hd_mod with hd_mod | hd_mod <;> omega

/-- Every positive fundamental discriminant is nonsquare as a natural number.

The odd branch is squarefree and greater than one.  In the `4d` branch, a
putative square would make `d` square; squarefreeness would then force `d = 1`,
contradicting its residue class modulo four. -/
theorem not_isSquare_of_positiveFundamentalDiscriminant {D : ℕ}
    (hD : PositiveFundamentalDiscriminant D) : ¬ IsSquare D := by
  rcases hD with ⟨hD_gt, hodd | heven⟩
  · intro hsq
    have hD_one := squarefree_eq_one_of_isSquare hodd.1 hsq
    omega
  · obtain ⟨d, rfl, hd_sqfree, hd_mod⟩ := heven
    intro hsq
    exact not_isSquare_of_squarefree_mod_four hd_sqfree hd_mod
      (isSquare_of_four_mul_isSquare hsq)

/-- The integer Pell radicand attached to a positive fundamental discriminant
is nonsquare. -/
theorem int_not_isSquare_of_positiveFundamentalDiscriminant {D : ℕ}
    (hD : PositiveFundamentalDiscriminant D) : ¬ IsSquare (D : ℤ) := by
  simpa only [Int.isSquare_natCast_iff] using
    not_isSquare_of_positiveFundamentalDiscriminant hD

/-- A positive fundamental discriminant has its unique positive fundamental
Pell solution. -/
theorem existsUnique_isFundamental_of_positiveFundamentalDiscriminant {D : ℕ}
    (hD : PositiveFundamentalDiscriminant D) :
    ∃! a : Pell.Solution₁ (D : ℤ), Pell.IsFundamental a := by
  exact existsUnique_isFundamental_iff.mpr
    ⟨int_pos_of_positiveFundamentalDiscriminant hD,
      int_not_isSquare_of_positiveFundamentalDiscriminant hD⟩

end PellPaper
