import Pell.Definitions
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Data.Int.GCD
import Mathlib.Algebra.Squarefree.Basic

/-!
# The elementary factorization of a Pell solution

The dyadic factorization in `main.tex` starts with the two integer factors
`x - 1` and `x + 1`.  This file records their product, positivity, and common
divisors before any square parts are separated.
-/

namespace PellPaper

/-- Factoring `x² - 1` in the integer Pell equation.  No positivity hypothesis
is needed for this identity. -/
theorem pell_factorization {d : ℤ} (a : Pell.Solution₁ d) :
    (a.x - 1) * (a.x + 1) = d * a.y ^ 2 := by
  nlinarith [a.prop]

/-- The coordinates of every integer Pell solution are relatively prime. -/
theorem pell_coordinates_gcd_eq_one {d : ℤ} (a : Pell.Solution₁ d) :
    Int.gcd a.x a.y = 1 := by
  apply Int.gcd_eq_one_iff.mpr
  intro c hx hy
  rw [← a.prop, pow_two, pow_two]
  exact dvd_sub (dvd_mul_of_dvd_left hx a.x)
    (dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hy a.y) d)

/-- The only possible common prime divisor of `x - 1` and `x + 1` is `2`.
Here `Int.gcd` takes values in `ℕ`, including for signed coordinates. -/
theorem pell_factors_gcd_dvd_two {d : ℤ} (a : Pell.Solution₁ d) :
    Int.gcd (a.x - 1) (a.x + 1) ∣ 2 := by
  exact Int.gcd_dvd_iff.mpr ⟨-1, 1, by ring⟩

/-- If `x` is even, the two unhalved factors are coprime. -/
theorem pell_factors_gcd_eq_one_of_even {d : ℤ} (a : Pell.Solution₁ d)
    (hx : Even a.x) : Int.gcd (a.x - 1) (a.x + 1) = 1 := by
  rcases (Nat.dvd_prime Nat.prime_two).mp (pell_factors_gcd_dvd_two a) with h | h
  · exact h
  · have hminus := Int.gcd_dvd_left (a.x - 1) (a.x + 1)
    rw [h] at hminus
    have hone : (2 : ℤ) ∣ 1 := by
      simpa using dvd_sub (even_iff_two_dvd.mp hx) hminus
    norm_num at hone

/-- If `x` is odd, the unhalved factors have gcd exactly `2`. -/
theorem pell_factors_gcd_eq_two_of_odd {d : ℤ} (a : Pell.Solution₁ d)
    (hx : Odd a.x) : Int.gcd (a.x - 1) (a.x + 1) = 2 := by
  apply Nat.dvd_antisymm (pell_factors_gcd_dvd_two a)
  apply Int.dvd_gcd
  · exact even_iff_two_dvd.mp (even_sub_one.mpr hx)
  · exact even_iff_two_dvd.mp (even_add_one.mpr hx)

/-- An even first coordinate forces both the radicand and second coordinate
to be odd, as in the even branch of the dyadic factorization. -/
theorem pell_odd_radicand_and_y_of_even_x {d : ℤ} (a : Pell.Solution₁ d)
    (hx : Even a.x) : Odd d ∧ Odd a.y := by
  have hp : Odd (d * a.y ^ 2) := by
    rw [a.prop_y]
    exact odd_sub_one.mpr (Int.even_pow.mpr ⟨hx, by decide⟩)
  simpa only [Int.odd_mul, Int.odd_pow, OfNat.ofNat_ne_zero, or_false] using hp

/-- For squarefree integer radicands, an odd first coordinate forces an even
second coordinate.  Squarefreeness is essential in this branch. -/
theorem pell_even_y_of_odd_x_of_squarefree {d : ℤ} (a : Pell.Solution₁ d)
    (hd : Squarefree d) (hx : Odd a.x) : Even a.y := by
  by_contra hy
  obtain ⟨k, hk⟩ := hx
  obtain ⟨l, hl⟩ := Int.not_even_iff_odd.mp hy
  have hp := a.prop
  rw [hk, hl] at hp
  have hfour : (2 : ℤ) * 2 ∣ d := by
    refine ⟨k * (k + 1) - d * l * (l + 1), ?_⟩
    nlinarith [hp]
  have hu := hd 2 hfour
  norm_num [Int.isUnit_iff] at hu

/-- The halved factors are consecutive integers.  Integer division makes this
identity valid even without a parity assumption. -/
theorem pell_half_factors_difference {d : ℤ} (a : Pell.Solution₁ d) :
    (a.x + 1) / 2 - (a.x - 1) / 2 = 1 := by
  omega

/-- In particular, the two halved factors are coprime. -/
theorem pell_half_factors_gcd_eq_one {d : ℤ} (a : Pell.Solution₁ d) :
    Int.gcd ((a.x - 1) / 2) ((a.x + 1) / 2) = 1 := by
  apply Int.gcd_eq_one_iff.mpr
  intro c hm hp
  simpa only [pell_half_factors_difference a] using dvd_sub hp hm

/-- In the odd branch, halving the two factors removes exactly a factor of
four from their product. -/
theorem pell_half_factorization_mul_four {d : ℤ} (a : Pell.Solution₁ d)
    (hx : Odd a.x) :
    4 * ((a.x - 1) / 2) * ((a.x + 1) / 2) = d * a.y ^ 2 := by
  have hm := Int.ediv_mul_cancel (even_iff_two_dvd.mp (even_sub_one.mpr hx))
  have hp := Int.ediv_mul_cancel (even_iff_two_dvd.mp (even_add_one.mpr hx))
  calc
    4 * ((a.x - 1) / 2) * ((a.x + 1) / 2) =
        (((a.x - 1) / 2) * 2) * (((a.x + 1) / 2) * 2) := by ring
    _ = (a.x - 1) * (a.x + 1) := by rw [hm, hp]
    _ = d * a.y ^ 2 := pell_factorization a

/-- The squarefree odd branch has the exact product used in the manuscript. -/
theorem pell_half_factorization_of_squarefree {d : ℤ} (a : Pell.Solution₁ d)
    (hd : Squarefree d) (hx : Odd a.x) :
    ((a.x - 1) / 2) * ((a.x + 1) / 2) = d * (a.y / 2) ^ 2 := by
  have hy := Int.ediv_mul_cancel
    (even_iff_two_dvd.mp (pell_even_y_of_odd_x_of_squarefree a hd hx))
  have hp := pell_half_factorization_mul_four a hx
  rw [← hy] at hp
  nlinarith [hp]

/-- Positive Pell coordinates give positive halved factors in the odd branch. -/
theorem pell_half_factors_pos {d : ℤ} (a : Pell.Solution₁ d)
    (hpos : 1 < a.x) (hx : Odd a.x) :
    0 < (a.x - 1) / 2 ∧ 0 < (a.x + 1) / 2 := by
  obtain ⟨k, hk⟩ := hx
  omega

/-- The two factors and the second coordinate are positive for a fundamental
solution. -/
theorem pell_factors_pos_of_isFundamental {d : ℤ} {a : Pell.Solution₁ d}
    (ha : Pell.IsFundamental a) : 0 < a.x - 1 ∧ 0 < a.x + 1 ∧ 0 < a.y := by
  have hx := ha.1
  exact ⟨by omega, by omega, ha.2.1⟩

/-- Natural coordinates retain the exact factorization when the solution has
positive coordinates. -/
theorem pell_factorization_nat {m : ℕ} (a : Pell.Solution₁ (m : ℤ))
    (hx : 1 < a.x) (hy : 0 ≤ a.y) :
    (a.x.toNat - 1) * (a.x.toNat + 1) = m * a.y.toNat ^ 2 := by
  have hx0 : 0 ≤ a.x := by omega
  have hx1 : 1 ≤ a.x.toNat := by omega
  have hp := pell_factorization a
  have hxcast : (a.x.toNat : ℤ) = a.x := Int.toNat_of_nonneg hx0
  have hycast : (a.y.toNat : ℤ) = a.y := Int.toNat_of_nonneg hy
  exact_mod_cast (show ((a.x.toNat : ℤ) - 1) * ((a.x.toNat : ℤ) + 1) =
    (m : ℤ) * (a.y.toNat : ℤ) ^ 2 by simpa only [hxcast, hycast] using hp)

end PellPaper
