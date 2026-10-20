import Pell.QuadraticFormProperEquivalence
import Mathlib.Algebra.Squarefree.Basic

/-!
# Fundamental discriminants force primitivity

Every integral binary quadratic form whose discriminant is positive
fundamental is primitive. In the even branch, a nonunit common divisor
would force all coefficients to be even, making D/4 itself a discriminant
and therefore zero or one modulo four, contrary to fundamentality.
-/

namespace PellPaper
namespace IntegralBinaryQuadraticForm

private theorem two_dvd_of_dvd_four_of_not_isUnit {z : ℤ}
    (hz : z ∣ 4) (hu : ¬ IsUnit z) : (2 : ℤ) ∣ z := by
  have hzabs : z.natAbs ∣ 2 ^ 2 := by
    norm_num only [Nat.reducePow]
    exact Int.dvd_natCast.mp hz
  obtain ⟨k, hk, heq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hzabs
  apply Int.natCast_dvd.mpr
  rw [heq]
  have hk0 : k ≠ 0 := by
    intro h
    apply hu
    rw [Int.isUnit_iff_natAbs_eq, heq, h, pow_zero]
  exact dvd_pow_self 2 hk0

/-- No separate primitivity premise is needed for an integral form of
positive fundamental discriminant. -/
theorem primitive_of_positiveFundamentalDiscriminant
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D)
    (Q : IntegralBinaryQuadraticForm) (hQ : Q.discriminant = (D : ℤ)) :
    Q.Primitive := by
  intro z hza hzb hzc
  have hzsq : z * z ∣ (D : ℤ) := by
    rw [← hQ, discriminant, pow_two]
    exact dvd_sub (mul_dvd_mul hzb hzb)
      (by simpa only [mul_assoc] using dvd_mul_of_dvd_right (mul_dvd_mul hza hzc) 4)
  rcases hD.2 with ⟨hsq, _⟩ | ⟨d, hDd, hsq, hdmod⟩
  · exact (Int.squarefree_natCast.mpr hsq) z hzsq
  · by_contra hu
    have hzi : z * z ∣ (4 : ℤ) * (d : ℤ) := by
      simpa only [hDd, Nat.cast_mul, Nat.cast_ofNat] using hzsq
    have hzfour : z ∣ (4 : ℤ) :=
      (Int.squarefree_natCast.mpr hsq).dvd_of_squarefree_of_mul_dvd_mul_left hzi
    have hz2 := two_dvd_of_dvd_four_of_not_isUnit hzfour hu
    obtain ⟨a, ha⟩ := hz2.trans hza
    obtain ⟨b, hb⟩ := hz2.trans hzb
    obtain ⟨c, hc⟩ := hz2.trans hzc
    have hd : (d : ℤ) = b ^ 2 - 4 * a * c := by
      simp only [discriminant, ha, hb, hc, hDd, Nat.cast_mul, Nat.cast_ofNat] at hQ
      nlinarith
    have hdmod' : (d : ℤ) % 4 = 2 ∨ (d : ℤ) % 4 = 3 := by
      exact_mod_cast hdmod
    rcases Int.even_or_odd b with ⟨t, ht⟩ | ⟨t, ht⟩
    · have hd0 : (d : ℤ) = 4 * (t ^ 2 - a * c) := by rw [hd, ht]; ring
      omega
    · have hd1 : (d : ℤ) = 4 * (t ^ 2 + t - a * c) + 1 := by rw [hd, ht]; ring
      omega

end IntegralBinaryQuadraticForm
end PellPaper
