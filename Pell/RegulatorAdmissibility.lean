import Pell.ClassRegulatorReparam

/-!
# Admissibility of the reparameterized regulator cutoff

The class-side cutoff uses the Pell exponent
`Θ(t) = 6 max(1 / 2, t)`.  This file supplies the elementary ceiling estimate
which turns a simple condition on `t` into the logarithmic admissibility
condition required by the uniform Pell estimate.  It makes no assertion about
the comparison between regulators and Pell units.
-/

namespace PellPaper

noncomputable section

/-- The two-layer degree at the class-side exponent is bounded by a linear
function of the nonnegative regulator cutoff. -/
theorem uniformQ_regulatorPellExponent_le_four_mul_add_one {t : ℝ} (ht : 0 ≤ t) :
    (uniformQ (regulatorPellExponent t) : ℝ) ≤ 4 * (t + 1) := by
  have hthree : 3 ≤ regulatorPellExponent t :=
    three_le_regulatorPellExponent t
  have hceil := uniformQ_lt_add_one hthree
  by_cases hhalf : (1 / 2 : ℝ) ≤ t
  · rw [regulatorPellExponent, max_eq_right hhalf]
    rw [regulatorPellExponent, max_eq_right hhalf] at hceil
    linarith
  · have htlt : t < (1 / 2 : ℝ) := lt_of_not_ge hhalf
    have hmax : max (1 / 2 : ℝ) t = 1 / 2 := max_eq_left htlt.le
    rw [regulatorPellExponent, hmax]
    rw [regulatorPellExponent, hmax] at hceil
    linarith

/-- A linear regulator cutoff condition is sufficient for the uniform Pell
admissibility condition after the standard reparameterization. -/
theorem uniformAdmissible_regulatorPellExponent_of_four_mul_add_one_le
    {cExc t X : ℝ} (ht : 0 ≤ t)
    (hcutoff : 4 * (t + 1) ≤
      cExc * Real.sqrt (Real.log X / Real.log (Real.log X))) :
    UniformAdmissible cExc (regulatorPellExponent t) X := by
  unfold UniformAdmissible
  exact (uniformQ_regulatorPellExponent_le_four_mul_add_one ht).trans hcutoff

end

end PellPaper
