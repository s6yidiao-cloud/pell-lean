import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# The continuous cubic calculation behind the sheared rank cap

This is the exact elementary integral which produces the cubic coefficient in
the two-regime estimate of `L:sheared` in `main.tex`.  It deliberately does
not yet compare the finite lattice rank cap to these continuous envelopes.
-/

namespace PellPaper

open MeasureTheory
open scoped Interval

noncomputable section

/-- The low (triangular) continuous rank-cap envelope. -/
def shearedTriangularCap (m x lambda : ℝ) : ℝ :=
  lambda ^ 2 / (2 * m * x)

/-- The high (parallel-line shell) continuous rank-cap envelope. -/
def shearedShellCap (rho m x lambda : ℝ) : ℝ :=
  rho * lambda / m - x * rho ^ 2 / (2 * m)

/-- On the triangular branch, the continuous rank-cap deficit is nonnegative
up to the crossover radius under the manuscript's shear condition. -/
theorem nonneg_shearedTriangularDeficit
    {rho m x lambda : ℝ} (hrho : 0 ≤ rho) (hm : 0 < m) (hx : 0 < x)
    (hshear : x * rho ≤ 2 * m) (hlambda_nonneg : 0 ≤ lambda)
    (hlambda_le : lambda ≤ x * rho) :
    0 ≤ rho - shearedTriangularCap m x lambda := by
  have hden : 0 < 2 * m * x := by positivity
  have hxr_nonneg : 0 ≤ x * rho := mul_nonneg hx.le hrho
  have hsq : lambda ^ 2 ≤ (x * rho) ^ 2 :=
    (sq_le_sq₀ hlambda_nonneg hxr_nonneg).mpr hlambda_le
  have hshape_mul : (x * rho) ^ 2 ≤ 2 * m * x * rho := by
    calc
      (x * rho) ^ 2 = (x * rho) * (x * rho) := by ring
      _ ≤ (2 * m) * (x * rho) :=
        mul_le_mul_of_nonneg_right hshear hxr_nonneg
      _ = 2 * m * x * rho := by ring
  rw [sub_nonneg, shearedTriangularCap]
  apply (div_le_iff₀ hden).mpr
  calc
    lambda ^ 2 ≤ (x * rho) ^ 2 := hsq
    _ ≤ 2 * m * x * rho := hshape_mul
    _ = rho * (2 * m * x) := by ring

/-- On the parallel-line shell branch, the continuous rank-cap deficit is
nonnegative until the terminal radius of the sheared calculation. -/
theorem nonneg_shearedShellDeficit
    {rho m x lambda : ℝ} (hrho : 0 ≤ rho) (hm : 0 < m)
    (hlambda_le : lambda ≤ m + x * rho / 2) :
    0 ≤ rho - shearedShellCap rho m x lambda := by
  have hfactor_nonneg : 0 ≤ rho / m := div_nonneg hrho hm.le
  have htail_nonneg : 0 ≤ m + x * rho / 2 - lambda :=
    sub_nonneg.mpr hlambda_le
  have hidentity : rho - shearedShellCap rho m x lambda =
      (rho / m) * (m + x * rho / 2 - lambda) := by
    rw [shearedShellCap]
    field_simp [hm.ne']
    ring
  rw [hidentity]
  exact mul_nonneg hfactor_nonneg htail_nonneg

private theorem integral_shearedTriangularDeficit
    (rho m x a b : ℝ) :
    (∫ lambda in a..b, rho - shearedTriangularCap m x lambda) =
      (b - a) * rho -
        ((b ^ 3 - a ^ 3) / 3) * (2 * m * x)⁻¹ := by
  have hpow : IntervalIntegrable (fun lambda : ℝ => lambda ^ 2) volume a b :=
    (continuous_id.pow 2).intervalIntegrable _ _
  calc
    (∫ lambda in a..b, rho - shearedTriangularCap m x lambda) =
        (∫ _lambda in a..b, rho) -
          ∫ lambda in a..b, lambda ^ 2 * (2 * m * x)⁻¹ := by
          apply intervalIntegral.integral_sub intervalIntegrable_const
            (hpow.mul_const _)
    _ = (b - a) * rho -
          ((∫ lambda in a..b, lambda ^ 2) * (2 * m * x)⁻¹) := by
          rw [intervalIntegral.integral_const, intervalIntegral.integral_mul_const]
          simp only [smul_eq_mul]
    _ = (b - a) * rho -
          ((b ^ 3 - a ^ 3) / 3) * (2 * m * x)⁻¹ := by
          rw [integral_pow]
          norm_num

private theorem integral_shearedShellDeficit
    (rho m x a b : ℝ) :
    (∫ lambda in a..b, rho - shearedShellCap rho m x lambda) =
      (b - a) * rho - ((b ^ 2 - a ^ 2) / 2) * (rho / m) +
        (b - a) * (x * rho ^ 2 / (2 * m)) := by
  have hid : IntervalIntegrable (fun lambda : ℝ => lambda) volume a b :=
    continuous_id.intervalIntegrable _ _
  have hlin : IntervalIntegrable (fun lambda : ℝ => (rho / m) * lambda)
      volume a b :=
    hid.const_mul _
  have hconst : IntervalIntegrable (fun _lambda : ℝ => x * rho ^ 2 / (2 * m))
      volume a b :=
    intervalIntegrable_const
  have hone : (∫ lambda in a..b, lambda) = (b ^ 2 - a ^ 2) / 2 := by
    simp
  calc
    (∫ lambda in a..b, rho - shearedShellCap rho m x lambda) =
        ∫ lambda in a..b,
          (rho - (rho / m) * lambda + x * rho ^ 2 / (2 * m)) := by
          apply intervalIntegral.integral_congr
          intro lambda _
          simp only [shearedShellCap]
          ring
    _ = (∫ _lambda in a..b, rho) -
          (∫ lambda in a..b, (rho / m) * lambda) +
          ∫ _lambda in a..b, x * rho ^ 2 / (2 * m) := by
          rw [intervalIntegral.integral_add (intervalIntegrable_const.sub hlin) hconst,
            intervalIntegral.integral_sub intervalIntegrable_const hlin]
    _ = (b - a) * rho -
          (rho / m) * (∫ lambda in a..b, lambda) +
          (b - a) * (x * rho ^ 2 / (2 * m)) := by
          rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
            intervalIntegral.integral_const]
          simp only [smul_eq_mul]
    _ = (b - a) * rho - ((b ^ 2 - a ^ 2) / 2) * (rho / m) +
          (b - a) * (x * rho ^ 2 / (2 * m)) := by
          rw [hone]
          ring

/-- **Continuous two-regime cubic identity.**  The triangular cap up to
`x * rho` and the parallel-line shell cap afterwards contribute exactly the
cubic coefficient used in the sheared determinant estimate. -/
theorem sheared_twoRegime_continuous_integral_eq_cubic
    (rho m x : ℝ) (hm : m ≠ 0) (hx : x ≠ 0) :
    (∫ lambda in 0..x * rho, rho - shearedTriangularCap m x lambda) +
      (∫ lambda in x * rho..m + x * rho / 2,
        rho - shearedShellCap rho m x lambda) =
      rho * m / 2 + x * rho ^ 2 / 2 - x ^ 2 * rho ^ 3 / (24 * m) := by
  rw [integral_shearedTriangularDeficit,
    integral_shearedShellDeficit]
  field_simp [hm, hx]
  ring

/-- The same cubic identity with the positive parts appearing in the greedy
rank-deficit integral.  Positivity of the two displayed deficits follows from
the shear condition, so no mass is lost by the positive-part operation. -/
theorem sheared_twoRegime_continuous_positivePart_integral_eq_cubic
    (rho m x : ℝ) (hrho : 0 ≤ rho) (hm : 0 < m) (hx : 0 < x)
    (hshear : x * rho ≤ 2 * m) :
    (∫ lambda in 0..x * rho,
      max (rho - shearedTriangularCap m x lambda) 0) +
      (∫ lambda in x * rho..m + x * rho / 2,
        max (rho - shearedShellCap rho m x lambda) 0) =
      rho * m / 2 + x * rho ^ 2 / 2 - x ^ 2 * rho ^ 3 / (24 * m) := by
  have hxr_nonneg : 0 ≤ x * rho := mul_nonneg hx.le hrho
  have hsecond_order : x * rho ≤ m + x * rho / 2 := by
    nlinarith
  have hlow :
      (∫ lambda in 0..x * rho,
        max (rho - shearedTriangularCap m x lambda) 0) =
        ∫ lambda in 0..x * rho, rho - shearedTriangularCap m x lambda := by
    apply intervalIntegral.integral_congr
    intro lambda hlambda
    have hlambda' : lambda ∈ Set.Icc 0 (x * rho) := by
      simpa only [Set.uIcc_of_le hxr_nonneg] using hlambda
    exact max_eq_left (nonneg_shearedTriangularDeficit hrho hm hx hshear
      hlambda'.1 hlambda'.2)
  have hhigh :
      (∫ lambda in x * rho..m + x * rho / 2,
        max (rho - shearedShellCap rho m x lambda) 0) =
        ∫ lambda in x * rho..m + x * rho / 2,
          rho - shearedShellCap rho m x lambda := by
    apply intervalIntegral.integral_congr
    intro lambda hlambda
    have hlambda' : lambda ∈ Set.Icc (x * rho) (m + x * rho / 2) := by
      simpa only [Set.uIcc_of_le hsecond_order] using hlambda
    exact max_eq_left (nonneg_shearedShellDeficit hrho hm hlambda'.2)
  rw [hlow, hhigh]
  exact sheared_twoRegime_continuous_integral_eq_cubic rho m x hm.ne' hx.ne'

end

end PellPaper
