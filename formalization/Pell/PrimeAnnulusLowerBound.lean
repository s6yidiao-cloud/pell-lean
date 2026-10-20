import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Many primes in a fourfold annulus

The literal prime set `N < p ≤ 4*N` eventually has cardinality at least
`(log 2 / 4) * N / log N`, with a fixed positive constant and no supplied
prime-density premise.  Mathlib's elementary Chebyshev lower and upper
bounds give a positive difference at the scales `4*N` and `N`; their
logarithmic errors are absorbed internally.  This proves a fourfold
annulus estimate, not an estimate for the narrower interval `(N, 2*N]`.
-/

namespace PellPaper

open Asymptotics Filter
open scoped BigOperators

private theorem theta_four_mul_sub_theta_eq_sum (N : ℕ) :
    Chebyshev.theta ((4 * N : ℕ) : ℝ) - Chebyshev.theta (N : ℝ) =
      ∑ p ∈ (Finset.Ioc N (4 * N)).filter Nat.Prime, Real.log (p : ℝ) := by
  have hsubset : Nat.primesLE N ⊆ Nat.primesLE (4 * N) :=
    Nat.primesLE_mono (by omega)
  have hset : Nat.primesLE (4 * N) \ Nat.primesLE N =
      (Finset.Ioc N (4 * N)).filter Nat.Prime := by
    ext p
    by_cases hp : p.Prime <;> simp [Nat.mem_primesLE, hp, not_le, and_comm]
  rw [Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE_log,
    ← Finset.sum_sdiff_eq_sub hsubset, hset]

private theorem eventually_theta_four_mul_sub_theta_lower :
    ∀ᶠ N : ℕ in atTop,
      Real.log 2 * (N : ℝ) ≤
        Chebyshev.theta ((4 * N : ℕ) : ℝ) - Chebyshev.theta (N : ℝ) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcast : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hfour : Tendsto (fun N : ℕ => 4 * (N : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num) hcast
  have hfouradd : Tendsto (fun N : ℕ => 4 * (N : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 hfour
  have hsmall₁ := (Real.isLittleO_log_id_atTop.comp_tendsto hfouradd).def
    (show 0 < Real.log 2 / 10 by positivity)
  have hsmall₂ := ((isLittleO_log_rpow_atTop
    (show (0 : ℝ) < 1 / 2 by norm_num)).comp_tendsto hfour).def
      (show 0 < Real.log 2 / 16 by positivity)
  filter_upwards [hsmall₁, hsmall₂, eventually_ge_atTop 1] with N h₁ h₂ hN
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  change ‖Real.log (4 * (N : ℝ) + 1)‖ ≤
    (Real.log 2 / 10) * ‖4 * (N : ℝ) + 1‖ at h₁
  change ‖Real.log (4 * (N : ℝ))‖ ≤
    (Real.log 2 / 16) * ‖(4 * (N : ℝ)) ^ (1 / 2 : ℝ)‖ at h₂
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by linarith)),
    Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h₁
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by linarith)),
    ← Real.sqrt_eq_rpow, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)] at h₂
  have herror₁ : Real.log (4 * (N : ℝ) + 1) ≤ (Real.log 2 / 2) * N := by
    nlinarith [mul_le_mul_of_nonneg_left hNreal hlog2.le]
  have herror₂ : 2 * Real.sqrt (4 * (N : ℝ)) * Real.log (4 * (N : ℝ)) ≤
      (Real.log 2 / 2) * N := by
    calc
      _ ≤ 2 * Real.sqrt (4 * (N : ℝ)) *
          ((Real.log 2 / 16) * Real.sqrt (4 * (N : ℝ))) :=
        mul_le_mul_of_nonneg_left h₂ (by positivity)
      _ = (Real.log 2 / 8) * Real.sqrt (4 * (N : ℝ)) ^ 2 := by ring
      _ = (Real.log 2 / 2) * N := by
        rw [Real.sq_sqrt (by positivity)]
        ring
  have hlower := Chebyshev.theta_ge (4 * N)
  have hupper := Chebyshev.theta_le_log4_mul_x hN0
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hlower ⊢
  rw [hlog4] at hupper
  linarith

/-- A fixed positive multiple of `N / log N` primes lie in the literal
fourfold annulus `(N, 4*N]` for all sufficiently large natural `N`. -/
theorem eventually_prime_annulus_card_lower :
    ∀ᶠ N : ℕ in atTop,
      (Real.log 2 / 4) * (N : ℝ) / Real.log (N : ℝ) ≤
        (((Finset.Ioc N (4 * N)).filter Nat.Prime).card : ℝ) := by
  filter_upwards [eventually_theta_four_mul_sub_theta_lower, eventually_ge_atTop 4]
    with N htheta hN
  have hNreal : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : 0 < (N : ℝ) := by linarith
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogscale : Real.log (4 * (N : ℝ)) ≤ 2 * Real.log (N : ℝ) := by
    rw [Real.log_mul (by norm_num) hNpos.ne']
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hNreal
    linarith
  have hsum : (∑ p ∈ (Finset.Ioc N (4 * N)).filter Nat.Prime, Real.log (p : ℝ)) ≤
      (((Finset.Ioc N (4 * N)).filter Nat.Prime).card : ℝ) *
        (2 * Real.log (N : ℝ)) := by
    calc
      _ ≤ ∑ _p ∈ (Finset.Ioc N (4 * N)).filter Nat.Prime,
          2 * Real.log (N : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        have hp' := Finset.mem_filter.mp hp
        have hppos : (0 : ℝ) < p := by exact_mod_cast hp'.2.pos
        apply (Real.log_le_log hppos _).trans hlogscale
        exact_mod_cast (Finset.mem_Ioc.mp hp'.1).2
      _ = _ := by simp
  rw [theta_four_mul_sub_theta_eq_sum] at htheta
  apply (div_le_iff₀ hlogN).mpr
  have hprod : 0 ≤ Real.log 2 * (N : ℝ) := mul_nonneg hlog2.le hNpos.le
  nlinarith

end PellPaper
