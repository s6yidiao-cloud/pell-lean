import Pell.DyadicBalancedSquareSieveEnvelope
import Pell.DyadicFactorBoxNormalization
import Mathlib.Tactic

/-!
# Reusable consequences of an actual factor cell and the balanced sieve scale

This module records three small implications repeatedly needed by the wide
balanced-box composition.  A nonempty actual factor cell excludes the two
degenerate dyadic heights.  Separately, a real balanced square-sieve scale at
least two forces the cell denominator below the target endpoint product.
The wide prime threshold packages both scale consequences.
-/

namespace PellPaper

noncomputable section

/-- A nonempty actual dyadic factor cell has global height at least two.  The
case `Y = 1` genuinely uses the four permitted Pell differences, rather than
following from endpoint-product inequalities alone. -/
theorem nonempty_dyadicFactorBoxCell_two_le_Y
    {theta : ℝ} {Y : ℕ} {i : ℕ × ℕ × ℕ × ℕ}
    (hcell : (dyadicFactorBoxCell theta Y i).Nonempty) :
    2 ≤ Y := by
  obtain ⟨p, hp⟩ := hcell
  rcases p with ⟨d, e, u, v⟩
  have hcond : DyadicFactorCondition theta Y d e u v :=
    mem_dyadicFactorTuples.mp (Finset.mem_inter.mp hp).1
  by_contra hY
  interval_cases Y
  · rcases hcond with
      ⟨_hd, _he, _hu, _hv, _hdHeight, _heHeight,
        huHeight, _hvHeight, _rest⟩
    omega
  · rcases hcond with
      ⟨hd, he, hu, hv, _hdHeight, _heHeight, huHeight, hvHeight,
        _hsquarefreeU, _hsquarefreeV, _hcoprime, _hYuv, _huvY,
        _hvu, _hvSquare, hdiff, _hheight⟩
    have huOne : u = 1 := by omega
    have hvOne : v = 1 := by omega
    subst u
    subst v
    have hdZ : (1 : ℤ) ≤ d := by exact_mod_cast hd
    have heZ : (1 : ℤ) ≤ e := by exact_mod_cast he
    rcases lt_trichotomy (d : ℤ) (e : ℤ) with hde | hde | hde
    · have hstep : (d : ℤ) + 1 ≤ e := by omega
      have hsquares : (d : ℤ) ^ 2 + 3 ≤ (e : ℤ) ^ 2 := by nlinarith
      rcases hdiff with h | h | h | h <;> norm_num at h <;> nlinarith
    · have hdeNat : d = e := by exact_mod_cast hde
      subst e
      rcases hdiff with h | h | h | h <;> norm_num at h
    · have hstep : (e : ℤ) + 1 ≤ d := by omega
      have hsquares : (e : ℤ) ^ 2 + 3 ≤ (d : ℤ) ^ 2 := by nlinarith
      rcases hdiff with h | h | h | h <;> norm_num at h <;> nlinarith

/-- If the real balanced fourth-root scale is at least two, then a positive
cell denominator is at most the target dyadic endpoint product. -/
theorem dyadicCellDenominator_le_targetEndpointProduct_of_two_le_balancedScale
    (i : ℕ × ℕ × ℕ × ℕ) (M : ℕ)
    (hM : 0 < M)
    (hscale : 2 ≤ dyadicBalancedSquareSieveRealScale i M) :
    (M : ℝ) ≤
      ((2 ^ i.2.2.1 : ℕ) : ℝ) * ((2 ^ i.2.2.2 : ℕ) : ℝ) := by
  let U : ℝ := ((2 ^ i.2.2.1 : ℕ) : ℝ)
  let V : ℝ := ((2 ^ i.2.2.2 : ℕ) : ℝ)
  let R : ℝ := dyadicBalancedSquareSieveRealScale i M
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hR4 : R ^ 4 = U * V / (M : ℝ) := by
    simpa only [R, U, V] using
      dyadicBalancedSquareSieveRealScale_pow_four i M
  have hR4one : 1 ≤ R ^ 4 := by
    have hR0 : 0 ≤ R := by
      dsimp [R, dyadicBalancedSquareSieveRealScale]
      positivity
    nlinarith [sq_nonneg (R ^ 2 - 1)]
  have hquotient : 1 ≤ U * V / (M : ℝ) := hR4one.trans_eq hR4
  have hproduct : (M : ℝ) ≤ U * V := by
    simpa only [one_mul] using (le_div_iff₀ hMr).1 hquotient
  simpa only [U, V] using hproduct

/-- The wide endpoint prime threshold forces both the minimum useful real
sieve scale and the target-product bound for a positive denominator. -/
theorem widePrimeThreshold_two_le_balancedScale_and_denominator_le_targetProduct
    (theta : ℝ) (Y : ℕ) (i : ℕ × ℕ × ℕ × ℕ) (M : ℕ)
    (hM : 0 < M) (htheta : 3 ≤ theta) (hY : 2 ≤ Y)
    (hprime :
      1280000 * theta ^ 7 * (1 + Real.log (2 * (Y : ℝ))) ≤
        dyadicBalancedSquareSieveRealScale i M) :
    2 ≤ dyadicBalancedSquareSieveRealScale i M ∧
      (M : ℝ) ≤
        ((2 ^ i.2.2.1 : ℕ) : ℝ) * ((2 ^ i.2.2.2 : ℕ) : ℝ) := by
  have hthetaOne : (1 : ℝ) ≤ theta := by linarith
  have hthetaPow : (1 : ℝ) ≤ theta ^ 7 := one_le_pow₀ hthetaOne
  have htwoY : (1 : ℝ) ≤ 2 * (Y : ℝ) := by
    exact_mod_cast (show 1 ≤ 2 * Y by omega)
  have hlogBudget : (1 : ℝ) ≤ 1 + Real.log (2 * (Y : ℝ)) :=
    le_add_of_nonneg_right (Real.log_nonneg htwoY)
  have hscale : 2 ≤ dyadicBalancedSquareSieveRealScale i M := by
    calc
      (2 : ℝ) ≤ 1280000 * 1 * 1 := by norm_num
      _ ≤ 1280000 * theta ^ 7 *
          (1 + Real.log (2 * (Y : ℝ))) := by
        gcongr
      _ ≤ dyadicBalancedSquareSieveRealScale i M := hprime
  exact ⟨hscale,
    dyadicCellDenominator_le_targetEndpointProduct_of_two_le_balancedScale
      i M hM hscale⟩

end

end PellPaper
