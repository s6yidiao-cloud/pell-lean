import Pell.DyadicBalancedSquareSieveScale
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Logarithmic budgets at the balanced square-sieve scale

This module controls the ceiling and the two logarithmic factors occurring in
the full-cell aggregate envelope.  The dyadic target endpoints are positive
powers of two, so the hypotheses `M ≤ U*V ≤ Y` place the real fourth-root
scale between `1` and `Y` and make the reciprocal logarithm harmless.
-/

namespace PellPaper

noncomputable section

/-- Once the real fourth-root scale is at least one, its positive natural
ceiling is at most twice the real scale. -/
theorem dyadicBalancedSquareSieveScale_le_two_mul_realScale
    (i : ℕ × ℕ × ℕ × ℕ) (M : ℕ)
    (hscale : 1 ≤ dyadicBalancedSquareSieveRealScale i M) :
    (dyadicBalancedSquareSieveScale i M : ℝ) ≤
      2 * dyadicBalancedSquareSieveRealScale i M := by
  calc
    (dyadicBalancedSquareSieveScale i M : ℝ) ≤
        dyadicBalancedSquareSieveRealScale i M + 1 :=
      dyadicBalancedSquareSieveScale_le_realScale_add_one i M
    _ ≤ 2 * dyadicBalancedSquareSieveRealScale i M := by linarith

/-- Under `0 < M` and `U*V ≤ Y`, the real fourth-root scale is at most
`Y`.  The lower bound `M ≤ U*V` records that the fourth-root base lies in
the manuscript's nondegenerate range. -/
theorem dyadicBalancedSquareSieveRealScale_le_Y
    (i : ℕ × ℕ × ℕ × ℕ) (M Y : ℕ)
    (hM : 0 < M)
    (hMle : (M : ℝ) ≤
      ((2 ^ i.2.2.1 : ℕ) : ℝ) * ((2 ^ i.2.2.2 : ℕ) : ℝ))
    (hUVY :
      ((2 ^ i.2.2.1 : ℕ) : ℝ) * ((2 ^ i.2.2.2 : ℕ) : ℝ) ≤
        (Y : ℝ)) :
    dyadicBalancedSquareSieveRealScale i M ≤ (Y : ℝ) := by
  let U : ℝ := ((2 ^ i.2.2.1 : ℕ) : ℝ)
  let V : ℝ := ((2 ^ i.2.2.2 : ℕ) : ℝ)
  have hUone : 1 ≤ U := by
    dsimp [U]
    exact_mod_cast (Nat.one_le_two_pow : 1 ≤ 2 ^ i.2.2.1)
  have hVone : 1 ≤ V := by
    dsimp [V]
    exact_mod_cast (Nat.one_le_two_pow : 1 ≤ 2 ^ i.2.2.2)
  have hU0 : 0 ≤ U := zero_le_one.trans hUone
  have hV0 : 0 ≤ V := zero_le_one.trans hVone
  have hUV0 : 0 ≤ U * V := mul_nonneg hU0 hV0
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast hM
  have hMone : (1 : ℝ) ≤ M := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hM.ne')
  have hbaseOne : 1 ≤ (U * V) / (M : ℝ) := by
    apply (le_div_iff₀ hMpos).2
    simpa only [one_mul, U, V] using hMle
  have hbaseLeUV : (U * V) / (M : ℝ) ≤ U * V := by
    apply (div_le_iff₀ hMpos).2
    have hmul : U * V * 1 ≤ U * V * (M : ℝ) :=
      mul_le_mul_of_nonneg_left hMone hUV0
    simpa only [mul_one] using hmul
  rw [dyadicBalancedSquareSieveRealScale]
  change ((U * V) / (M : ℝ)) ^ ((1 : ℝ) / 4) ≤ (Y : ℝ)
  calc
    ((U * V) / (M : ℝ)) ^ ((1 : ℝ) / 4) ≤
        (U * V) / (M : ℝ) :=
      Real.rpow_le_self_of_one_le hbaseOne (by norm_num)
    _ ≤ U * V := hbaseLeUV
    _ ≤ (Y : ℝ) := by simpa only [U, V] using hUVY

/-- At a real scale at least two, the natural scale is at most `2Y`. -/
theorem dyadicBalancedSquareSieveScale_le_two_mul_Y
    (i : ℕ × ℕ × ℕ × ℕ) (M Y : ℕ)
    (hM : 0 < M)
    (hMle : (M : ℝ) ≤
      ((2 ^ i.2.2.1 : ℕ) : ℝ) * ((2 ^ i.2.2.2 : ℕ) : ℝ))
    (hUVY :
      ((2 ^ i.2.2.1 : ℕ) : ℝ) * ((2 ^ i.2.2.2 : ℕ) : ℝ) ≤
        (Y : ℝ))
    (hscale : 2 ≤ dyadicBalancedSquareSieveRealScale i M) :
    (dyadicBalancedSquareSieveScale i M : ℝ) ≤ 2 * (Y : ℝ) := by
  calc
    (dyadicBalancedSquareSieveScale i M : ℝ) ≤
        2 * dyadicBalancedSquareSieveRealScale i M :=
      dyadicBalancedSquareSieveScale_le_two_mul_realScale i M (by linarith)
    _ ≤ 2 * (Y : ℝ) := by
      gcongr
      exact dyadicBalancedSquareSieveRealScale_le_Y i M Y hM hMle hUVY

/-- The logarithmic scale factor in the aggregate envelope costs at most four
copies of the standard global logarithm. -/
theorem dyadicBalancedSquareSieve_scaleLog_le
    (i : ℕ × ℕ × ℕ × ℕ) (M Y : ℕ)
    (hM : 0 < M)
    (hMle : (M : ℝ) ≤
      ((2 ^ i.2.2.1 : ℕ) : ℝ) * ((2 ^ i.2.2.2 : ℕ) : ℝ))
    (hY : 2 ≤ Y)
    (hUVY :
      ((2 ^ i.2.2.1 : ℕ) : ℝ) * ((2 ^ i.2.2.2 : ℕ) : ℝ) ≤
        (Y : ℝ))
    (hscale : 2 ≤ dyadicBalancedSquareSieveRealScale i M) :
    1 + Real.log
        (16 * (dyadicBalancedSquareSieveScale i M : ℝ) ^ 2) ≤
      4 * (1 + Real.log (2 * (Y : ℝ))) := by
  let N : ℕ := dyadicBalancedSquareSieveScale i M
  have hNposNat : 0 < N := by
    dsimp [N, dyadicBalancedSquareSieveScale]
    exact positiveNatCeil_pos _
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hNposNat
  have hNle : (N : ℝ) ≤ 2 * (Y : ℝ) := by
    dsimp [N]
    exact dyadicBalancedSquareSieveScale_le_two_mul_Y
      i M Y hM hMle hUVY hscale
  have htwoYpos : 0 < 2 * (Y : ℝ) := by positivity
  have hlogN : Real.log (N : ℝ) ≤ Real.log (2 * (Y : ℝ)) :=
    Real.log_le_log hNpos hNle
  have hlogTwoYOne : 1 ≤ Real.log (2 * (Y : ℝ)) := by
    apply (Real.le_log_iff_exp_le htwoYpos).2
    have hthree : (3 : ℝ) ≤ 2 * (Y : ℝ) := by
      exact_mod_cast (show 3 ≤ 2 * Y by omega)
    exact Real.exp_one_lt_three.le.trans hthree
  have hlogSixteen : Real.log 16 ≤ 4 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    have hlogTwo : Real.log 2 ≤ 1 := by
      have h :=
        Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h
      exact h
    nlinarith
  change 1 + Real.log (16 * (N : ℝ) ^ 2) ≤
    4 * (1 + Real.log (2 * (Y : ℝ)))
  rw [Real.log_mul (by norm_num : (16 : ℝ) ≠ 0)
    (pow_ne_zero 2 hNpos.ne'), Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  calc
    1 + (Real.log 16 + 2 * Real.log (N : ℝ)) ≤
        1 + (4 + 2 * Real.log (2 * (Y : ℝ))) := by linarith
    _ ≤ 4 * (1 + Real.log (2 * (Y : ℝ))) := by nlinarith

/-- The reciprocal-side logarithm is no larger than the standard global
logarithm.  Positivity of the power-of-two endpoints is used internally. -/
theorem dyadicBalancedSquareSieve_reciprocalLog_le
    (i : ℕ × ℕ × ℕ × ℕ) (M Y : ℕ)
    (hM : 0 < M)
    (hMle : (M : ℝ) ≤
      ((2 ^ i.2.2.1 : ℕ) : ℝ) * ((2 ^ i.2.2.2 : ℕ) : ℝ))
    (hY : 2 ≤ Y)
    (hUVY :
      ((2 ^ i.2.2.1 : ℕ) : ℝ) * ((2 ^ i.2.2.2 : ℕ) : ℝ) ≤
        (Y : ℝ)) :
    1 + Real.log
        (1 + ((2 ^ i.2.2.1 : ℕ) : ℝ) /
          Real.sqrt
            ((((2 ^ i.2.2.1 : ℕ) : ℝ) *
              ((2 ^ i.2.2.2 : ℕ) : ℝ)) / (M : ℝ))) ≤
      1 + Real.log (2 * (Y : ℝ)) := by
  let U : ℝ := ((2 ^ i.2.2.1 : ℕ) : ℝ)
  let V : ℝ := ((2 ^ i.2.2.2 : ℕ) : ℝ)
  let X : ℝ := (U * V) / (M : ℝ)
  have hUone : 1 ≤ U := by
    dsimp [U]
    exact_mod_cast (Nat.one_le_two_pow : 1 ≤ 2 ^ i.2.2.1)
  have hVone : 1 ≤ V := by
    dsimp [V]
    exact_mod_cast (Nat.one_le_two_pow : 1 ≤ 2 ^ i.2.2.2)
  have hU0 : 0 ≤ U := zero_le_one.trans hUone
  have hV0 : 0 ≤ V := zero_le_one.trans hVone
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast hM
  have hXone : 1 ≤ X := by
    dsimp [X]
    apply (le_div_iff₀ hMpos).2
    simpa only [one_mul, U, V] using hMle
  have hsqrtOne : 1 ≤ Real.sqrt X := Real.one_le_sqrt.mpr hXone
  have hsqrtPos : 0 < Real.sqrt X := zero_lt_one.trans_le hsqrtOne
  have hUdiv : U / Real.sqrt X ≤ U := by
    apply (div_le_iff₀ hsqrtPos).2
    have hmul : U * 1 ≤ U * Real.sqrt X :=
      mul_le_mul_of_nonneg_left hsqrtOne hU0
    simpa only [mul_one] using hmul
  have hUleUV : U ≤ U * V := by
    have hmul : U * 1 ≤ U * V :=
      mul_le_mul_of_nonneg_left hVone hU0
    simpa only [mul_one] using hmul
  have hquotient0 : 0 ≤ U / Real.sqrt X :=
    div_nonneg hU0 hsqrtPos.le
  have hargumentPos : 0 < 1 + U / Real.sqrt X := by linarith
  have hargumentLe : 1 + U / Real.sqrt X ≤ 2 * (Y : ℝ) := by
    have hYone : (1 : ℝ) ≤ Y := by exact_mod_cast (show 1 ≤ Y by omega)
    have hUVY' : U * V ≤ (Y : ℝ) := by
      simpa only [U, V] using hUVY
    nlinarith
  have hlog := Real.log_le_log hargumentPos hargumentLe
  change 1 + Real.log (1 + U / Real.sqrt X) ≤
    1 + Real.log (2 * (Y : ℝ))
  linarith

/-- Packaged scale and logarithm bounds used to simplify the balanced
full-cell aggregate envelope. -/
theorem dyadicBalancedSquareSieve_scale_and_log_bounds
    (i : ℕ × ℕ × ℕ × ℕ) (M Y : ℕ)
    (hM : 0 < M)
    (hMle : (M : ℝ) ≤
      ((2 ^ i.2.2.1 : ℕ) : ℝ) * ((2 ^ i.2.2.2 : ℕ) : ℝ))
    (hY : 2 ≤ Y)
    (hUVY :
      ((2 ^ i.2.2.1 : ℕ) : ℝ) * ((2 ^ i.2.2.2 : ℕ) : ℝ) ≤
        (Y : ℝ))
    (hscale : 2 ≤ dyadicBalancedSquareSieveRealScale i M) :
    (dyadicBalancedSquareSieveScale i M : ℝ) ≤
        2 * dyadicBalancedSquareSieveRealScale i M ∧
      (dyadicBalancedSquareSieveScale i M : ℝ) ≤ 2 * (Y : ℝ) ∧
      1 + Real.log
          (16 * (dyadicBalancedSquareSieveScale i M : ℝ) ^ 2) ≤
        4 * (1 + Real.log (2 * (Y : ℝ))) ∧
      1 + Real.log
          (1 + ((2 ^ i.2.2.1 : ℕ) : ℝ) /
            Real.sqrt
              ((((2 ^ i.2.2.1 : ℕ) : ℝ) *
                ((2 ^ i.2.2.2 : ℕ) : ℝ)) / (M : ℝ))) ≤
        1 + Real.log (2 * (Y : ℝ)) := by
  exact
    ⟨dyadicBalancedSquareSieveScale_le_two_mul_realScale i M (by linarith),
      dyadicBalancedSquareSieveScale_le_two_mul_Y
        i M Y hM hMle hUVY hscale,
      dyadicBalancedSquareSieve_scaleLog_le
        i M Y hM hMle hY hUVY hscale,
      dyadicBalancedSquareSieve_reciprocalLog_le
        i M Y hM hMle hY hUVY⟩

end

end PellPaper
