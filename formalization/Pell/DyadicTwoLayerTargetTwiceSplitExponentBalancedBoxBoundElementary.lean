import Pell.DyadicTwoLayerTargetTwiceSplitExponentStandardBalancedFanCompositionElementary
import Pell.DyadicTargetTwiceActualCellCoordinateBudget
import Pell.DyadicFactorBoxNormalization
import Pell.DyadicBalancedSquareSieveEnvelopeElementary
import Pell.DyadicBalancedSquareSieveLogBudget
import Pell.DyadicBalancedScaleConsequences
import Mathlib.Tactic

/-!
# A split-exponent target-twice balanced dyadic box bound

This module evaluates the repaired split-exponent fan estimate at the natural
square-sieve scale and removes the target-endpoint-product premise.  An empty factor cell is immediate.  A
nonempty cell supplies the exact dyadic normalization `UV < 2Y`; the wide
prime threshold then supplies both the useful lower bound on the real sieve
scale and `M <= UV`.  Actual-cell height also supplies the residual coordinate
budget without imposing an upper bound on the source-clearing exponent.
The envelope is evaluated with auxiliary height `2Y`,
and the resulting `log(4Y)` factor is absorbed into the standard `log(2Y)`
budget.
-/

namespace PellPaper

open Filter

noncomputable section

/-- **Split-exponent target-twice balanced local box bound.**  No target-endpoint-product,
denominator-to-product, scale-lower-bound, or coordinate/log-budget premise is
exposed: these are consequences of actual cell nonemptiness and the wide
prime threshold.  `cellTheta` controls actual Pell height, `theta` controls
the near-square numerical ledger, `qDecay` controls the determinant fan, and
`qCost` controls only source clearing. -/
theorem eventually_dyadicFactorBoxCell_card_le_targetTwiceSplitExponentBalancedBox_elementary :
    ∀ᶠ N0 : ℕ in atTop,
      ∀ (B H0 : ℕ) (cellTheta theta Q qDecay qCost m : ℝ) (Y : ℕ)
        (i : ℕ × ℕ × ℕ × ℕ) (M : ℕ)
        (xScale sigma : ℝ),
        0 < M → 2 ≤ Y → 2 ≤ Q →
        3 ≤ theta →
        cellTheta ≤ 2 * theta →
        theta ^ 2 ≤ (B : ℝ) →
        (B : ℝ) < theta ^ 2 + 1 →
        9 / 10 ≤ m → m ≤ 1 →
        m ≤ qDecay → qDecay ≤ 7 * theta / 6 →
        (1 - m) * theta ^ 2 ≤ 1 / 50 →
        Real.exp (800 * theta ^ 2) < (Y : ℝ) →
        (M : ℝ) ≤
          ((2 ^ i.2.1 : ℕ) : ℝ) ^ 2 * ((2 ^ i.2.2.2 : ℕ) : ℝ) →
        ((2 ^ i.2.1 : ℕ) : ℝ) ^ 2 * ((2 ^ i.2.2.2 : ℕ) : ℝ) ≤
          (Y : ℝ) ^ (2 * Q) →
        xScale ≤ ((2 ^ i.2.1 : ℕ) : ℝ) ^ 2 *
          ((2 ^ i.2.2.2 : ℕ) : ℝ) →
        1536 ≤ xScale → 0 < sigma →
        Real.exp (Real.log (1536 : ℝ) / sigma) ≤ xScale →
        m * Real.log (Y : ℝ) ≤ Real.log (M : ℝ) →
        qDecay * Real.log (Y : ℝ) =
          (1 - sigma) * Real.log xScale →
        (qCost - qDecay) * Real.log (Y : ℝ) ≤ Real.log 15360 →
        ((2 ^ i.1 : ℕ) : ℝ) * ((2 ^ i.2.1 : ℕ) : ℝ) ≤
          (Y : ℝ) ^ (qCost - 1 / 2) →
        1280000 * theta ^ 7 * (1 + Real.log (2 * (Y : ℝ))) ≤
          dyadicBalancedSquareSieveRealScale i M →
        N0 ≤ dyadicBalancedSquareSieveScale i M →
        let U : ℝ := ((2 ^ i.2.2.1 : ℕ) : ℝ)
        let V : ℝ := ((2 ^ i.2.2.2 : ℕ) : ℝ)
        let R : ℝ := dyadicBalancedSquareSieveRealScale i M
        let S : ℝ := Real.sqrt (U * V * (M : ℝ)) + U + V
        ((dyadicFactorBoxCell cellTheta Y i).card : ℝ) ≤
          1348 * (M : ℝ) *
              ((H0 : ℝ) + 96 * Q * (B : ℝ) + 16) +
            327680000000 * ((B : ℝ) + 1) ^ 2 *
              (1 + Real.log (2 * (Y : ℝ))) ^ 3 * R * S := by
  filter_upwards
    [eventually_apply_at_dyadicBalancedSquareSieveScale
      (eventually_dyadicFactorBoxCell_card_le_thinFull_of_targetTwiceSplitExponentStandardBalancedFan_elementary)] with N0 hcell
  intro B H0 cellTheta theta Q qDecay qCost m Y i M xScale sigma
    hM hY hQ htheta hcellTheta hBlower hBupper hmlower hmupper
    hmqDecay hqDecay
    hdefect hYgrow hMscale hxQ htargetScale hxScale hsigma
    hlocalThreshold hsourceDecay hxDetL hgap hDE hprime hN0
  let U : ℝ := ((2 ^ i.2.2.1 : ℕ) : ℝ)
  let V : ℝ := ((2 ^ i.2.2.2 : ℕ) : ℝ)
  let N : ℕ := dyadicBalancedSquareSieveScale i M
  let R : ℝ := dyadicBalancedSquareSieveRealScale i M
  let L : ℝ := 1 + Real.log (16 * (N : ℝ) ^ 2)
  let G : ℝ := 1 + Real.log
    (1 + U / Real.sqrt (U * V / (M : ℝ)))
  let A : ℝ := 1 + Real.log (2 * (Y : ℝ))
  let A4 : ℝ := 1 + Real.log (2 * ((2 * Y : ℕ) : ℝ))
  let S : ℝ := Real.sqrt (U * V * (M : ℝ)) + U + V
  by_cases hnonempty : (dyadicFactorBoxCell cellTheta Y i).Nonempty
  · have hnormalization :=
      nonempty_dyadicFactorBoxCell_endpoint_normalization hnonempty
    have hUVlt : U * V < 2 * (Y : ℝ) := by
      simpa only [U, V] using hnormalization.1
    have hUV : U * V ≤ 2 * (Y : ℝ) := hUVlt.le
    have hwide :=
      widePrimeThreshold_two_le_balancedScale_and_denominator_le_targetProduct
        theta Y i M hM htheta hY hprime
    have hscale : 2 ≤ R := by simpa only [R] using hwide.1
    have hproduct : (M : ℝ) ≤ U * V := by
      simpa only [U, V] using hwide.2
    have hthreshold :=
      fullCellResidualSieveUniformBudgetThreshold_le_balancedSquareSieveScale_of_nonemptyFactorCell
        B cellTheta theta Y i M hnonempty hM htheta hY hcellTheta
        hBupper hprime
    have hcell' := hcell i M hN0 B H0 cellTheta theta Q qDecay qCost m
      Y i M xScale sigma
      hM hY hQ htheta hBlower hBupper hmlower hmupper hmqDecay hqDecay
      hdefect hYgrow hMscale hxQ htargetScale hxScale hsigma
      hlocalThreshold hsourceDecay hxDetL hgap hDE
      (by simpa only [U, V] using hUV) hthreshold
    have henv :=
      fullCellElementarySieveAggregateEnvelope_balancedScale_le
        (2 * B + 1) i M hM
        (by simpa only [U, V] using hproduct)
        (by simpa only [R] using hscale)
    have hauxY : 2 ≤ 2 * Y := by omega
    have hUVaux :
        ((2 ^ i.2.2.1 : ℕ) : ℝ) * ((2 ^ i.2.2.2 : ℕ) : ℝ) ≤
          ((2 * Y : ℕ) : ℝ) := by
      simpa only [U, V, Nat.cast_mul, Nat.cast_ofNat] using hUV
    obtain ⟨hNR0, _hNaux, hL0, hG0⟩ :=
      dyadicBalancedSquareSieve_scale_and_log_bounds
        i M (2 * Y) hM
          (by simpa only [U, V] using hproduct) hauxY hUVaux
          (by simpa only [R] using hscale)
    have hNR : (N : ℝ) ≤ 2 * R := by
      simpa only [N, R] using hNR0
    have hLupper : L ≤ 4 * A4 := by
      simpa only [L, N, A4] using hL0
    have hGupper : G ≤ A4 := by
      simpa only [G, U, V, A4] using hG0
    have htwoYone : (1 : ℝ) ≤ 2 * (Y : ℝ) := by
      exact_mod_cast (show 1 ≤ 2 * Y by omega)
    have hAone : 1 ≤ A := by
      dsimp [A]
      exact le_add_of_nonneg_right (Real.log_nonneg htwoYone)
    have hfourYone : (1 : ℝ) ≤ 2 * ((2 * Y : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ 2 * (2 * Y) by omega)
    have hA4one : 1 ≤ A4 := by
      dsimp [A4]
      exact le_add_of_nonneg_right (Real.log_nonneg hfourYone)
    have htwoYpos : (0 : ℝ) < 2 * (Y : ℝ) := by positivity
    have hlogTwo : Real.log 2 ≤ (1 : ℝ) := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h
      exact h
    have hA4upper : A4 ≤ 2 * A := by
      dsimp [A4, A]
      rw [show (2 : ℝ) * ((2 * Y : ℕ) : ℝ) =
          2 * (2 * (Y : ℝ)) by norm_num,
        Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) htwoYpos.ne']
      linarith [Real.log_nonneg htwoYone]
    have hNnat : 0 < N := by
      dsimp [N, dyadicBalancedSquareSieveScale]
      exact positiveNatCeil_pos _
    have hNone : (1 : ℝ) ≤ N := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hNnat.ne')
    have hLone : 1 ≤ L := by
      dsimp [L]
      apply le_add_of_nonneg_right
      apply Real.log_nonneg
      calc
        (1 : ℝ) ≤ (N : ℝ) ^ 2 := one_le_pow₀ hNone
        _ = 1 * (N : ℝ) ^ 2 := by ring
        _ ≤ 16 * (N : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg (N : ℝ))
    have hLsq : L ^ 2 ≤ 16 * A4 ^ 2 := by
      calc
        L ^ 2 ≤ (4 * A4) ^ 2 :=
          pow_le_pow_left₀ (zero_le_one.trans hLone) hLupper 2
        _ = 16 * A4 ^ 2 := by ring
    have hA4cube : A4 ^ 3 ≤ 8 * A ^ 3 := by
      calc
        A4 ^ 3 ≤ (2 * A) ^ 3 :=
          pow_le_pow_left₀ (zero_le_one.trans hA4one) hA4upper 3
        _ = 8 * A ^ 3 := by ring
    have hS0 : 0 ≤ S := by dsimp [S, U, V]; positivity
    have hdegree :
        ((((2 * B + 1 : ℕ) : ℝ) + 1) ^ 2) =
          4 * ((B : ℝ) + 1) ^ 2 := by
      push_cast
      ring
    have henv' :
        fullCellElementarySieveAggregateEnvelope N (2 * B + 1) U V (M : ℝ) ≤
          40000000 * ((((2 * B + 1 : ℕ) : ℝ) + 1) ^ 2) *
            L ^ 2 * G * (N : ℝ) * S := by
      simpa only [U, V, N, L, G, S] using henv
    have hcollapsed :
        fullCellElementarySieveAggregateEnvelope N (2 * B + 1) U V (M : ℝ) ≤
          5120000000 * ((B : ℝ) + 1) ^ 2 * A4 ^ 3 * R * S := by
      calc
        fullCellElementarySieveAggregateEnvelope N (2 * B + 1) U V (M : ℝ) ≤
            40000000 * ((((2 * B + 1 : ℕ) : ℝ) + 1) ^ 2) *
              L ^ 2 * G * (N : ℝ) * S := henv'
        _ ≤ 40000000 * ((((2 * B + 1 : ℕ) : ℝ) + 1) ^ 2) *
              L ^ 2 * A4 * (N : ℝ) * S := by
          gcongr
        _ ≤ 40000000 * (4 * ((B : ℝ) + 1) ^ 2) *
              (16 * A4 ^ 2) * A4 * (2 * R) * S := by
          rw [hdegree]
          gcongr
        _ = 5120000000 * ((B : ℝ) + 1) ^ 2 * A4 ^ 3 * R * S := by
          ring
    change ((dyadicFactorBoxCell cellTheta Y i).card : ℝ) ≤
      1348 * (M : ℝ) * ((H0 : ℝ) + 96 * Q * (B : ℝ) + 16) +
        327680000000 * ((B : ℝ) + 1) ^ 2 * A ^ 3 * R * S
    have hcell'' : ((dyadicFactorBoxCell cellTheta Y i).card : ℝ) ≤
        1348 * (M : ℝ) * ((H0 : ℝ) + 96 * Q * (B : ℝ) + 16) +
          8 * fullCellElementarySieveAggregateEnvelope
            N (2 * B + 1) U V (M : ℝ) := by
      simpa only [N, U, V] using hcell'
    calc
      ((dyadicFactorBoxCell cellTheta Y i).card : ℝ) ≤
          1348 * (M : ℝ) * ((H0 : ℝ) + 96 * Q * (B : ℝ) + 16) +
            8 * fullCellElementarySieveAggregateEnvelope
              N (2 * B + 1) U V (M : ℝ) := hcell''
      _ ≤ 1348 * (M : ℝ) * ((H0 : ℝ) + 96 * Q * (B : ℝ) + 16) +
            8 * (5120000000 * ((B : ℝ) + 1) ^ 2 * A4 ^ 3 * R * S) := by
        gcongr
      _ ≤ 1348 * (M : ℝ) * ((H0 : ℝ) + 96 * Q * (B : ℝ) + 16) +
            8 * (5120000000 * ((B : ℝ) + 1) ^ 2 * (8 * A ^ 3) * R * S) := by
        gcongr
      _ = 1348 * (M : ℝ) * ((H0 : ℝ) + 96 * Q * (B : ℝ) + 16) +
            327680000000 * ((B : ℝ) + 1) ^ 2 * A ^ 3 * R * S := by
        ring
  · have hempty : dyadicFactorBoxCell cellTheta Y i = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hnonempty
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    have hA0 : 0 ≤ A := by
      dsimp [A]
      have htwoYone : (1 : ℝ) ≤ 2 * (Y : ℝ) := by
        exact_mod_cast (show 1 ≤ 2 * Y by omega)
      linarith [Real.log_nonneg htwoYone]
    have hR0 : 0 ≤ R := by
      dsimp [R, dyadicBalancedSquareSieveRealScale]
      positivity
    have hS0 : 0 ≤ S := by dsimp [S, U, V]; positivity
    positivity

end

end PellPaper

