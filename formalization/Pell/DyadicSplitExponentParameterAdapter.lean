import Pell.DyadicFactorBoxNormalization
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Concrete split-exponent parameters for a nonempty dyadic factor cell

The balanced argument uses the literal target endpoint scale
`X_i = E^2 V`.  The determinant decay exponent must account for the fixed
local threshold `1536`, whereas the source-clearing exponent must also absorb
the actual-cell comparison `DE sqrt Y <= 10 X_i`.  This file defines the two
exponents separately and proves the exact identities needed by the repaired
split-exponent box theorem.

All endpoint comparisons are consequences of membership in the actual factor
cell.  No asymptotic comparison or analytic black box is used here.
-/

namespace PellPaper

noncomputable section

/-- The literal target endpoint scale `X_i = E^2 V` of a dyadic box. -/
def dyadicTargetEndpointScale (i : ℕ × ℕ × ℕ × ℕ) : ℝ :=
  ((2 ^ i.2.1 : ℕ) : ℝ) ^ 2 * ((2 ^ i.2.2.2 : ℕ) : ℝ)

/-- The determinant-decay slack attached to a target endpoint scale. -/
def dyadicSplitExponentSigma (xScale : ℝ) : ℝ :=
  Real.log 1536 / Real.log xScale

/-- The exponent whose logarithmic weight is `log (xScale / 1536)`. -/
def dyadicSplitExponentDecay (Y : ℕ) (xScale : ℝ) : ℝ :=
  (Real.log xScale - Real.log 1536) / Real.log (Y : ℝ)

/-- The source-clearing exponent.  Its excess over the decay exponent is the
fixed logarithmic cost `log 15360 / log Y`. -/
def dyadicSplitExponentCost (Y : ℕ) (xScale : ℝ) : ℝ :=
  dyadicSplitExponentDecay Y xScale +
    Real.log 15360 / Real.log (Y : ℝ)

/-- On a nonempty actual factor cell, source endpoint height and the literal
target endpoint scale are comparable with explicit constants `10` and `7`.
The squared constants come from `24 * 4 < 100` and `24 * 2 < 49`. -/
theorem nonempty_dyadicFactorBoxCell_endpointHeight_targetScale_comparable
    {cellTheta : ℝ} {Y : ℕ} {i : ℕ × ℕ × ℕ × ℕ}
    (hcell : (dyadicFactorBoxCell cellTheta Y i).Nonempty) :
    let DE : ℝ :=
      ((2 ^ i.1 : ℕ) : ℝ) * ((2 ^ i.2.1 : ℕ) : ℝ)
    DE * Real.sqrt (Y : ℝ) ≤ 10 * dyadicTargetEndpointScale i ∧
      dyadicTargetEndpointScale i ≤ 7 * (DE * Real.sqrt (Y : ℝ)) := by
  obtain ⟨p, hp⟩ := hcell
  rcases p with ⟨d, e, u, v⟩
  have hmem := Finset.mem_inter.mp hp
  have hcond : DyadicFactorCondition cellTheta Y d e u v :=
    mem_dyadicFactorTuples.mp hmem.1
  have hbox : (d, e, u, v) ∈ dyadicBox i := hmem.2
  have hcompare :=
    dyadicFactorCondition_dyadicBox_endpoint_scales_comparable hcond hbox
  have hnormalization :=
    dyadicFactorCondition_dyadicBox_endpoint_normalization hcond hbox
  let D : ℝ := ((2 ^ i.1 : ℕ) : ℝ)
  let E : ℝ := ((2 ^ i.2.1 : ℕ) : ℝ)
  let U : ℝ := ((2 ^ i.2.2.1 : ℕ) : ℝ)
  let V : ℝ := ((2 ^ i.2.2.2 : ℕ) : ℝ)
  let A : ℝ := D * E * Real.sqrt (Y : ℝ)
  let X : ℝ := E ^ 2 * V
  change A ≤ 10 * X ∧ X ≤ 7 * A
  have hD : 0 < D := by dsimp [D]; positivity
  have hE : 0 < E := by dsimp [E]; positivity
  have hU : 0 < U := by dsimp [U]; positivity
  have hV : 0 < V := by dsimp [V]; positivity
  have hX : 0 < X := by dsimp [X]; positivity
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hY0 : (0 : ℝ) ≤ Y := by positivity
  have hsqrtSq : (Real.sqrt (Y : ℝ)) ^ 2 = (Y : ℝ) :=
    Real.sq_sqrt hY0
  have hcompareTarget : X ≤ 24 * (D ^ 2 * U) := by
    simpa only [D, E, U, V, X] using hcompare.1
  have hcompareSource : D ^ 2 * U ≤ 24 * X := by
    simpa only [D, E, U, V, X] using hcompare.2
  have hYupper : (Y : ℝ) < 4 * (U * V) := by
    simpa only [U, V] using hnormalization.2.1
  have hUVupper : U * V < 2 * (Y : ℝ) := by
    simpa only [U, V] using hnormalization.1
  have hheightSq : A ^ 2 < 96 * X ^ 2 := by
    have hscaleY :
        (D * E) ^ 2 * (Y : ℝ) < (D * E) ^ 2 * (4 * (U * V)) :=
      mul_lt_mul_of_pos_left hYupper (sq_pos_of_pos (mul_pos hD hE))
    have hsourceScaled :
        4 * X * (D ^ 2 * U) ≤ 4 * X * (24 * X) :=
      mul_le_mul_of_nonneg_left hcompareSource (by positivity)
    calc
      A ^ 2 = (D * E) ^ 2 * (Y : ℝ) := by
        dsimp [A]
        rw [mul_pow, hsqrtSq]
      _ < (D * E) ^ 2 * (4 * (U * V)) := hscaleY
      _ = 4 * X * (D ^ 2 * U) := by dsimp [X]; ring
      _ ≤ 4 * X * (24 * X) := hsourceScaled
      _ = 96 * X ^ 2 := by ring
  have htargetSq : X ^ 2 < 48 * A ^ 2 := by
    have htargetScaled : X * X ≤ X * (24 * (D ^ 2 * U)) :=
      mul_le_mul_of_nonneg_left hcompareTarget hX.le
    have hUVscaled :
        24 * D ^ 2 * E ^ 2 * (U * V) <
          24 * D ^ 2 * E ^ 2 * (2 * (Y : ℝ)) :=
      mul_lt_mul_of_pos_left hUVupper (by positivity)
    calc
      X ^ 2 = X * X := by ring
      _ ≤ X * (24 * (D ^ 2 * U)) := htargetScaled
      _ = 24 * D ^ 2 * E ^ 2 * (U * V) := by dsimp [X]; ring
      _ < 24 * D ^ 2 * E ^ 2 * (2 * (Y : ℝ)) := hUVscaled
      _ = 48 * A ^ 2 := by
        dsimp [A]
        rw [mul_pow, hsqrtSq]
        ring
  constructor
  · nlinarith [sq_nonneg (A - 10 * X)]
  · nlinarith [sq_nonneg (X - 7 * A)]

/-- The split slack is positive once the literal endpoint scale reaches the
fixed determinant threshold. -/
theorem dyadicSplitExponentSigma_pos {xScale : ℝ}
    (hxScale : 1536 ≤ xScale) :
    0 < dyadicSplitExponentSigma xScale := by
  have hxOne : (1 : ℝ) < xScale := (by norm_num : (1 : ℝ) < 1536).trans_le hxScale
  exact div_pos (Real.log_pos (by norm_num)) (Real.log_pos hxOne)

/-- The chosen slack makes the determinant threshold exactly the literal
endpoint scale. -/
theorem exp_log1536_div_dyadicSplitExponentSigma {xScale : ℝ}
    (hxScale : 1536 ≤ xScale) :
    Real.exp (Real.log (1536 : ℝ) / dyadicSplitExponentSigma xScale) =
      xScale := by
  have hxOne : (1 : ℝ) < xScale := (by norm_num : (1 : ℝ) < 1536).trans_le hxScale
  have hxPos : 0 < xScale := zero_lt_one.trans hxOne
  have hlogX : Real.log xScale ≠ 0 := (Real.log_pos hxOne).ne'
  have hlogC : Real.log (1536 : ℝ) ≠ 0 :=
    (Real.log_pos (by norm_num)).ne'
  rw [dyadicSplitExponentSigma]
  have hquotient :
      Real.log (1536 : ℝ) /
          (Real.log (1536 : ℝ) / Real.log xScale) = Real.log xScale := by
    field_simp
  rw [hquotient, Real.exp_log hxPos]

/-- The decay exponent has precisely the logarithmic weight required by the
determinant estimate. -/
theorem dyadicSplitExponentDecay_mul_log
    (Y : ℕ) {xScale : ℝ} (hY : 2 ≤ Y)
    (hxScale : 1536 ≤ xScale) :
    dyadicSplitExponentDecay Y xScale * Real.log (Y : ℝ) =
      (1 - dyadicSplitExponentSigma xScale) * Real.log xScale := by
  have hlogY : Real.log (Y : ℝ) ≠ 0 := by
    apply (Real.log_pos ?_).ne'
    exact_mod_cast (show 1 < Y by omega)
  have hlogX : Real.log xScale ≠ 0 := by
    apply (Real.log_pos ?_).ne'
    exact (by norm_num : (1 : ℝ) < 1536).trans_le hxScale
  rw [dyadicSplitExponentDecay, dyadicSplitExponentSigma]
  field_simp

/-- The clearing exponent differs from the decay exponent by exactly the
fixed logarithmic charge used in the split fan ledger. -/
theorem dyadicSplitExponentCost_sub_decay_mul_log
    (Y : ℕ) (xScale : ℝ) (hY : 2 ≤ Y) :
    (dyadicSplitExponentCost Y xScale -
        dyadicSplitExponentDecay Y xScale) * Real.log (Y : ℝ) =
      Real.log 15360 := by
  have hlogY : Real.log (Y : ℝ) ≠ 0 := by
    apply (Real.log_pos ?_).ne'
    exact_mod_cast (show 1 < Y by omega)
  rw [dyadicSplitExponentCost]
  ring_nf
  field_simp

/-- The clearing exponent turns the explicit actual-cell comparison
`DE sqrt Y <= 10 xScale` into the source product bound consumed by the
balanced box theorem. -/
theorem endpointProduct_le_rpow_dyadicSplitExponentCost
    (Y : ℕ) {xScale DE : ℝ} (hY : 2 ≤ Y)
    (hxScale : 1536 ≤ xScale)
    (hheight : DE * Real.sqrt (Y : ℝ) ≤ 10 * xScale) :
    DE ≤ (Y : ℝ) ^ (dyadicSplitExponentCost Y xScale - 1 / 2) := by
  have hYpos : (0 : ℝ) < Y := by positivity
  have hxOne : (1 : ℝ) < xScale := (by norm_num : (1 : ℝ) < 1536).trans_le hxScale
  have hxPos : 0 < xScale := zero_lt_one.trans hxOne
  have hlogY : Real.log (Y : ℝ) ≠ 0 := (Real.log_pos (by
    exact_mod_cast (show 1 < Y by omega))).ne'
  have hcostLog :
      dyadicSplitExponentCost Y xScale * Real.log (Y : ℝ) =
        Real.log (10 * xScale) := by
    rw [dyadicSplitExponentCost, dyadicSplitExponentDecay]
    have hlog15360 : Real.log (15360 : ℝ) =
        Real.log 1536 + Real.log 10 := by
      rw [show (15360 : ℝ) = 1536 * 10 by norm_num,
        Real.log_mul (by norm_num) (by norm_num)]
    have hlog10x : Real.log (10 * xScale) =
        Real.log 10 + Real.log xScale := by
      rw [Real.log_mul (by norm_num) hxPos.ne']
    rw [hlog15360, hlog10x]
    field_simp
    ring
  have hpower :
      (Y : ℝ) ^ dyadicSplitExponentCost Y xScale = 10 * xScale := by
    calc
      (Y : ℝ) ^ dyadicSplitExponentCost Y xScale =
          Real.exp (Real.log (Y : ℝ) *
            dyadicSplitExponentCost Y xScale) :=
        Real.rpow_def_of_pos hYpos _
      _ = Real.exp (dyadicSplitExponentCost Y xScale *
            Real.log (Y : ℝ)) := by ring_nf
      _ = Real.exp (Real.log (10 * xScale)) := by rw [hcostLog]
      _ = 10 * xScale := Real.exp_log (by positivity)
  have hfactor :
      (Y : ℝ) ^ (dyadicSplitExponentCost Y xScale - 1 / 2) *
          Real.sqrt (Y : ℝ) =
        (Y : ℝ) ^ dyadicSplitExponentCost Y xScale := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hYpos]
    congr 1
    ring
  have hsqrtPos : 0 < Real.sqrt (Y : ℝ) := Real.sqrt_pos.2 hYpos
  apply le_of_mul_le_mul_right _ hsqrtPos
  calc
    DE * Real.sqrt (Y : ℝ) ≤ 10 * xScale := hheight
    _ = (Y : ℝ) ^ dyadicSplitExponentCost Y xScale := hpower.symm
    _ = (Y : ℝ) ^ (dyadicSplitExponentCost Y xScale - 1 / 2) *
        Real.sqrt (Y : ℝ) := hfactor.symm

/-- The concrete clearing exponent bounds the source endpoint product on a
nonempty actual cell. -/
theorem nonempty_dyadicFactorBoxCell_endpointProduct_le_splitExponentCost
    {cellTheta : ℝ} {Y : ℕ} {i : ℕ × ℕ × ℕ × ℕ}
    (hcell : (dyadicFactorBoxCell cellTheta Y i).Nonempty)
    (hY : 2 ≤ Y) (hxScale : 1536 ≤ dyadicTargetEndpointScale i) :
    ((2 ^ i.1 : ℕ) : ℝ) * ((2 ^ i.2.1 : ℕ) : ℝ) ≤
      (Y : ℝ) ^
        (dyadicSplitExponentCost Y (dyadicTargetEndpointScale i) - 1 / 2) := by
  apply endpointProduct_le_rpow_dyadicSplitExponentCost Y hY hxScale
  exact
    (nonempty_dyadicFactorBoxCell_endpointHeight_targetScale_comparable
      hcell).1

/-- Actual-cell height and the upper half of endpoint comparability bound the
literal target scale by `7 (2Y)^cellTheta`. -/
theorem dyadicTargetEndpointScale_le_seven_mul_twoY_rpow_of_nonemptyFactorCell
    {cellTheta : ℝ} {Y : ℕ} {i : ℕ × ℕ × ℕ × ℕ}
    (hcell : (dyadicFactorBoxCell cellTheta Y i).Nonempty) :
    dyadicTargetEndpointScale i ≤
      7 * ((2 * Y : ℕ) : ℝ) ^ cellTheta := by
  have hcompare :=
    (nonempty_dyadicFactorBoxCell_endpointHeight_targetScale_comparable
      hcell).2
  have hheight :=
    (nonempty_dyadicFactorBoxCell_endpoint_normalization hcell).2.2
  calc
    dyadicTargetEndpointScale i ≤
        7 * ((((2 ^ i.1 : ℕ) : ℝ) * ((2 ^ i.2.1 : ℕ) : ℝ)) *
          Real.sqrt (Y : ℝ)) := hcompare
    _ ≤ 7 * ((2 * Y : ℕ) : ℝ) ^ cellTheta := by
      gcongr

/-- Under the global growth hypothesis used by the balanced fan, the literal
decay exponent is at most `7 theta / 6`.  Here `cellTheta = theta + 1/4` is
the square-part height shift, while `theta` remains the numerical degree
parameter. -/
theorem dyadicSplitExponentDecay_le_seven_mul_theta_div_six_of_growth
    {cellTheta theta : ℝ} {Y : ℕ} {i : ℕ × ℕ × ℕ × ℕ}
    (hcell : (dyadicFactorBoxCell cellTheta Y i).Nonempty)
    (htheta : 3 ≤ theta) (hY : 2 ≤ Y)
    (hcellTheta : cellTheta = theta + 1 / 4)
    (hYgrow : Real.exp (800 * theta ^ 2) < (Y : ℝ)) :
    dyadicSplitExponentDecay Y (dyadicTargetEndpointScale i) ≤
      7 * theta / 6 := by
  subst cellTheta
  let X : ℝ := dyadicTargetEndpointScale i
  let L : ℝ := Real.log (Y : ℝ)
  let Z : ℝ := 2 * (Y : ℝ)
  have hYpos : (0 : ℝ) < Y := by positivity
  have hYone : (1 : ℝ) < (Y : ℝ) := by
    exact_mod_cast (show 1 < Y by omega)
  have hLpos : 0 < L := by
    dsimp [L]
    exact Real.log_pos hYone
  have hXpos : 0 < X := by dsimp [X, dyadicTargetEndpointScale]; positivity
  have hZpos : 0 < Z := by dsimp [Z]; positivity
  have hXupper : X ≤ 7 * Z ^ (theta + 1 / 4) := by
    simpa only [X, Z, Nat.cast_mul, Nat.cast_ofNat] using
      dyadicTargetEndpointScale_le_seven_mul_twoY_rpow_of_nonemptyFactorCell
        hcell
  have hlogXupper :
      Real.log X ≤
        Real.log 7 + (theta + 1 / 4) *
          (Real.log 2 + Real.log (Y : ℝ)) := by
    calc
      Real.log X ≤ Real.log (7 * Z ^ (theta + 1 / 4)) :=
        Real.log_le_log hXpos hXupper
      _ = Real.log 7 + (theta + 1 / 4) * Real.log Z := by
        rw [Real.log_mul (by norm_num)
            (Real.rpow_pos_of_pos hZpos (theta + 1 / 4)).ne',
          Real.log_rpow hZpos]
      _ = Real.log 7 + (theta + 1 / 4) *
          (Real.log 2 + Real.log (Y : ℝ)) := by
        rw [show Z = 2 * (Y : ℝ) by rfl,
          Real.log_mul (by norm_num) hYpos.ne']
  have hlogSeven : Real.log (7 : ℝ) ≤ 2 := by
    have hlt : Real.log (7 : ℝ) < 2 :=
      (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 7)).2 (by
        calc
          (7 : ℝ) < (2.7 : ℝ) ^ 2 := by norm_num
          _ < (Real.exp 1) ^ 2 := by
            gcongr
            exact (by norm_num : (2.7 : ℝ) < 2.7182818283).trans
              Real.exp_one_gt_d9
          _ = Real.exp 2 := by
            rw [← Real.exp_nat_mul]
            norm_num)
    exact hlt.le
  have hlogTwo : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hlogC0 : 0 ≤ Real.log (1536 : ℝ) :=
    Real.log_nonneg (by norm_num)
  have hlogGrowth : 800 * theta ^ 2 < L := by
    have h := Real.strictMonoOn_log (Real.exp_pos _) hYpos hYgrow
    rw [Real.log_exp] at h
    simpa only [L] using h
  have hpoly : theta + 9 / 4 ≤ 200 * theta ^ 2 := by
    nlinarith [sq_nonneg (theta - 3)]
  have hquarterGrowth : 200 * theta ^ 2 < (1 / 4 : ℝ) * L := by
    nlinarith
  have hdelta : (1 / 4 : ℝ) ≤ theta / 6 - 1 / 4 := by
    linarith
  have hdeltaLog : (1 / 4 : ℝ) * L ≤
      (theta / 6 - 1 / 4) * L :=
    mul_le_mul_of_nonneg_right hdelta hLpos.le
  have hfixedBudget : theta + 9 / 4 ≤
      (theta / 6 - 1 / 4) * L :=
    hpoly.trans (hquarterGrowth.le.trans hdeltaLog)
  rw [dyadicSplitExponentDecay]
  apply (div_le_iff₀ hLpos).2
  calc
    Real.log X - Real.log 1536 ≤ Real.log X := sub_le_self _ hlogC0
    _ ≤ Real.log 7 + (theta + 1 / 4) *
        (Real.log 2 + Real.log (Y : ℝ)) := hlogXupper
    _ ≤ 2 + (theta + 1 / 4) * (1 + L) := by
      dsimp [L]
      exact add_le_add hlogSeven
        (mul_le_mul_of_nonneg_left
          (by
            simpa only [add_comm] using
              add_le_add_right hlogTwo (Real.log (Y : ℝ)))
          (by linarith))
    _ = (theta + 1 / 4) * L + (theta + 9 / 4) := by ring
    _ ≤ (theta + 1 / 4) * L + (theta / 6 - 1 / 4) * L := by
      gcongr
    _ = (7 * theta / 6) * L := by ring

/-- The concrete parameter package in exactly the form consumed by the
split-exponent balanced box theorem. -/
theorem nonempty_dyadicFactorBoxCell_splitExponent_parameter_package
    {cellTheta theta : ℝ} {Y : ℕ} {i : ℕ × ℕ × ℕ × ℕ}
    (hcell : (dyadicFactorBoxCell cellTheta Y i).Nonempty)
    (htheta : 3 ≤ theta) (hY : 2 ≤ Y)
    (hcellTheta : cellTheta = theta + 1 / 4)
    (hxScale : 1536 ≤ dyadicTargetEndpointScale i)
    (hYgrow : Real.exp (800 * theta ^ 2) < (Y : ℝ)) :
    let X : ℝ := dyadicTargetEndpointScale i
    let sigma : ℝ := dyadicSplitExponentSigma X
    let qDecay : ℝ := dyadicSplitExponentDecay Y X
    let qCost : ℝ := dyadicSplitExponentCost Y X
    0 < sigma ∧
      Real.exp (Real.log (1536 : ℝ) / sigma) ≤ X ∧
      qDecay * Real.log (Y : ℝ) =
        (1 - sigma) * Real.log X ∧
      (qCost - qDecay) * Real.log (Y : ℝ) ≤ Real.log 15360 ∧
      ((2 ^ i.1 : ℕ) : ℝ) * ((2 ^ i.2.1 : ℕ) : ℝ) ≤
        (Y : ℝ) ^ (qCost - 1 / 2) ∧
      qDecay ≤ 7 * theta / 6 := by
  dsimp only
  refine ⟨dyadicSplitExponentSigma_pos hxScale, ?_,
    dyadicSplitExponentDecay_mul_log Y hY hxScale, ?_, ?_, ?_⟩
  · exact (exp_log1536_div_dyadicSplitExponentSigma hxScale).le
  · exact (dyadicSplitExponentCost_sub_decay_mul_log
      Y (dyadicTargetEndpointScale i) hY).le
  · exact nonempty_dyadicFactorBoxCell_endpointProduct_le_splitExponentCost
      hcell hY hxScale
  · exact dyadicSplitExponentDecay_le_seven_mul_theta_div_six_of_growth
      hcell htheta hY hcellTheta hYgrow

end

end PellPaper
