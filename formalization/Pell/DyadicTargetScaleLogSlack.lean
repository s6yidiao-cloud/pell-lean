import Pell.DyadicFactorScaleComparability
import Pell.DyadicLocalSourceNormalizedDeterminant
import Pell.ShearedLocalCoordinateLogInput

/-!
# Absorbing the dyadic target-scale rescaling into logarithmic slack

The factor-and-box scale bridge naturally gives a local denominator estimate
at `X = x / 768` when the ordinary target endpoint obeys `x ≤ E² V`.  This
module records the separate logarithmic calculation which absorbs the fixed
factor `768`: after the explicit threshold
`exp (log 1536 / sigma) ≤ x`, the local `2 / (x / 768)` error is bounded by
`exp (-(1 - sigma) log x)` itself.

Thus the determinant-side target exponent can use the ordinary local scale
`x`, while the geometric denominator calculation uses its explicitly
rescaled version.  No determinant cost, mesh, or strict-rate estimate is
claimed here.
-/

namespace PellPaper

noncomputable section

/-- A fixed positive numerator can be absorbed into a positive logarithmic
slack once the displayed exponential threshold is reached. -/
theorem fixed_div_le_exp_neg_one_sub_slack_log
    {C x sigma : ℝ} (hC : 0 < C) (hsigma : 0 < sigma)
    (hlarge : Real.exp (Real.log C / sigma) ≤ x) :
    C / x ≤ Real.exp (-(1 - sigma) * Real.log x) := by
  have hx : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hlarge
  have hlogquot : Real.log C / sigma ≤ Real.log x := by
    apply (Real.exp_le_exp).mp
    simpa only [Real.exp_log hx] using hlarge
  have hlog : Real.log C ≤ sigma * Real.log x := by
    have hmul := (div_le_iff₀ hsigma).mp hlogquot
    linarith
  calc
    C / x = Real.exp (Real.log C - Real.log x) := by
      rw [Real.exp_sub, Real.exp_log hC, Real.exp_log hx]
    _ ≤ Real.exp (-(1 - sigma) * Real.log x) := by
      apply Real.exp_le_exp.mpr
      linarith

/-- The literal rescaling used by the target endpoint converts the local
`2 / X` error at `X = x / 768` into `1536 / x`. -/
theorem two_div_rescaledTargetScale_eq
    {x : ℝ} (hx : 0 < x) :
    2 / (x / 768) = 1536 / x := by
  field_simp [hx.ne']
  ring

/-- A positive ordinary target scale at least `1536` makes the rescaled
local scale `x / 768` large enough for the local logarithm estimate. -/
theorem two_le_rescaledTargetScale_of_1536_le
    {x : ℝ} (hx : 1536 ≤ x) : 2 ≤ x / 768 := by
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 768)).mpr
  norm_num
  exact hx

/-- Actual factor data in a dyadic box, localized at a positive source
centre, yields the determinant-form target logarithm bound at the ordinary
target scale `x`.  The denominator calculation uses `x / 768` internally;
the explicit threshold absorbs that fixed rescaling into `sigma`-slack. -/
theorem dyadicFactorCondition_abs_sheared_log_localRatios_le_exp_neg_one_sub_slack_log_of_targetEndpointScale
    {theta : ℝ} {Y d e u v : ℕ} {i : ℕ × ℕ × ℕ × ℕ}
    {s0 M x sigma : ℝ}
    (hcond : DyadicFactorCondition theta Y d e u v)
    (hbox : (d, e, u, v) ∈ dyadicBox i)
    (hs0 : 0 < s0) (hM : 1 ≤ M)
    (hlower : s0 ≤ (d : ℝ) / (e : ℝ))
    (hupper : (d : ℝ) / (e : ℝ) ≤ s0 * (1 + 1 / M))
    (htarget_scale : x ≤ ((2 ^ i.2.1 : ℕ) : ℝ) ^ 2 *
      ((2 ^ i.2.2.2 : ℕ) : ℝ))
    (hx : 1536 ≤ x) (hsigma : 0 < sigma)
    (hlarge : Real.exp (Real.log (1536 : ℝ) / sigma) ≤ x) :
    |Real.log (localTargetRatio s0 u v) -
        2 * Real.log (localSourceRatio s0 d e)| ≤
      Real.exp (-(1 - sigma) * Real.log x) := by
  have hx_pos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hX : 2 ≤ x / 768 :=
    two_le_rescaledTargetScale_of_1536_le hx
  have hS : 1 ≤ localSourceRatio s0 d e := by
    unfold localSourceRatio
    apply (le_div_iff₀ hs0).mpr
    simpa using hlower
  have hscale_input : 768 * (x / 768) ≤
      ((2 ^ i.2.1 : ℕ) : ℝ) ^ 2 * ((2 ^ i.2.2.2 : ℕ) : ℝ) := by
    calc
      768 * (x / 768) = x := by ring
      _ ≤ ((2 ^ i.2.1 : ℕ) : ℝ) ^ 2 * ((2 ^ i.2.2.2 : ℕ) : ℝ) :=
        htarget_scale
  have hscale : 2 * (x / 768) ≤ s0 ^ 2 * (e : ℝ) ^ 2 * (u : ℝ) :=
    two_mul_le_local_displacement_denominator_of_dyadicBox_localized_source_scale
      hcond hbox hM hupper hscale_input
  calc
    |Real.log (localTargetRatio s0 u v) -
        2 * Real.log (localSourceRatio s0 d e)| ≤ 2 / (x / 768) :=
      dyadicFactorCondition_abs_sheared_log_localRatios_le_two_div_of_scale
        hcond hs0 hX hS hscale
    _ = 1536 / x := two_div_rescaledTargetScale_eq hx_pos
    _ ≤ Real.exp (-(1 - sigma) * Real.log x) :=
      fixed_div_le_exp_neg_one_sub_slack_log (by norm_num) hsigma hlarge

/-- The preceding pointwise result supplies the second reindexed logarithmic
input in exactly the source-normalized determinant shape, without retaining
an abstract local denominator-scale premise. -/
theorem generalBidegreeReindexedShearedLogT_bound_of_dyadicTargetEndpointScale
    {ι : Type*} (A B : ℕ) (eRows : ι ≃ generalBidegreeGrid A B)
    {theta : ℝ} {Y : ℕ} (i : ι → ℕ × ℕ × ℕ × ℕ)
    (d e u v : ι → ℕ) (s0 M x sigma : ℝ)
    (hcond : ∀ row, DyadicFactorCondition theta Y
      (d row) (e row) (u row) (v row))
    (hbox : ∀ row, (d row, e row, u row, v row) ∈ dyadicBox (i row))
    (hs0 : 0 < s0) (hM : 1 ≤ M)
    (hlower : ∀ row, s0 ≤ (d row : ℝ) / (e row : ℝ))
    (hupper : ∀ row,
      (d row : ℝ) / (e row : ℝ) ≤ s0 * (1 + 1 / M))
    (htarget_scale : ∀ row, x ≤ ((2 ^ (i row).2.1 : ℕ) : ℝ) ^ 2 *
      ((2 ^ (i row).2.2.2 : ℕ) : ℝ))
    (hx : 1536 ≤ x) (hsigma : 0 < sigma)
    (hlarge : Real.exp (Real.log (1536 : ℝ) / sigma) ≤ x) :
    ∀ r, |generalBidegreeReindexedShearedLogT A B eRows
      (fun row => localSourceRatio s0 (d row) (e row))
      (fun row => localTargetRatio s0 (u row) (v row)) r| ≤
        Real.exp (-(1 - sigma) * Real.log x) := by
  intro r
  simpa [generalBidegreeReindexedShearedLogT] using
    dyadicFactorCondition_abs_sheared_log_localRatios_le_exp_neg_one_sub_slack_log_of_targetEndpointScale
      (hcond (eRows.symm r)) (hbox (eRows.symm r)) hs0 hM
      (hlower (eRows.symm r)) (hupper (eRows.symm r))
      (htarget_scale (eRows.symm r)) hx hsigma hlarge

/-- The source-normalized cleared-minor endpoint with its target logarithm
input obtained from an ordinary target dyadic endpoint `x ≤ E²V`.  The
determinant exponent `xDet * L` is explicitly matched to the slackened
ordinary scale; all mesh, cubic, and denominator-cost estimates remain
separate hypotheses. -/
theorem standardSelectedIntegralMinor_det_eq_zero_of_dyadicTargetScaleLogSlack
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : ℕ) (eRows : ι ≃ generalBidegreeGrid A B)
    (r : generalBidegreeFormIndex A B ≃ ι)
    (hr : r = (generalBidegreeGridPointEquiv A B).trans eRows.symm)
    {theta : ℝ} {Y : ℕ} (i : ι → ℕ × ℕ × ℕ × ℕ)
    (d e u v : ι → ℕ) (s0 M x sigma m xDet L : ℝ)
    (hcond : ∀ row, DyadicFactorCondition theta Y
      (d row) (e row) (u row) (v row))
    (hbox : ∀ row, (d row, e row, u row, v row) ∈ dyadicBox (i row))
    (hs0 : 0 < s0) (hM : 1 ≤ M)
    (hlower : ∀ row, s0 ≤ (d row : ℝ) / (e row : ℝ))
    (hupper : ∀ row,
      (d row : ℝ) / (e row : ℝ) ≤ s0 * (1 + 1 / M))
    (htarget_scale : ∀ row, x ≤ ((2 ^ (i row).2.1 : ℕ) : ℝ) ^ 2 *
      ((2 ^ (i row).2.2.2 : ℕ) : ℝ))
    (hx : 1536 ≤ x) (hsigma : 0 < sigma)
    (hlarge : Real.exp (Real.log (1536 : ℝ) / sigma) ≤ x)
    (hsource_decay : m * L ≤ Real.log M)
    (hxDetL : xDet * L = (1 - sigma) * Real.log x)
    (hB : 0 < B) (hm : 0 < m) (hmxDet : m ≤ xDet) (hL : 0 < L)
    (hshear : xDet * ((A : ℝ) / (B : ℝ)) ≤ 2 * m)
    (cost : ℝ)
    (hcost :
      |(∏ j : generalBidegreeFormIndex A B,
          ((dyadicFactorTupleFamilyPoints d e u v (r j)).1.2 : ℝ) ^ A *
            ((dyadicFactorTupleFamilyPoints d e u v (r j)).2.2 : ℝ) ^ B) *
          s0 ^ (((A + 1) * (B + 1) * (A + 2 * B)) / 2)| ≤ Real.exp cost)
    (hrate : cost + Real.log (Nat.factorial (Fintype.card
      (generalBidegreeGrid A B)) : ℝ) +
      shearedActualRankTaylorTail A B *
        (Fintype.card (generalBidegreeGrid A B) : ℝ) <
      sourceNormalizedFloorCubicGain A B m xDet L) :
    ((generalBidegreeFormEvaluationMatrix A B
      (dyadicFactorTupleFamilyPoints d e u v)).submatrix r id).det = 0 := by
  have hS_one : ∀ row, 1 ≤ localSourceRatio s0 (d row) (e row) := by
    intro row
    unfold localSourceRatio
    apply (le_div_iff₀ hs0).mpr
    simpa using hlower row
  have hS : ∀ row, 0 < localSourceRatio s0 (d row) (e row) := by
    intro row
    exact lt_of_lt_of_le zero_lt_one (hS_one row)
  have hT : ∀ row, 0 < localTargetRatio s0 (u row) (v row) := by
    intro row
    unfold localTargetRatio
    have hu : 0 < (u row : ℝ) := by
      exact_mod_cast (hcond row).2.2.1
    have hv : 0 < (v row : ℝ) := by
      exact_mod_cast (hcond row).2.2.2.1
    exact div_pos (div_pos hv hu) (sq_pos_of_pos hs0)
  have halpha : ∀ row,
      |generalBidegreeReindexedLogS A B eRows
        (fun row => localSourceRatio s0 (d row) (e row)) row| ≤
          Real.exp (-(m * L)) :=
    generalBidegreeReindexedLogS_bound_of_localizedIntervals
      A B eRows s0 M m L d e hs0 hM hlower hupper hsource_decay
  have hbeta_raw : ∀ row,
      |generalBidegreeReindexedShearedLogT A B eRows
        (fun row => localSourceRatio s0 (d row) (e row))
        (fun row => localTargetRatio s0 (u row) (v row)) row| ≤
          Real.exp (-(1 - sigma) * Real.log x) :=
    generalBidegreeReindexedShearedLogT_bound_of_dyadicTargetEndpointScale
      A B eRows i d e u v s0 M x sigma hcond hbox hs0 hM hlower hupper
      htarget_scale hx hsigma hlarge
  have hbeta : ∀ row,
      |generalBidegreeReindexedShearedLogT A B eRows
        (fun row => localSourceRatio s0 (d row) (e row))
        (fun row => localTargetRatio s0 (u row) (v row)) row| ≤
          Real.exp (-(xDet * L)) := by
    intro row
    calc
      |generalBidegreeReindexedShearedLogT A B eRows
          (fun row => localSourceRatio s0 (d row) (e row))
          (fun row => localTargetRatio s0 (u row) (v row)) row| ≤
        Real.exp (-(1 - sigma) * Real.log x) := hbeta_raw row
      _ = Real.exp (-(xDet * L)) := by
        congr 1
        rw [hxDetL]
        ring
  exact standardSelectedIntegralMinor_det_eq_zero_of_sourceNormalizedFloorCubic_rate
    A B (dyadicFactorTupleFamilyPoints d e u v) eRows r hr s0
      (fun row => localSourceRatio s0 (d row) (e row))
      (fun row => localTargetRatio s0 (u row) (v row))
      (dyadicFactorTupleFamilyPoints_denominators_ne_zero_of_condition d e u v hcond)
      (dyadicFactorTupleFamilyPoints_local_coordinates d e u v hs0
        (fun row => (hcond row).2.1) (fun row => (hcond row).2.2.1))
      hS hT m xDet L hB hm hmxDet hL hshear halpha hbeta cost hcost hrate

end

end PellPaper
