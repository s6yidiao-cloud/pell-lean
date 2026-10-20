import Pell.ClassCutoffAdmissibility
import Pell.ClassUniformDynamic
import Pell.ClassAverageSecondMoment
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Growth of the class-average cutoff

The regulator cutoff in the class-number argument is a positive constant
times `sqrt (log X / log (log X))`.  The preceding class-side reduction left
two elementary eventual conditions open: that this cutoff eventually exceeds
the fixed lower regulator endpoint, and that a sufficiently small multiple of
it lies in the admissible range of the uniform Pell estimate.

This file proves those conditions directly.  It makes no assertion about
quadratic fields, unit comparison, class-number formulae, or Dirichlet
`L`-function moments.
-/

namespace PellPaper

open Filter Set

noncomputable section

/-- The iterated logarithm is eventually no larger than the square root of
the first logarithm.  This is the only asymptotic ingredient needed to show
that the class-average cutoff tends to infinity. -/
theorem eventually_log_log_le_sqrt_log :
    ∀ᶠ X : ℝ in atTop,
      Real.log (Real.log X) ≤ Real.sqrt (Real.log X) := by
  have hsmall : Real.log =o[atTop] (fun y : ℝ ↦ y ^ (1 / 2 : ℝ)) :=
    isLittleO_log_rpow_atTop (by norm_num)
  have hbound := Real.tendsto_log_atTop.eventually hsmall.eventuallyLE
  filter_upwards [hbound,
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with X hboundX hlogX
  have hloglog_nonneg : 0 ≤ Real.log (Real.log X) := Real.log_nonneg hlogX
  have hroot_nonneg : 0 ≤ (Real.log X) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (zero_le_one.trans hlogX) _
  simpa only [Real.norm_eq_abs, Real.sqrt_eq_rpow, abs_of_nonneg hloglog_nonneg,
    abs_of_nonneg hroot_nonneg] using hboundX

/-- The logarithmic factor underlying the class-average cutoff tends to
infinity. -/
theorem tendsto_classAverageCutoffFactor_atTop :
    Tendsto (fun X : ℝ ↦
      Real.sqrt (Real.log X / Real.log (Real.log X))) atTop atTop := by
  apply tendsto_atTop_mono' atTop
    ((eventually_log_log_le_sqrt_log.and
      (Real.tendsto_log_atTop.eventually_ge_atTop (2 : ℝ))).mono
      fun X hX ↦ ?_)
  · exact (Real.tendsto_sqrt_atTop.comp
      (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop))
  · have hlog_pos : 0 < Real.log X := by linarith [hX.2]
    have hloglog_pos : 0 < Real.log (Real.log X) :=
      Real.log_pos (by linarith [hX.2])
    apply Real.sqrt_le_sqrt
    apply (le_div_iff₀ hloglog_pos).mpr
    calc
      Real.sqrt (Real.log X) * Real.log (Real.log X) ≤
          Real.sqrt (Real.log X) * Real.sqrt (Real.log X) :=
        mul_le_mul_of_nonneg_left hX.1 (Real.sqrt_nonneg _)
      _ = Real.log X := Real.mul_self_sqrt hlog_pos.le

/-- Any positive constant times the class-average cutoff factor tends to
infinity. -/
theorem tendsto_classAverageCutoff_atTop {c : ℝ} (hc : 0 < c) :
    Tendsto (fun X : ℝ ↦ classAverageCutoff c X) atTop atTop := by
  simpa only [classAverageCutoff] using
    tendsto_classAverageCutoffFactor_atTop.const_mul_atTop hc

/-- A positive class-average cutoff eventually lies above every fixed real
lower regulator endpoint. -/
theorem eventually_le_classAverageCutoff {r₀ c : ℝ} (hc : 0 < c) :
    ∀ᶠ X : ℝ in atTop, r₀ ≤ classAverageCutoff c X :=
  (tendsto_classAverageCutoff_atTop hc).eventually_ge_atTop r₀

/-- Choosing the cutoff constant to be `cExc / 8` makes the endpoint
admissibility inequality true eventually.  The numerical `8` leaves half of
the available logarithmic factor for the additive rounding term. -/
theorem eventually_classAverageCutoff_endpoint_admissible {cExc : ℝ}
    (hcExc : 0 < cExc) :
    ∀ᶠ X : ℝ in atTop,
      4 * (classAverageCutoff (cExc / 8) X + 1) ≤
        cExc * Real.sqrt (Real.log X / Real.log (Real.log X)) := by
  filter_upwards [tendsto_classAverageCutoffFactor_atTop.eventually_ge_atTop
    (8 / cExc)] with X hX
  have hprod : 8 ≤ cExc *
      Real.sqrt (Real.log X / Real.log (Real.log X)) :=
    calc
      8 = (8 / cExc) * cExc := by field_simp
      _ ≤ Real.sqrt (Real.log X / Real.log (Real.log X)) * cExc :=
        mul_le_mul_of_nonneg_right hX hcExc.le
      _ = _ := by ring
  unfold classAverageCutoff
  nlinarith

/-- The canonical small cutoff `cExc / 8` automatically supplies both
eventual side conditions needed to run the class-side regulator bridge. -/
theorem eventually_classAverageCutoff_lower_and_admissible
    {cExc r₀ : ℝ} (hcExc : 0 < cExc) (hr₀ : 0 ≤ r₀) :
    ∀ᶠ X : ℝ in atTop,
      r₀ ≤ classAverageCutoff (cExc / 8) X ∧
        ∀ t ∈ Icc r₀ (classAverageCutoff (cExc / 8) X),
          UniformAdmissible cExc (regulatorPellExponent t) X := by
  filter_upwards [eventually_le_classAverageCutoff
      (r₀ := r₀) (show 0 < cExc / 8 by positivity),
    eventually_classAverageCutoff_endpoint_admissible hcExc] with X hlower hendpoint
  exact ⟨hlower,
    uniformAdmissible_regulatorPellExponent_on_Icc_classAverageCutoff
      hr₀ hendpoint⟩

/-- The moving-family Cauchy--Schwarz reduction can choose its cutoff
constant internally, after the uniform Pell estimate has supplied `cExc`.
With the canonical choice `cExc / 8`, the regulator-cutoff lower bound and
uniform admissibility are no longer hypotheses.  The remaining non-elementary
inputs are the genuine arithmetic bridge, the class-number-formula comparison,
and the second moment. -/
theorem eventually_formClassSum_bound_of_uniformExceptional_canonicalCutoff
    (M : ClassNumberModel) (L r : ℕ → ℝ)
    (Cmoment r₀ cSave : ℝ)
    (hCmoment : 0 ≤ Cmoment)
    (hr₀ : 0 < r₀)
    (hL : ∀ D, PositiveFundamentalDiscriminant D → 0 ≤ L D)
    (hr : ∀ D, PositiveFundamentalDiscriminant D → r₀ ≤ r D)
    (htransfer : ∀ X t D, D ∈ fundamentalDiscriminantsBelow X → r D < t →
      SmallFundamentalSolution (regulatorPellExponent t) D)
    (hUniform : UniformExceptionalEstimate cSave)
    (hpoint : ∀ X D, D ∈ fundamentalDiscriminantsBelow X →
      (M.formClassNumber D : ℝ) ≤
        (Real.sqrt X / Real.log X) * (L D / r D))
    (hsecond : ∀ᶠ X : ℝ in atTop,
      (∑ D ∈ fundamentalDiscriminantsBelow X, (L D) ^ 2) ≤ Cmoment * X) :
    ∃ cExc C : ℝ, 0 < cExc ∧ 0 < C ∧
      ∀ᶠ X : ℝ in atTop,
        M.formClassSum X ≤
          (Real.sqrt Cmoment / (cExc / 8) + Real.sqrt (C * Cmoment) *
            (((1 + 1 / r₀) ^ 2 + 1) /
              Real.sqrt ((cSave / 36) / 2))) * classAverageScale X := by
  obtain ⟨cExc, C, hcExc, hC, hcard⟩ :=
    uniformExceptionalEstimate_fundamentalDiscriminantsBelow_reparam_rate
      r cSave htransfer hUniform
  have hc : 0 < cExc / 8 := by positivity
  have hfirst : ∀ᶠ X : ℝ in atTop,
      (∑ D ∈ fundamentalDiscriminantsBelow X, L D) ≤ Real.sqrt Cmoment * X := by
    filter_upwards [hsecond, eventually_ge_atTop (0 : ℝ)] with X hsecondX hX
    exact fundamentalDiscriminantsBelow_first_moment_of_second_moment L
      hCmoment hX hsecondX
  refine ⟨cExc, C, hcExc, hC, ?_⟩
  filter_upwards [hcard, hfirst, hsecond,
    eventually_classAverageCutoff_lower_and_admissible hcExc hr₀.le,
    eventually_ge_atTop (Real.exp (Real.exp 1))] with
      X hcardX hfirstX hsecondX hsideX hlargeX
  have hsave : 0 < cSave / 36 := by
    obtain ⟨hcSave, -⟩ := hUniform
    positivity
  have hcardAt : ∀ t ∈ Icc r₀ (classAverageCutoff (cExc / 8) X),
      (((fundamentalDiscriminantsBelow X).filter (fun D ↦ r D < t)).card : ℝ) ≤
        C * X * Real.exp
          (-(cSave / 36) * Real.log X / (t + 1) ^ 2) := by
    intro t ht
    exact hcardX t (hr₀.le.trans ht.1) (hsideX.2 t ht)
  have hfinite := finite_sum_class_bound_of_exponential_cardinality_rate
    (fundamentalDiscriminantsBelow X)
    (fun D ↦ (M.formClassNumber D : ℝ)) L r
    (Real.sqrt Cmoment) C Cmoment r₀ (cSave / 36) (cExc / 8) X
    (Real.sqrt_nonneg _) hC.le hCmoment
    (fun D hD ↦ hL D (mem_fundamentalDiscriminantsBelow.mp hD).1)
    (fun D hD ↦ hr D (mem_fundamentalDiscriminantsBelow.mp hD).1)
    hr₀ hc hsave hlargeX hsideX.1
    (fun D hD ↦ hpoint X D hD)
    hfirstX hsecondX hcardAt
  simpa [ClassNumberModel.formClassSum] using hfinite

end

end PellPaper
