import Pell.ClassFiniteInitialRange
import Pell.ClassCutoffGrowth
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.Compact

/-!
# Completing an eventual class-average bound

The analytic class-average argument naturally produces a bound only eventually
in the real cutoff.  This module proves the elementary completion step from
that eventual statement to the exact all-`X ≥ 3` target.  It reuses the
positivity of `classAverageScale` from `ClassFiniteInitialRange`, and extends
its compactness argument from the manuscript's particular analytic threshold
to an arbitrary finite endpoint selected from the eventual filter.

No arithmetic, regulator, exceptional-set, or Dirichlet-`L` input is supplied
here.  The final theorem below merely removes a finite-cutoff bookkeeping
premise from the conditional result of `ClassCutoffGrowth`.
-/

namespace PellPaper

open Filter Set
open scoped BigOperators

noncomputable section

/-- The class-average scale is continuous on every finite interval whose
left endpoint is `3`.  This is the variable-endpoint form of the continuity
calculation used for the fixed initial interval. -/
theorem continuousOn_classAverageScale_Icc (T : ℝ) :
    ContinuousOn classAverageScale (Icc (3 : ℝ) T) := by
  have hlog : ContinuousOn (fun X : ℝ ↦ Real.log X) (Icc (3 : ℝ) T) :=
    Real.continuousOn_log.mono fun X hX ↦ ne_of_gt (by linarith [hX.1])
  have hlogLog : ContinuousOn (fun X : ℝ ↦ Real.log (Real.log X))
      (Icc (3 : ℝ) T) :=
    Real.continuousOn_log.comp' hlog (fun X hX ↦
      ne_of_gt (Real.log_pos (by linarith [hX.1])))
  have hXpow : ContinuousOn (fun X : ℝ ↦ Real.rpow X (3 / 2))
      (Icc (3 : ℝ) T) :=
    (Real.continuous_rpow_const (by norm_num)).continuousOn
  have hsqrtLogLog : ContinuousOn (fun X : ℝ ↦ Real.sqrt (Real.log (Real.log X)))
      (Icc (3 : ℝ) T) :=
    Real.continuous_sqrt.comp_continuousOn' hlogLog
  have hlogPow : ContinuousOn (fun X : ℝ ↦ Real.rpow (Real.log X) (3 / 2))
      (Icc (3 : ℝ) T) :=
    Real.continuous_rpow_const (by norm_num) |>.comp_continuousOn' hlog
  have hdenom : ∀ X ∈ Icc (3 : ℝ) T,
      Real.rpow (Real.log X) (3 / 2) ≠ 0 := by
    intro X hX
    exact (Real.rpow_pos_of_pos
      (Real.log_pos (by linarith [hX.1])) _).ne'
  change ContinuousOn
    (fun X : ℝ ↦ Real.rpow X (3 / 2) * Real.sqrt (Real.log (Real.log X)) /
      Real.rpow (Real.log X) (3 / 2))
    (Icc (3 : ℝ) T)
  exact (hXpow.mul hsqrtLogLog).div hlogPow hdenom

/-- On every finite interval relevant to the target, the class-average scale
has one strictly positive lower bound. -/
theorem exists_pos_le_classAverageScale_Icc (T : ℝ) :
    ∃ b : ℝ, 0 < b ∧ ∀ X ∈ Icc (3 : ℝ) T,
      b ≤ classAverageScale X := by
  exact isCompact_Icc.exists_forall_le'
    (continuousOn_classAverageScale_Icc T)
    (fun X hX ↦ classAverageScale_pos_of_three_le hX.1)

/-- A form-class sum has a uniform multiple of the target scale on any fixed
finite interval.  This is the arbitrary-endpoint counterpart of
`exists_formClassSum_initialRange_bound`; it is needed because an eventual
bound may begin beyond the manuscript's fixed analytic threshold. -/
theorem exists_formClassSum_compactRange_bound (M : ClassNumberModel) (T : ℝ) :
    ∃ Bsmall : ℝ, 0 ≤ Bsmall ∧ ∀ X : ℝ, 3 ≤ X → X ≤ T →
      M.formClassSum X ≤ Bsmall * classAverageScale X := by
  obtain ⟨b, hb, hscale⟩ := exists_pos_le_classAverageScale_Icc T
  refine ⟨M.formClassSum T / b,
    div_nonneg (M.formClassSum_nonneg _) hb.le, ?_⟩
  intro X hXthree hXupper
  have hsum : M.formClassSum X ≤ M.formClassSum T :=
    M.formClassSum_mono hXupper
  have hscaleX : b ≤ classAverageScale X := hscale X ⟨hXthree, hXupper⟩
  have hquotient_nonneg : 0 ≤ M.formClassSum T / b :=
    div_nonneg (M.formClassSum_nonneg _) hb.le
  calc
    M.formClassSum X ≤ M.formClassSum T := hsum
    _ = (M.formClassSum T / b) * b := by
      rw [div_mul_cancel₀ _ hb.ne']
    _ ≤ (M.formClassSum T / b) * classAverageScale X :=
      mul_le_mul_of_nonneg_left hscaleX hquotient_nonneg

/-- An eventual form-class estimate already implies the exact all-cutoff
class-average target.  The eventual threshold supplies a finite endpoint;
monotonicity bounds the form-class sum before it, while compact positivity of
the scale absorbs that range into the final positive constant. -/
theorem fieldClassAverageAssertion_of_eventually_formClassSum_bound
    (M : ClassNumberModel) (K : ℝ)
    (hlarge : ∀ᶠ X : ℝ in atTop,
      M.formClassSum X ≤ K * classAverageScale X) :
    FieldClassAverageAssertion M := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp hlarge
  let U : ℝ := max T 3
  obtain ⟨Bsmall, hBsmall, hsmall⟩ :=
    exists_formClassSum_compactRange_bound M U
  let C : ℝ := |K| + Bsmall + 1
  have hC : 0 < C := by
    dsimp [C]
    nlinarith [abs_nonneg K, hBsmall]
  refine ⟨C, hC, ?_⟩
  intro X hXthree
  constructor
  · exact M.ordinaryClassSum_le_formClassSum X
  · by_cases hlargeX : U ≤ X
    · have hscale : 0 ≤ classAverageScale X :=
        classAverageScale_nonneg (by linarith)
      calc
        M.formClassSum X ≤ K * classAverageScale X :=
          hT X ((le_max_left T 3).trans hlargeX)
        _ ≤ C * classAverageScale X := by
          apply mul_le_mul_of_nonneg_right _ hscale
          dsimp [C]
          nlinarith [le_abs_self K, hBsmall]
    · have hXupper : X ≤ U := le_of_not_ge hlargeX
      have hscale : 0 ≤ classAverageScale X :=
        classAverageScale_nonneg (by linarith)
      calc
        M.formClassSum X ≤ Bsmall * classAverageScale X :=
          hsmall X hXthree hXupper
        _ ≤ C * classAverageScale X := by
          apply mul_le_mul_of_nonneg_right _ hscale
          dsimp [C]
          nlinarith [abs_nonneg K]

/-- The canonical-cutoff class-side pipeline now has its exact all-`X ≥ 3`
conclusion without a separately assumed small-range estimate.  Its remaining
hypotheses are exactly the non-elementary model, regulator-transfer,
uniform-exceptional, pointwise class-number, and second-moment inputs. -/
theorem fieldClassAverageAssertion_of_uniformExceptional_canonicalCutoff
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
    FieldClassAverageAssertion M := by
  obtain ⟨cExc, Cexc, hcExc, hCexc, hlarge⟩ :=
    eventually_formClassSum_bound_of_uniformExceptional_canonicalCutoff M L r
      Cmoment r₀ cSave hCmoment hr₀ hL hr htransfer hUniform hpoint hsecond
  exact fieldClassAverageAssertion_of_eventually_formClassSum_bound M
    (Real.sqrt Cmoment / (cExc / 8) + Real.sqrt (Cexc * Cmoment) *
      (((1 + 1 / r₀) ^ 2 + 1) / Real.sqrt ((cSave / 36) / 2))) hlarge

end

end PellPaper
