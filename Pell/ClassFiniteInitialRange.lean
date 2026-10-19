import Pell.ClassAverageCutoff
import Pell.ClassAverageSecondMoment
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.Compact

/-!
# The finite initial range in the class-average argument

The all-cutoff version of the class-average theorem needs an estimate below
the fixed analytic threshold `exp (exp 1)`.  This range does not require an
arithmetic input: for any `ClassNumberModel`, monotonicity gives a finite
upper bound for the form-class sum, while the target scale is continuous and
strictly positive on the compact interval `[3, exp (exp 1)]`.

This module makes that reduction explicit.  It deliberately does not assert
anything about genuine class numbers, Dirichlet `L`-values, or the large-range
exceptional-set estimate.
-/

namespace PellPaper

open Set

noncomputable section

/-- The target scale is strictly positive throughout the range relevant to
the class-average theorem. -/
theorem classAverageScale_pos_of_three_le {X : ℝ} (hX : 3 ≤ X) :
    0 < classAverageScale X := by
  have hExpX : Real.exp 1 < X := Real.exp_one_lt_three.trans_le hX
  have hlogOne : 1 < Real.log X := one_lt_log_of_exp_one_lt hExpX
  have hlogLog : 0 < Real.log (Real.log X) := Real.log_pos hlogOne
  unfold classAverageScale
  exact div_pos
    (mul_pos (Real.rpow_pos_of_pos (by linarith) _)
      (Real.sqrt_pos.2 hlogLog))
    (Real.rpow_pos_of_pos (zero_lt_one.trans hlogOne) _)

/-- On the compact initial range, `classAverageScale` is continuous. -/
theorem continuousOn_classAverageScale_initialRange :
    ContinuousOn classAverageScale (Icc (3 : ℝ) (Real.exp (Real.exp 1))) := by
  have hlog : ContinuousOn (fun X : ℝ ↦ Real.log X)
      (Icc (3 : ℝ) (Real.exp (Real.exp 1))) :=
    Real.continuousOn_log.mono fun X hX ↦ ne_of_gt (by linarith [hX.1])
  have hlogLog : ContinuousOn (fun X : ℝ ↦ Real.log (Real.log X))
      (Icc (3 : ℝ) (Real.exp (Real.exp 1))) :=
    Real.continuousOn_log.comp' hlog (fun X hX ↦
      ne_of_gt (Real.log_pos (by linarith [hX.1])))
  have hXpow : ContinuousOn (fun X : ℝ ↦ Real.rpow X (3 / 2))
      (Icc (3 : ℝ) (Real.exp (Real.exp 1))) :=
    (Real.continuous_rpow_const (by norm_num)).continuousOn
  have hsqrtLogLog : ContinuousOn (fun X : ℝ ↦ Real.sqrt (Real.log (Real.log X)))
      (Icc (3 : ℝ) (Real.exp (Real.exp 1))) :=
    Real.continuous_sqrt.comp_continuousOn' hlogLog
  have hlogPow : ContinuousOn (fun X : ℝ ↦ Real.rpow (Real.log X) (3 / 2))
      (Icc (3 : ℝ) (Real.exp (Real.exp 1))) :=
    Real.continuous_rpow_const (by norm_num) |>.comp_continuousOn' hlog
  have hdenom : ∀ X ∈ Icc (3 : ℝ) (Real.exp (Real.exp 1)),
      Real.rpow (Real.log X) (3 / 2) ≠ 0 := by
    intro X hX
    exact (Real.rpow_pos_of_pos
      (Real.log_pos (by linarith [hX.1])) _).ne'
  change ContinuousOn
    (fun X : ℝ ↦ Real.rpow X (3 / 2) * Real.sqrt (Real.log (Real.log X)) /
      Real.rpow (Real.log X) (3 / 2))
    (Icc (3 : ℝ) (Real.exp (Real.exp 1)))
  exact (hXpow.mul hsqrtLogLog).div hlogPow hdenom

/-- The target scale has one positive lower bound on the complete finite
initial range.  The bound is existential on purpose: it is used only to
absorb finitely many cutoffs into the implied constant. -/
theorem exists_pos_le_classAverageScale_initialRange :
    ∃ b : ℝ, 0 < b ∧ ∀ X ∈ Icc (3 : ℝ) (Real.exp (Real.exp 1)),
      b ≤ classAverageScale X := by
  exact isCompact_Icc.exists_forall_le'
    continuousOn_classAverageScale_initialRange
    (fun X hX ↦ classAverageScale_pos_of_three_le hX.1)

/-- The finite initial range in the exact class-average target needs no
separate arithmetic hypothesis.  Its constant can always be chosen from the
finite sum at the fixed endpoint `exp (exp 1)` and a positive lower bound for
the target scale. -/
theorem exists_formClassSum_initialRange_bound (M : ClassNumberModel) :
    ∃ Bsmall : ℝ, 0 ≤ Bsmall ∧ ∀ X : ℝ, 3 ≤ X →
      X ≤ Real.exp (Real.exp 1) →
        M.formClassSum X ≤ Bsmall * classAverageScale X := by
  obtain ⟨b, hb, hscale⟩ := exists_pos_le_classAverageScale_initialRange
  refine ⟨M.formClassSum (Real.exp (Real.exp 1)) / b,
    div_nonneg (M.formClassSum_nonneg _) hb.le, ?_⟩
  intro X hXthree hXupper
  have hsum : M.formClassSum X ≤ M.formClassSum (Real.exp (Real.exp 1)) :=
    M.formClassSum_mono hXupper
  have hscaleX : b ≤ classAverageScale X := hscale X ⟨hXthree, hXupper⟩
  have hquotient_nonneg : 0 ≤ M.formClassSum (Real.exp (Real.exp 1)) / b :=
    div_nonneg (M.formClassSum_nonneg _) hb.le
  calc
    M.formClassSum X ≤ M.formClassSum (Real.exp (Real.exp 1)) := hsum
    _ = (M.formClassSum (Real.exp (Real.exp 1)) / b) * b := by
      rw [div_mul_cancel₀ _ hb.ne']
    _ ≤ (M.formClassSum (Real.exp (Real.exp 1)) / b) * classAverageScale X :=
      mul_le_mul_of_nonneg_left hscaleX hquotient_nonneg

/-- The all-cutoff class-average reduction does not need a separately assumed
finite-range estimate.  Once the large-range second moment, regulator, and
exceptional-cardinality inputs are present, the finite initial interval is
absorbed by `exists_formClassSum_initialRange_bound`. -/
theorem fieldClassAverageAssertion_of_secondMomentInputs_noSmallRange
    (M : ClassNumberModel) (L r : ℕ → ℝ)
    (Ccard Cmoment r₀ a c : ℝ)
    (hCcard : 0 ≤ Ccard) (hCmoment : 0 ≤ Cmoment)
    (hr₀ : 0 < r₀) (ha : 0 < a) (hc : 0 < c)
    (hL : ∀ D, PositiveFundamentalDiscriminant D → 0 ≤ L D)
    (hr : ∀ D, PositiveFundamentalDiscriminant D → r₀ ≤ r D)
    (hcutoff : ∀ X : ℝ, Real.exp (Real.exp 1) ≤ X →
      r₀ ≤ classAverageCutoff c X)
    (hpoint : ∀ X : ℝ, ∀ D ∈ fundamentalDiscriminantsBelow X,
      (M.formClassNumber D : ℝ) ≤
        (Real.sqrt X / Real.log X) * (L D / r D))
    (hsecond : ∀ X : ℝ, Real.exp (Real.exp 1) ≤ X →
      (∑ D ∈ fundamentalDiscriminantsBelow X, (L D) ^ 2) ≤ Cmoment * X)
    (hcard : ∀ X : ℝ, Real.exp (Real.exp 1) ≤ X →
      ∀ θ ∈ Icc r₀ (classAverageCutoff c X),
        (((fundamentalDiscriminantsBelow X).filter (fun D ↦ r D < θ)).card : ℝ) ≤
          Ccard * X * Real.exp (-a * Real.log X / (θ + 1) ^ 2)) :
    FieldClassAverageAssertion M := by
  obtain ⟨Bsmall, hBsmall, hsmall⟩ := exists_formClassSum_initialRange_bound M
  exact fieldClassAverageAssertion_of_secondMomentInputs M L r
    Ccard Cmoment r₀ a c Bsmall hCcard hCmoment hr₀ ha hc hBsmall
    hL hr hcutoff hpoint hsecond hcard hsmall

end

end PellPaper
