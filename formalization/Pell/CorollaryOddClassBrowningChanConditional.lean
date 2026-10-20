import Pell.CorollaryOddClassBrowningChanScale
import Pell.CorollaryOddClassExceptionalCutoff
import Pell.QuadraticSelectedLValueSecondMoment

/-!
# Conditional Browning--Chan completion of Corollary 1.2

This module combines the exact finite one-cutoff theorem with three named
arithmetic/analytic inputs: the genus pointwise bound, the published
Browning--Chan weighted moment, and the uniform Pell exceptional estimate.
The selected-L second moment is first kept as an explicit eventual premise;
a final adapter then supplies its already proved constant `520`.

No declaration in this file is an axiom.  Its generic endpoints keep the
Browning--Chan moment, genus bound, and uniform exceptional estimate visible;
the separate capstone module supplies the latter two proved inputs and leaves
only `BrowningChanOddClassBaselineMoment` unresolved.
-/

namespace PellPaper

open Filter Set
open scoped BigOperators

noncomputable section

/-- Conditional eventual Corollary 1.2 bound from the exact finite pipeline.
The second moment is kept explicit here so that the analytic dependency
boundary is visible in the theorem type. -/
theorem eventually_realQuadraticFieldOddClassSum_le_oddClassAverageScale_of_browningChan
    {Cgenus cSave Cmoment : ℝ}
    (hgenus : OddClassGenusPointwiseBound Cgenus)
    (hBrowningChan : BrowningChanOddClassBaselineMoment)
    (hUniform : UniformExceptionalEstimate cSave)
    (hCmoment : 0 ≤ Cmoment)
    (hsecond : ∀ᶠ X : ℝ in atTop,
      (∑ D ∈ fundamentalDiscriminantsBelow X,
        (selectedKroneckerLValue D) ^ 2) ≤ Cmoment * X) :
    ∃ K : ℝ, ∀ᶠ X : ℝ in atTop,
      realQuadraticFieldOddClassSum X ≤ K * oddClassAverageScale X := by
  obtain ⟨Cbc, hCbc, hbc⟩ := hBrowningChan
  obtain ⟨kappa, Cexc, hkappa, hCexc, hE⟩ :=
    uniformExceptionalEstimate_eventually_E_oddClassCutoff_add_one_le
      hUniform
  let Klow : ℝ := 48 * Cgenus * Real.sqrt (Cexc * Cmoment)
  let Khigh : ℝ := (6 * Cgenus * Cbc) * (1 / kappa)
  refine ⟨Klow + Khigh, ?_⟩
  filter_upwards [hbc, hE, hsecond,
    eventually_le_classAverageCutoff (r₀ := (2 : ℝ)) hkappa,
    eventually_ge_atTop (Real.exp (Real.exp 1)),
    eventually_ge_atTop (3 : ℝ)] with
      X hbcX hEX hsecondX hTtwo hlarge hXthree
  have hlogs := classAverage_large_log_bounds hlarge
  have hlog : 0 < Real.log X := classAverageCutoff_log_pos hlogs.1
  have hXpos : 0 < X := (Real.exp_pos (Real.exp 1)).trans_le hlarge
  let T : ℝ := classAverageCutoff kappa X
  have hfinite := realQuadraticFieldOddClassSum_le_browningChan_oneCutoff
    Cgenus X T (Cmoment * X)
      (Cbc * browningChanOddClassBaselineScale X)
    hgenus hXthree (by dsimp [T]; linarith)
    hsecondX (by simpa only [browningChanOddClassBaselineSum] using hbcX)
  have hproduct :
      E (T + 1) X * (Cmoment * X) ≤
        (Real.sqrt (Cexc * Cmoment) * X / (Real.log X) ^ 2) ^ 2 := by
    calc
      E (T + 1) X * (Cmoment * X) ≤
          (Cexc * X / (Real.log X) ^ 4) * (Cmoment * X) := by
        apply mul_le_mul_of_nonneg_right _
          (mul_nonneg hCmoment hXpos.le)
        simpa only [T] using hEX
      _ = (Real.sqrt (Cexc * Cmoment) * X /
          (Real.log X) ^ 2) ^ 2 := by
        rw [div_pow, mul_pow, Real.sq_sqrt
          (mul_nonneg hCexc.le hCmoment)]
        field_simp [hlog.ne']
  have hsqrtBound :
      Real.sqrt (E (T + 1) X * (Cmoment * X)) ≤
        Real.sqrt (Cexc * Cmoment) * X / (Real.log X) ^ 2 := by
    rw [Real.sqrt_le_iff]
    exact ⟨div_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) hXpos.le) (sq_nonneg _), hproduct⟩
  have hratioNonneg : 0 ≤ Real.sqrt X / Real.log X :=
    div_nonneg (Real.sqrt_nonneg _) hlog.le
  have hlow :
      48 * Cgenus * (Real.sqrt X / Real.log X) *
          Real.sqrt (E (T + 1) X * (Cmoment * X)) ≤
        Klow * oddClassAverageScale X := by
    calc
      48 * Cgenus * (Real.sqrt X / Real.log X) *
          Real.sqrt (E (T + 1) X * (Cmoment * X)) ≤
        48 * Cgenus * (Real.sqrt X / Real.log X) *
          (Real.sqrt (Cexc * Cmoment) * X / (Real.log X) ^ 2) := by
        exact mul_le_mul_of_nonneg_left hsqrtBound
          (mul_nonneg (mul_nonneg (by norm_num) hgenus.1) hratioNonneg)
      _ = Klow *
          ((Real.sqrt X / Real.log X) * (X / (Real.log X) ^ 2)) := by
        dsimp [Klow]
        ring
      _ ≤ Klow * oddClassAverageScale X := by
        apply mul_le_mul_of_nonneg_left (oddClass_low_scale_le hlarge)
        dsimp [Klow]
        exact mul_nonneg
          (mul_nonneg (by norm_num) hgenus.1)
          (Real.sqrt_nonneg _)
  have hhigh :
      (6 * Cgenus *
        (Cbc * browningChanOddClassBaselineScale X)) / T =
          Khigh * oddClassAverageScale X := by
    have hidentity :=
      browningChanOddClassBaselineScale_div_classAverageCutoff
        (kappa := kappa) hlogs.1
    dsimp [T]
    rw [show (6 * Cgenus *
        (Cbc * browningChanOddClassBaselineScale X)) /
          classAverageCutoff kappa X =
        (6 * Cgenus * Cbc) *
          (browningChanOddClassBaselineScale X /
            classAverageCutoff kappa X) by ring,
      hidentity]
    dsimp [Khigh]
    ring
  calc
    realQuadraticFieldOddClassSum X ≤
      48 * Cgenus * (Real.sqrt X / Real.log X) *
          Real.sqrt (E (T + 1) X * (Cmoment * X)) +
        (6 * Cgenus *
          (Cbc * browningChanOddClassBaselineScale X)) / T := hfinite
    _ ≤ Klow * oddClassAverageScale X +
        Khigh * oddClassAverageScale X := add_le_add hlow hhigh.le
    _ = (Klow + Khigh) * oddClassAverageScale X := by ring

/-- Exact all-cutoff assertion with every analytic input still displayed in
the theorem type. -/
theorem realQuadraticFieldOddClassAverageAssertion_of_browningChan_and_secondMoment
    {Cgenus cSave Cmoment : ℝ}
    (hgenus : OddClassGenusPointwiseBound Cgenus)
    (hBrowningChan : BrowningChanOddClassBaselineMoment)
    (hUniform : UniformExceptionalEstimate cSave)
    (hCmoment : 0 ≤ Cmoment)
    (hsecond : ∀ᶠ X : ℝ in atTop,
      (∑ D ∈ fundamentalDiscriminantsBelow X,
        (selectedKroneckerLValue D) ^ 2) ≤ Cmoment * X) :
    RealQuadraticFieldOddClassAverageAssertion := by
  obtain ⟨K, hK⟩ :=
    eventually_realQuadraticFieldOddClassSum_le_oddClassAverageScale_of_browningChan
      hgenus hBrowningChan hUniform hCmoment hsecond
  exact realQuadraticFieldOddClassAverageAssertion_of_eventually_bound K hK

/-- The already proved selected-L second moment discharges the explicit
second-moment premise with constant `520`. -/
theorem eventually_realQuadraticFieldOddClassSum_le_oddClassAverageScale_of_browningChan_provedSecondMoment
    {Cgenus cSave : ℝ}
    (hgenus : OddClassGenusPointwiseBound Cgenus)
    (hBrowningChan : BrowningChanOddClassBaselineMoment)
    (hUniform : UniformExceptionalEstimate cSave) :
    ∃ K : ℝ, ∀ᶠ X : ℝ in atTop,
      realQuadraticFieldOddClassSum X ≤ K * oddClassAverageScale X := by
  exact eventually_realQuadraticFieldOddClassSum_le_oddClassAverageScale_of_browningChan
    hgenus hBrowningChan hUniform (Cmoment := 520) (by norm_num)
    eventually_sum_selectedKroneckerLValue_sq_le

/-- Conditional exact all-cutoff assertion.  Compact-range completion is
already proved for the literal field sum and exact Corollary 1.2 scale. -/
theorem realQuadraticFieldOddClassAverageAssertion_of_browningChan
    {Cgenus cSave : ℝ}
    (hgenus : OddClassGenusPointwiseBound Cgenus)
    (hBrowningChan : BrowningChanOddClassBaselineMoment)
    (hUniform : UniformExceptionalEstimate cSave) :
    RealQuadraticFieldOddClassAverageAssertion := by
  obtain ⟨K, hK⟩ :=
    eventually_realQuadraticFieldOddClassSum_le_oddClassAverageScale_of_browningChan_provedSecondMoment
      hgenus hBrowningChan hUniform
  exact realQuadraticFieldOddClassAverageAssertion_of_eventually_bound K hK

end

end PellPaper
