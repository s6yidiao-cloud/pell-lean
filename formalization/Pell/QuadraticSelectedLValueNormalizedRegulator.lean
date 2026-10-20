import Pell.QuadraticProperFormClassWeightedBound
import Pell.MaximalOrderFundamentalUnitClassBridge

/-!
# Positive selected L-values and an actual normalized-regulator bound

The proved actual class-number formula forces the selected real L-value to
be positive.  The selected normalized regulator is the actual regulator
divided by `log D`.  An elementary uniform comparison, valid for every
`2 <= d <= X`, bounds `sqrt d / log d` by four times `sqrt X / log X`.

Consequently the literal proper-form class number satisfies the all-real
cutoff pointwise estimate with weight `4 * selectedKroneckerLValue` and the
actual selected normalized regulator.  No moment or exceptional-set bound
is assumed or proved here.
-/

namespace PellPaper

noncomputable section

open IntegralBinaryQuadraticForm

/-- Positivity follows from the actual class number and regulator formula,
without a separate nonvanishing or L-value sign input. -/
theorem selectedKroneckerLValue_pos (D : ℕ)
    (hD : PositiveFundamentalDiscriminant D) : 0 < selectedKroneckerLValue D := by
  have hR := rationalQuadraticAlgebraRegulatorAtPositiveFundamentalDiscriminant_pos D hD
  have hh : (0 : ℝ) < rationalQuadraticAlgebraClassNumberAtPositiveFundamentalDiscriminant D hD := by
    exact_mod_cast rationalQuadraticAlgebraClassNumberAtPositiveFundamentalDiscriminant_pos D hD
  have hf := selectedKroneckerLValue_classNumberFormulaInput D hD
  have hprod : 0 < Real.sqrt (D : ℝ) / 2 * selectedKroneckerLValue D := by
    rw [← hf]
    exact mul_pos hR hh
  by_contra hL
  have hL0 : selectedKroneckerLValue D ≤ 0 := le_of_not_gt hL
  have := mul_nonpos_of_nonneg_of_nonpos
    (div_nonneg (Real.sqrt_nonneg (D : ℝ)) (by norm_num : (0 : ℝ) ≤ 2)) hL0
  linarith

/-- The total selected weight is nonnegative also off the intended family,
where its defining value is zero. -/
theorem selectedKroneckerLValue_nonneg (D : ℕ) : 0 ≤ selectedKroneckerLValue D := by
  by_cases hD : PositiveFundamentalDiscriminant D
  · exact (selectedKroneckerLValue_pos D hD).le
  · simp [selectedKroneckerLValue, hD]

/-- The chosen normalized regulator is exactly the actual field regulator
divided by the logarithm of its positive fundamental discriminant. -/
theorem maximalOrderFundamentalUnitRegulator_eq_actualRegulator_div_log
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) :
    maximalOrderFundamentalUnitRegulator D =
      rationalQuadraticAlgebraRegulatorAtPositiveFundamentalDiscriminant D hD /
        Real.log (D : ℝ) := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  rw [maximalOrderFundamentalUnitRegulator_eq_log_of_positiveFundamentalDiscriminant hD,
    rationalQuadraticAlgebraRegulatorAtPositiveFundamentalDiscriminant_eq_log_concreteFundamentalUnitRealModel
      D hD]

/-- The literal proper-form class count with its actual normalized-regulator
denominator, still at the individual discriminant. -/
theorem properFormClass_card_le_selectedLValue_div_normalizedRegulator
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) :
    (Nat.card (ProperFormClass (D : ℤ)) : ℝ) ≤
      (Real.sqrt (D : ℝ) / Real.log (D : ℝ)) *
        (selectedKroneckerLValue D / maximalOrderFundamentalUnitRegulator D) := by
  have hlog : 0 < Real.log (D : ℝ) := Real.log_pos (by exact_mod_cast hD.1)
  have hR := rationalQuadraticAlgebraRegulatorAtPositiveFundamentalDiscriminant_pos D hD
  calc
    _ ≤ Real.sqrt (D : ℝ) * selectedKroneckerLValue D /
        rationalQuadraticAlgebraRegulatorAtPositiveFundamentalDiscriminant D hD :=
      properFormClass_card_le_sqrt_mul_selectedKroneckerLValue_div_regulator D hD
    _ = _ := by
      rw [maximalOrderFundamentalUnitRegulator_eq_actualRegulator_div_log D hD]
      field_simp [hlog.ne', hR.ne']

/-- A uniform elementary comparison across the decreasing and increasing
parts of `sqrt x / log x`; no monotonicity assertion near two is used. -/
theorem sqrt_div_log_le_four_mul_of_two_le {d X : ℝ}
    (hd : 2 ≤ d) (hdX : d ≤ X) :
    Real.sqrt d / Real.log d ≤ 4 * (Real.sqrt X / Real.log X) := by
  have hd0 : 0 < d := by linarith
  have hX0 : 0 < X := hd0.trans_le hdX
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd0
  have hsX : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX0
  have hlogd : 0 < Real.log d := Real.log_pos (by linarith)
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hhalf : (1 / 2 : ℝ) ≤ Real.log d := by
    have htwo := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    have hmono := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hd
    norm_num at htwo
    linarith
  let t := Real.sqrt X / Real.sqrt d
  have ht0 : 0 < t := div_pos hsX hsd
  have ht : 1 ≤ t := (one_le_div hsd).mpr (Real.sqrt_le_sqrt hdX)
  have hlogt : Real.log t = Real.log X / 2 - Real.log d / 2 := by
    dsimp [t]
    rw [Real.log_div hsX.ne' hsd.ne', Real.log_sqrt hX0.le, Real.log_sqrt hd0.le]
  have hlogbound := Real.log_le_sub_one_of_pos ht0
  have hlogcompare : Real.log X ≤ 4 * t * Real.log d := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr hhalf)]
  have ht_eq : Real.sqrt d * t = Real.sqrt X := by
    dsimp [t]
    field_simp
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ hlogd hlogX).mpr
  calc
    Real.sqrt d * Real.log X ≤ Real.sqrt d * (4 * t * Real.log d) :=
      mul_le_mul_of_nonneg_left hlogcompare hsd.le
    _ = 4 * (Real.sqrt d * t) * Real.log d := by ring
    _ = _ := by rw [ht_eq]

/-- The actual proper-form pointwise bound has the exact all-real-cutoff
shape of the Cauchy input, with the explicit scaled weight `4 * L`.
Membership itself supplies `2 <= D < X`, so no extra cutoff premise occurs. -/
theorem properFormClass_card_le_cutoff_selectedLValue_div_normalizedRegulator
    (X : ℝ) (D : ℕ) (hDX : D ∈ fundamentalDiscriminantsBelow X) :
    (Nat.card (ProperFormClass (D : ℤ)) : ℝ) ≤
      (Real.sqrt X / Real.log X) *
        ((4 * selectedKroneckerLValue D) / maximalOrderFundamentalUnitRegulator D) := by
  obtain ⟨hD, hDX'⟩ := mem_fundamentalDiscriminantsBelow.mp hDX
  have hDtwo : (2 : ℝ) ≤ D := by exact_mod_cast hD.1
  have hratio : 0 ≤ selectedKroneckerLValue D / maximalOrderFundamentalUnitRegulator D :=
    div_nonneg (selectedKroneckerLValue_nonneg D)
      (maximalOrderFundamentalUnitRegulator_pos hD).le
  calc
    _ ≤ (Real.sqrt (D : ℝ) / Real.log (D : ℝ)) *
        (selectedKroneckerLValue D / maximalOrderFundamentalUnitRegulator D) :=
      properFormClass_card_le_selectedLValue_div_normalizedRegulator D hD
    _ ≤ (4 * (Real.sqrt X / Real.log X)) *
        (selectedKroneckerLValue D / maximalOrderFundamentalUnitRegulator D) :=
      mul_le_mul_of_nonneg_right (sqrt_div_log_le_four_mul_of_two_le hDtwo hDX'.le) hratio
    _ = _ := by ring

end
end PellPaper
