import Pell.DyadicLocalSourceNormalizedDeterminant
import Pell.ShearedLocalCoordinateRateAbsorption

/-!
# Actual dyadic comparable-cost input for the cleared determinant

The local determinant endpoint has a finite denominator-and-centre cost
input.  On one actual dyadic factor box, its abstract comparison constants
can be supplied directly: the source centre is at most twice the ratio of
the doubled source endpoints, and the source/target endpoint ratios satisfy
the one-sided comparison with factor `24`.

This module proves that transport.  The remaining symmetric exponential
cost bound is retained as an explicit hypothesis; deriving it from the
source's size ranges is separate geometric work.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- A localized source interval in a dyadic factor box makes its centre
positive and bounds its absolute value by twice the ratio of the doubled
source endpoints. -/
theorem dyadicBox_abs_center_le_two_mul_doubledSourceRatio
    {i : ℕ × ℕ × ℕ × ℕ} {d e u v : ℕ} {s₀ M : ℝ}
    (hbox : (d, e, u, v) ∈ dyadicBox i)
    (hM : 1 ≤ M)
    (hlower : s₀ ≤ (d : ℝ) / (e : ℝ))
    (hupper : (d : ℝ) / (e : ℝ) ≤ s₀ * (1 + 1 / M)) :
    |s₀| ≤ 2 *
      ((2 * ((2 ^ i.1 : ℕ) : ℝ)) /
        (2 * ((2 ^ i.2.1 : ℕ) : ℝ))) := by
  have hDpos : 0 < ((2 ^ i.1 : ℕ) : ℝ) := by positivity
  have hEpos : 0 < ((2 ^ i.2.1 : ℕ) : ℝ) := by positivity
  have hsLower := dyadicBox_center_lower_bound_of_localized_source_upper
    hbox hM hupper
  have hspos : 0 < s₀ := by
    have : 0 < ((2 ^ i.1 : ℕ) : ℝ) /
        (4 * ((2 ^ i.2.1 : ℕ) : ℝ)) := by positivity
    exact lt_of_lt_of_le this hsLower
  have hboxUpper := dyadicBox_coordinate_upper_bounds hbox
  have hboxLower := dyadicBox_coordinate_lower_bounds hbox
  have hdUpper : (d : ℝ) ≤ 2 * ((2 ^ i.1 : ℕ) : ℝ) := by
    exact_mod_cast hboxUpper.1
  have heLower : ((2 ^ i.2.1 : ℕ) : ℝ) ≤ (e : ℝ) := by
    exact_mod_cast hboxLower.2.1
  have hepos : 0 < (e : ℝ) := by
    have : 0 < e := lt_of_lt_of_le (by positivity : 0 < 2 ^ i.2.1)
      hboxLower.2.1
    exact_mod_cast this
  have hratio : (d : ℝ) / (e : ℝ) ≤
      (2 * ((2 ^ i.1 : ℕ) : ℝ)) / ((2 ^ i.2.1 : ℕ) : ℝ) := by
    apply (div_le_div_iff₀ hepos hEpos).mpr
    calc
      (d : ℝ) * ((2 ^ i.2.1 : ℕ) : ℝ) ≤
          (2 * ((2 ^ i.1 : ℕ) : ℝ)) *
            ((2 ^ i.2.1 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hdUpper hEpos.le
      _ ≤ (2 * ((2 ^ i.1 : ℕ) : ℝ)) * (e : ℝ) :=
        mul_le_mul_of_nonneg_left heLower (by positivity)
  calc
    |s₀| = s₀ := abs_of_pos hspos
    _ ≤ (d : ℝ) / (e : ℝ) := hlower
    _ ≤ (2 * ((2 ^ i.1 : ℕ) : ℝ)) /
          ((2 ^ i.2.1 : ℕ) : ℝ) := hratio
    _ = 2 *
        ((2 * ((2 ^ i.1 : ℕ) : ℝ)) /
          (2 * ((2 ^ i.2.1 : ℕ) : ℝ))) := by
      field_simp [hEpos.ne']

/-- The actual factor equation and one dyadic box give the comparable
source/target endpoint ratio needed by the local-cost ledger, after all four
coordinate endpoints are doubled to make them genuine upper bounds. -/
theorem dyadicFactorCondition_doubledEndpoint_scale_comparison
    {theta : ℝ} {Y d e u v : ℕ} {i : ℕ × ℕ × ℕ × ℕ}
    (hcond : DyadicFactorCondition theta Y d e u v)
    (hbox : (d, e, u, v) ∈ dyadicBox i) :
    (2 * ((2 ^ i.1 : ℕ) : ℝ) /
        (2 * ((2 ^ i.2.1 : ℕ) : ℝ))) ^ 2 ≤
      24 *
        ((2 * ((2 ^ i.2.2.2 : ℕ) : ℝ)) /
          (2 * ((2 ^ i.2.2.1 : ℕ) : ℝ))) := by
  let D : ℝ := ((2 ^ i.1 : ℕ) : ℝ)
  let E : ℝ := ((2 ^ i.2.1 : ℕ) : ℝ)
  let U : ℝ := ((2 ^ i.2.2.1 : ℕ) : ℝ)
  let V : ℝ := ((2 ^ i.2.2.2 : ℕ) : ℝ)
  change (2 * D / (2 * E)) ^ 2 ≤ 24 * (2 * V / (2 * U))
  have hcompare :=
    (dyadicFactorCondition_dyadicBox_endpoint_scales_comparable hcond hbox).2
  have hcompare' : D ^ 2 * U ≤ 24 * (E ^ 2 * V) := by
    simpa [D, E, U, V] using hcompare
  have hEpos : 0 < E := by
    dsimp [E]
    positivity
  have hUpos : 0 < U := by
    dsimp [U]
    positivity
  have hden : 0 < E ^ 2 * U := by positivity
  have hscaled : (D / E) ^ 2 ≤ 24 * (V / U) := by
    have hleft : (D / E) ^ 2 = (D ^ 2 * U) / (E ^ 2 * U) := by
      field_simp [hEpos.ne', hUpos.ne']
    have hright : 24 * (V / U) =
        (24 * (E ^ 2 * V)) / (E ^ 2 * U) := by
      field_simp [hEpos.ne', hUpos.ne']
    rw [hleft, hright]
    exact div_le_div_of_nonneg_right hcompare' hden.le
  calc
    (2 * D / (2 * E)) ^ 2 = (D / E) ^ 2 := by
      field_simp [hEpos.ne']
    _ ≤ 24 * (V / U) := hscaled
    _ = 24 * (2 * V / (2 * U)) := by
      field_simp [hUpos.ne']

/-- The actual tuple denominators in one dyadic box are bounded by the
doubled source and target endpoints. -/
theorem dyadicFactorTupleFamilyPoints_denominator_bounds_of_mem_dyadicBox
    {ι : Type*} (d e u v : ι → ℕ) {i : ℕ × ℕ × ℕ × ℕ}
    (hbox : ∀ row, (d row, e row, u row, v row) ∈ dyadicBox i) :
    (∀ row, |((dyadicFactorTupleFamilyPoints d e u v row).1.2 : ℝ)| ≤
      2 * ((2 ^ i.2.1 : ℕ) : ℝ)) ∧
    (∀ row, |((dyadicFactorTupleFamilyPoints d e u v row).2.2 : ℝ)| ≤
      2 * ((2 ^ i.2.2.1 : ℕ) : ℝ)) := by
  constructor
  · intro row
    have h := (dyadicBox_coordinate_upper_bounds (hbox row)).2.1
    have hcast : (e row : ℝ) ≤ 2 * ((2 ^ i.2.1 : ℕ) : ℝ) := by
      exact_mod_cast h
    simpa [dyadicFactorTupleFamilyPoints,
      dyadicFactorTupleToGeneralBidegreeFormPoint] using hcast
  · intro row
    have h := (dyadicBox_coordinate_upper_bounds (hbox row)).2.2.1
    have hcast : (u row : ℝ) ≤ 2 * ((2 ^ i.2.2.1 : ℕ) : ℝ) := by
      exact_mod_cast h
    simpa [dyadicFactorTupleFamilyPoints,
      dyadicFactorTupleToGeneralBidegreeFormPoint] using hcast

/-- **Actual dyadic comparable-cost adapter.**  A family of factor tuples in
one box, localized at the source ratio, discharges the row-denominator,
centre, and endpoint-comparison premises of the cleared determinant cost
bound with literal constants `c = 2` and `k = 24`.  The symmetric exponential
cost of the doubled endpoints remains the sole cost hypothesis. -/
theorem dyadicFactorTupleFamilyPoints_hcost_of_dyadicComparableBounds
    {ι : Type*} [Fintype ι]
    (A B : ℕ) (d e u v : ι → ℕ)
    (r : generalBidegreeFormIndex A B → ι)
    {theta : ℝ} {Y : ℕ} {i : ℕ × ℕ × ℕ × ℕ} {s₀ M baseCost : ℝ}
    (hcond : ∀ row, DyadicFactorCondition theta Y
      (d row) (e row) (u row) (v row))
    (hbox : ∀ row, (d row, e row, u row, v row) ∈ dyadicBox i)
    (hM : 1 ≤ M)
    (hlower : ∀ row, s₀ ≤ (d row : ℝ) / (e row : ℝ))
    (hupper : ∀ row, (d row : ℝ) / (e row : ℝ) ≤ s₀ * (1 + 1 / M))
    (hbaseCost :
      (2 : ℝ) ^ (((A + 1) * (B + 1) * (A + 2 * B)) / 2) *
        (24 : ℝ) ^ (B * ((A + 1) * (B + 1)) / 2) *
          ((2 * ((2 ^ i.1 : ℕ) : ℝ)) *
            (2 * ((2 ^ i.2.1 : ℕ) : ℝ))) ^
              (A * ((A + 1) * (B + 1)) / 2) *
            ((2 * ((2 ^ i.2.2.1 : ℕ) : ℝ)) *
              (2 * ((2 ^ i.2.2.2 : ℕ) : ℝ))) ^
                (B * ((A + 1) * (B + 1)) / 2) ≤ Real.exp baseCost) :
    |(∏ j : generalBidegreeFormIndex A B,
        ((dyadicFactorTupleFamilyPoints d e u v (r j)).1.2 : ℝ) ^ A *
          ((dyadicFactorTupleFamilyPoints d e u v (r j)).2.2 : ℝ) ^ B) *
        s₀ ^ (((A + 1) * (B + 1) * (A + 2 * B)) / 2)| ≤
      Real.exp baseCost := by
  have hbox0 := hbox (r (0, 0))
  have hcond0 := hcond (r (0, 0))
  have hcenter := dyadicBox_abs_center_le_two_mul_doubledSourceRatio
    hbox0 hM (hlower (r (0, 0))) (hupper (r (0, 0)))
  have hscale := dyadicFactorCondition_doubledEndpoint_scale_comparison
    hcond0 hbox0
  obtain ⟨he, hu⟩ :=
    dyadicFactorTupleFamilyPoints_denominator_bounds_of_mem_dyadicBox
      d e u v hbox
  apply sourceOriented_denominatorCenter_hcost_of_localDyadicComparableBounds
    A B (dyadicFactorTupleFamilyPoints d e u v) r s₀
    (2 * ((2 ^ i.1 : ℕ) : ℝ))
    (2 * ((2 ^ i.2.1 : ℕ) : ℝ))
    (2 * ((2 ^ i.2.2.1 : ℕ) : ℝ))
    (2 * ((2 ^ i.2.2.2 : ℕ) : ℝ)) 2 24 baseCost
  · positivity
  · positivity
  · positivity
  · positivity
  · norm_num
  · norm_num
  · exact fun j => he (r j)
  · exact fun j => hu (r j)
  · exact hcenter
  · exact hscale
  · simpa using hbaseCost

/-- The same actual-dyadic cost adapter with the `c = 2`, `k = 24` loss kept
as the named logarithmic correction used by the strict-rate bridge.  Its
base-cost hypothesis contains only the symmetric doubled-endpoint factors. -/
theorem dyadicFactorTupleFamilyPoints_hcost_logLoss_of_dyadicComparableBounds
    {ι : Type*} [Fintype ι]
    (A B : ℕ) (d e u v : ι → ℕ)
    (r : generalBidegreeFormIndex A B → ι)
    {theta : ℝ} {Y : ℕ} {i : ℕ × ℕ × ℕ × ℕ} {s₀ M baseCost : ℝ}
    (hcond : ∀ row, DyadicFactorCondition theta Y
      (d row) (e row) (u row) (v row))
    (hbox : ∀ row, (d row, e row, u row, v row) ∈ dyadicBox i)
    (hM : 1 ≤ M)
    (hlower : ∀ row, s₀ ≤ (d row : ℝ) / (e row : ℝ))
    (hupper : ∀ row, (d row : ℝ) / (e row : ℝ) ≤ s₀ * (1 + 1 / M))
    (hbaseCost :
      ((2 * ((2 ^ i.1 : ℕ) : ℝ)) *
        (2 * ((2 ^ i.2.1 : ℕ) : ℝ))) ^
          (A * ((A + 1) * (B + 1)) / 2) *
        ((2 * ((2 ^ i.2.2.1 : ℕ) : ℝ)) *
          (2 * ((2 ^ i.2.2.2 : ℕ) : ℝ))) ^
            (B * ((A + 1) * (B + 1)) / 2) ≤ Real.exp baseCost) :
    |(∏ j : generalBidegreeFormIndex A B,
        ((dyadicFactorTupleFamilyPoints d e u v (r j)).1.2 : ℝ) ^ A *
          ((dyadicFactorTupleFamilyPoints d e u v (r j)).2.2 : ℝ) ^ B) *
        s₀ ^ (((A + 1) * (B + 1) * (A + 2 * B)) / 2)| ≤
      Real.exp (baseCost + shearedComparableCoordinateLogLoss A B 2 24) := by
  have hbox0 := hbox (r (0, 0))
  have hcond0 := hcond (r (0, 0))
  have hcenter := dyadicBox_abs_center_le_two_mul_doubledSourceRatio
    hbox0 hM (hlower (r (0, 0))) (hupper (r (0, 0)))
  have hscale := dyadicFactorCondition_doubledEndpoint_scale_comparison
    hcond0 hbox0
  obtain ⟨he, hu⟩ :=
    dyadicFactorTupleFamilyPoints_denominator_bounds_of_mem_dyadicBox
      d e u v hbox
  apply abs_rowDenominator_center_le_expCost_of_comparableScale_logLoss
    A B
    (fun j : generalBidegreeFormIndex A B =>
      ((dyadicFactorTupleFamilyPoints d e u v (r j)).1.2 : ℝ))
    (fun j : generalBidegreeFormIndex A B =>
      ((dyadicFactorTupleFamilyPoints d e u v (r j)).2.2 : ℝ))
    s₀
    (2 * ((2 ^ i.1 : ℕ) : ℝ))
    (2 * ((2 ^ i.2.1 : ℕ) : ℝ))
    (2 * ((2 ^ i.2.2.1 : ℕ) : ℝ))
    (2 * ((2 ^ i.2.2.2 : ℕ) : ℝ)) 2 24 baseCost
  · exact card_generalBidegreeFormIndex A B
  · positivity
  · positivity
  · positivity
  · positivity
  · norm_num
  · norm_num
  · exact fun j => he (r j)
  · exact fun j => hu (r j)
  · exact hcenter
  · exact hscale
  · simpa using hbaseCost

end

end PellPaper
