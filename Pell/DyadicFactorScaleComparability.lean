import Pell.DyadicLocalCenterScale

/-!
# Dyadic scale comparability from the Pell factor equation

For a positive tuple satisfying one of the four factor equations
`e^2 v - d^2 u ∈ {±1, ±2}`, the two point-scale products are comparable.
After putting the tuple in a dyadic box, this gives the literal endpoint
comparison

`E^2 V ≤ 24 (D^2 U)` and `D^2 U ≤ 24 (E^2 V)`.

This is enough to replace the raw premise `32 X ≤ D^2 U` in the local
coordinate calculation by `768 X ≤ E^2 V`.  The latter is still an explicit
choice of a *rescaled* local parameter: the manuscript's literal scale is
`x = E^2 V`, so this file does not assert `32 x ≤ D^2 U` or hide the fixed
constant in an asymptotic notation.
-/

namespace PellPaper

/-- Two quantities at least one whose difference has absolute value at most
two are comparable with the concrete factor three. -/
theorem scale_products_comparable_of_abs_sub_le_two {a b : ℝ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hclose : |a - b| ≤ 2) :
    a ≤ 3 * b ∧ b ≤ 3 * a := by
  rw [abs_le] at hclose
  constructor <;> nlinarith

/-- The four Pell factor differences make the two point-scale products
comparable.  Positivity from `DyadicFactorCondition` supplies the lower bound
one needed to absorb the additive error two. -/
theorem dyadicFactorCondition_point_scale_products_comparable
    {θ : ℝ} {Y d e u v : ℕ}
    (hcond : DyadicFactorCondition θ Y d e u v) :
    (e : ℝ) ^ 2 * (v : ℝ) ≤ 3 * ((d : ℝ) ^ 2 * (u : ℝ)) ∧
      (d : ℝ) ^ 2 * (u : ℝ) ≤ 3 * ((e : ℝ) ^ 2 * (v : ℝ)) := by
  obtain ⟨h, hh, hdiff⟩ := dyadicFactorCondition_exists_difference hcond
  have hhabs : |(h : ℝ)| ≤ 2 := by
    rcases hh with rfl | rfl | rfl | rfl <;> norm_num
  have hdiffR :
      (e : ℝ) ^ 2 * (v : ℝ) - (d : ℝ) ^ 2 * (u : ℝ) = (h : ℝ) := by
    exact_mod_cast hdiff
  have heone : (1 : ℝ) ≤ (e : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hcond.2.1))
  have hvone : (1 : ℝ) ≤ (v : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hcond.2.2.2.1))
  have hdone : (1 : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hcond.1))
  have huone : (1 : ℝ) ≤ (u : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hcond.2.2.1))
  have hesqone : (1 : ℝ) ≤ (e : ℝ) ^ 2 :=
    one_le_pow₀ heone
  have hdsqone : (1 : ℝ) ≤ (d : ℝ) ^ 2 :=
    one_le_pow₀ hdone
  have hevo : (1 : ℝ) ≤ (e : ℝ) ^ 2 * (v : ℝ) :=
    one_le_mul_of_one_le_of_one_le hesqone hvone
  have hduo : (1 : ℝ) ≤ (d : ℝ) ^ 2 * (u : ℝ) :=
    one_le_mul_of_one_le_of_one_le hdsqone huone
  apply scale_products_comparable_of_abs_sub_le_two hevo hduo
  rw [hdiffR]
  exact hhabs

/-- Membership of a four-coordinate dyadic box supplies its four closed
upper bounds, written using the lower endpoints. -/
theorem dyadicBox_coordinate_upper_bounds
    {i : ℕ × ℕ × ℕ × ℕ} {d e u v : ℕ}
    (hbox : (d, e, u, v) ∈ dyadicBox i) :
    d ≤ 2 * 2 ^ i.1 ∧ e ≤ 2 * 2 ^ i.2.1 ∧
      u ≤ 2 * 2 ^ i.2.2.1 ∧ v ≤ 2 * 2 ^ i.2.2.2 := by
  unfold dyadicBox at hbox
  rcases Finset.mem_product.mp hbox with ⟨hd, hrest⟩
  rcases Finset.mem_product.mp hrest with ⟨he, hrest⟩
  rcases Finset.mem_product.mp hrest with ⟨hu, hv⟩
  refine ⟨Nat.le_of_lt (by
    simpa [pow_succ, Nat.succ_eq_add_one, Nat.mul_comm] using (Finset.mem_Ico.mp hd).2), ?_⟩
  refine ⟨Nat.le_of_lt (by
    simpa [pow_succ, Nat.succ_eq_add_one, Nat.mul_comm] using (Finset.mem_Ico.mp he).2), ?_⟩
  refine ⟨Nat.le_of_lt (by
    simpa [pow_succ, Nat.succ_eq_add_one, Nat.mul_comm] using (Finset.mem_Ico.mp hu).2), ?_⟩
  exact Nat.le_of_lt (by
    simpa [pow_succ, Nat.succ_eq_add_one, Nat.mul_comm] using (Finset.mem_Ico.mp hv).2)

/-- The exact Pell factor equation and dyadic endpoints give a concrete
two-sided comparison of the source and target scale products.  This is the
literal version of the manuscript's `E²V \asymp D²U` on a nonempty factor
box; it uses no determinant or asymptotic input. -/
theorem dyadicFactorCondition_dyadicBox_endpoint_scales_comparable
    {θ : ℝ} {Y d e u v : ℕ} {i : ℕ × ℕ × ℕ × ℕ}
    (hcond : DyadicFactorCondition θ Y d e u v)
    (hbox : (d, e, u, v) ∈ dyadicBox i) :
    ((2 ^ i.2.1 : ℕ) : ℝ) ^ 2 * ((2 ^ i.2.2.2 : ℕ) : ℝ) ≤
        24 * (((2 ^ i.1 : ℕ) : ℝ) ^ 2 * ((2 ^ i.2.2.1 : ℕ) : ℝ)) ∧
      ((2 ^ i.1 : ℕ) : ℝ) ^ 2 * ((2 ^ i.2.2.1 : ℕ) : ℝ) ≤
        24 * (((2 ^ i.2.1 : ℕ) : ℝ) ^ 2 * ((2 ^ i.2.2.2 : ℕ) : ℝ)) := by
  let D : ℝ := ((2 ^ i.1 : ℕ) : ℝ)
  let E : ℝ := ((2 ^ i.2.1 : ℕ) : ℝ)
  let U : ℝ := ((2 ^ i.2.2.1 : ℕ) : ℝ)
  let V : ℝ := ((2 ^ i.2.2.2 : ℕ) : ℝ)
  change E ^ 2 * V ≤ 24 * (D ^ 2 * U) ∧ D ^ 2 * U ≤ 24 * (E ^ 2 * V)
  have hpoint := dyadicFactorCondition_point_scale_products_comparable hcond
  have hlower := dyadicBox_coordinate_lower_bounds hbox
  have hupper := dyadicBox_coordinate_upper_bounds hbox
  have hDpos : 0 < D := by
    dsimp [D]
    positivity
  have hEpos : 0 < E := by
    dsimp [E]
    positivity
  have hUpos : 0 < U := by
    dsimp [U]
    positivity
  have hVpos : 0 < V := by
    dsimp [V]
    positivity
  have hDle : D ≤ (d : ℝ) := by
    dsimp [D]
    exact_mod_cast hlower.1
  have hEle : E ≤ (e : ℝ) := by
    dsimp [E]
    exact_mod_cast hlower.2.1
  have hUle : U ≤ (u : ℝ) := by
    dsimp [U]
    exact_mod_cast hlower.2.2.1
  have hVle : V ≤ (v : ℝ) := by
    dsimp [V]
    exact_mod_cast hlower.2.2.2
  have hdle : (d : ℝ) ≤ 2 * D := by
    dsimp [D]
    exact_mod_cast hupper.1
  have hele : (e : ℝ) ≤ 2 * E := by
    dsimp [E]
    exact_mod_cast hupper.2.1
  have hule : (u : ℝ) ≤ 2 * U := by
    dsimp [U]
    exact_mod_cast hupper.2.2.1
  have hvle : (v : ℝ) ≤ 2 * V := by
    dsimp [V]
    exact_mod_cast hupper.2.2.2
  have hEev : E ^ 2 * V ≤ (e : ℝ) ^ 2 * (v : ℝ) := by
    apply mul_le_mul
    · exact pow_le_pow_left₀ hEpos.le hEle 2
    · exact hVle
    · exact hVpos.le
    · exact sq_nonneg _
  have hDdu : D ^ 2 * U ≤ (d : ℝ) ^ 2 * (u : ℝ) := by
    apply mul_le_mul
    · exact pow_le_pow_left₀ hDpos.le hDle 2
    · exact hUle
    · exact hUpos.le
    · exact sq_nonneg _
  have hdu_upper : (d : ℝ) ^ 2 * (u : ℝ) ≤ (2 * D) ^ 2 * (2 * U) := by
    apply mul_le_mul
    · exact pow_le_pow_left₀ (by positivity) hdle 2
    · exact hule
    · positivity
    · exact sq_nonneg _
  have hev_upper : (e : ℝ) ^ 2 * (v : ℝ) ≤ (2 * E) ^ 2 * (2 * V) := by
    apply mul_le_mul
    · exact pow_le_pow_left₀ (by positivity) hele 2
    · exact hvle
    · positivity
    · exact sq_nonneg _
  constructor
  · calc
      E ^ 2 * V ≤ (e : ℝ) ^ 2 * (v : ℝ) := hEev
      _ ≤ 3 * ((d : ℝ) ^ 2 * (u : ℝ)) := hpoint.1
      _ ≤ 3 * ((2 * D) ^ 2 * (2 * U)) :=
        mul_le_mul_of_nonneg_left hdu_upper (by norm_num)
      _ = 24 * (D ^ 2 * U) := by ring
  · calc
      D ^ 2 * U ≤ (d : ℝ) ^ 2 * (u : ℝ) := hDdu
      _ ≤ 3 * ((e : ℝ) ^ 2 * (v : ℝ)) := hpoint.2
      _ ≤ 3 * ((2 * E) ^ 2 * (2 * V)) :=
        mul_le_mul_of_nonneg_left hev_upper (by norm_num)
      _ = 24 * (E ^ 2 * V) := by ring

/-- A local parameter no more than `E²V / 768` has enough denominator scale
in every positive Pell factor box.  The fixed factor is completely explicit:
it is `32` from the centre/endpoint loss and `24` from box comparability. -/
theorem dyadicFactorCondition_source_scale_lower_bound_of_dyadicBox
    {θ : ℝ} {Y d e u v : ℕ} {i : ℕ × ℕ × ℕ × ℕ} {X : ℝ}
    (hcond : DyadicFactorCondition θ Y d e u v)
    (hbox : (d, e, u, v) ∈ dyadicBox i)
    (hXscale : 768 * X ≤ ((2 ^ i.2.1 : ℕ) : ℝ) ^ 2 *
      ((2 ^ i.2.2.2 : ℕ) : ℝ)) :
    32 * X ≤ ((2 ^ i.1 : ℕ) : ℝ) ^ 2 * ((2 ^ i.2.2.1 : ℕ) : ℝ) := by
  have hcompare := dyadicFactorCondition_dyadicBox_endpoint_scales_comparable hcond hbox
  nlinarith [hcompare.1]

/-- Combining the factor-equation comparison with a localized source interval
supplies the full denominator hypothesis used by the local logarithm bridge.
The remaining input is the explicit rescaled choice `768 X ≤ E²V`, not an
unproved assertion that the manuscript's unrescaled `x = E²V` itself meets
the stronger `32 X ≤ D²U` inequality. -/
theorem two_mul_le_local_displacement_denominator_of_dyadicBox_localized_source_scale
    {θ : ℝ} {Y d e u v : ℕ} {i : ℕ × ℕ × ℕ × ℕ} {s₀ M X : ℝ}
    (hcond : DyadicFactorCondition θ Y d e u v)
    (hbox : (d, e, u, v) ∈ dyadicBox i)
    (hM : 1 ≤ M)
    (hupper : (d : ℝ) / (e : ℝ) ≤ s₀ * (1 + 1 / M))
    (hXscale : 768 * X ≤ ((2 ^ i.2.1 : ℕ) : ℝ) ^ 2 *
      ((2 ^ i.2.2.2 : ℕ) : ℝ)) :
    2 * X ≤ s₀ ^ 2 * (e : ℝ) ^ 2 * (u : ℝ) := by
  apply two_mul_le_local_displacement_denominator_of_dyadicBox_localized_source
    hbox hM hupper
  exact dyadicFactorCondition_source_scale_lower_bound_of_dyadicBox
    hcond hbox hXscale

end PellPaper
