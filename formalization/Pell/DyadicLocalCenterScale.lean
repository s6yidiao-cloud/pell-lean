import Pell.DyadicLocalBoxScale

/-!
# A dyadic lower scale for a localized source centre

For a localized source coordinate, the upper interval endpoint and the
lower/upper endpoints of a dyadic `d,e` box force a lower bound for the
chosen centre `s₀`.  The constants are deliberately literal: from
`d / e ≤ s₀ (1 + M⁻¹)`, `M ≥ 1`, `d ≥ D`, and `e < 2 E`, one gets
`D / (4 E) ≤ s₀`.

The final theorem converts this lower centre scale and the `e,u` box lower
endpoints into the displacement-denominator condition.  Its hypothesis
`32 X ≤ D² U` is an explicit source-side scale comparison; this module does
not derive it from the dyadic box or identify `X` with the manuscript's
`E² V \asymp D² U` scale.
-/

namespace PellPaper

/-- A localized source upper endpoint, with positive numerator and
denominator, forces the elementary lower centre bound `d / (2e) ≤ s₀`.
The only use of `M ≥ 1` is the literal estimate `1 + M⁻¹ ≤ 2`. -/
theorem local_center_lower_bound_of_localized_source_upper
    {s₀ M : ℝ} {d e : ℕ}
    (hd : 0 < d) (he : 0 < e) (hM : 1 ≤ M)
    (hupper : (d : ℝ) / (e : ℝ) ≤ s₀ * (1 + 1 / M)) :
    (d : ℝ) / (2 * (e : ℝ)) ≤ s₀ := by
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hfactor_pos : 0 < 1 + 1 / M := by positivity
  have hfactor_le : 1 + 1 / M ≤ 2 := by
    have hone_div : 1 / M ≤ 1 := by
      apply (div_le_iff₀ hMpos).mpr
      simpa using hM
    linarith
  have hdRpos : 0 < (d : ℝ) := by exact_mod_cast hd
  have heRpos : 0 < (e : ℝ) := by exact_mod_cast he
  have hratio_pos : 0 < (d : ℝ) / (e : ℝ) := div_pos hdRpos heRpos
  have hproduct_pos : 0 < s₀ * (1 + 1 / M) :=
    lt_of_lt_of_le hratio_pos hupper
  have hs₀ : 0 < s₀ := by
    rcases (mul_pos_iff.mp hproduct_pos) with h | h
    · exact h.1
    · exact False.elim ((not_lt_of_ge hfactor_pos.le) h.2)
  have hratio_le : (d : ℝ) / (e : ℝ) ≤ 2 * s₀ := by
    calc
      (d : ℝ) / (e : ℝ) ≤ s₀ * (1 + 1 / M) := hupper
      _ ≤ s₀ * 2 := mul_le_mul_of_nonneg_left hfactor_le hs₀.le
      _ = 2 * s₀ := by ring
  apply (div_le_iff₀ (mul_pos (by norm_num) heRpos)).mpr
  calc
    (d : ℝ) = ((d : ℝ) / (e : ℝ)) * (e : ℝ) := by
      field_simp [heRpos.ne']
    _ ≤ (2 * s₀) * (e : ℝ) :=
      mul_le_mul_of_nonneg_right hratio_le heRpos.le
    _ = s₀ * (2 * (e : ℝ)) := by ring

/-- In a dyadic box, a localized source upper endpoint gives the concrete
centre lower scale
`2^i_d / (4 · 2^i_e) ≤ s₀`.  The proof uses the lower endpoint for `d` and
the upper endpoint for `e`; no product-scale relation is involved. -/
theorem dyadicBox_center_lower_bound_of_localized_source_upper
    {i : ℕ × ℕ × ℕ × ℕ} {d e u v : ℕ} {s₀ M : ℝ}
    (hbox : (d, e, u, v) ∈ dyadicBox i)
    (hM : 1 ≤ M)
    (hupper : (d : ℝ) / (e : ℝ) ≤ s₀ * (1 + 1 / M)) :
    ((2 ^ i.1 : ℕ) : ℝ) /
        (4 * ((2 ^ i.2.1 : ℕ) : ℝ)) ≤ s₀ := by
  have hbox_lower := dyadicBox_coordinate_lower_bounds hbox
  have hDpos : 0 < 2 ^ i.1 := by positivity
  have hEpos : 0 < 2 ^ i.2.1 := by positivity
  have hd : 0 < d := lt_of_lt_of_le hDpos hbox_lower.1
  have he : 0 < e := lt_of_lt_of_le hEpos hbox_lower.2.1
  have hlocal := local_center_lower_bound_of_localized_source_upper
    hd he hM hupper
  have he_box_upper : e < 2 ^ (i.2.1 + 1) := by
    unfold dyadicBox at hbox
    rcases Finset.mem_product.mp hbox with ⟨_, hrest⟩
    rcases Finset.mem_product.mp hrest with ⟨he_mem, _⟩
    exact (Finset.mem_Ico.mp he_mem).2
  have he_upper_nat : e ≤ 2 * (2 ^ i.2.1) := by
    apply Nat.le_of_lt
    simpa [pow_succ, Nat.succ_eq_add_one, Nat.mul_comm] using he_box_upper
  have hDle : ((2 ^ i.1 : ℕ) : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast hbox_lower.1
  have he_upper : (e : ℝ) ≤ 2 * ((2 ^ i.2.1 : ℕ) : ℝ) := by
    exact_mod_cast he_upper_nat
  have hDposR : 0 < ((2 ^ i.1 : ℕ) : ℝ) := by positivity
  have hEposR : 0 < ((2 ^ i.2.1 : ℕ) : ℝ) := by positivity
  have hdRnonneg : 0 ≤ (d : ℝ) := by positivity
  have heRpos : 0 < (e : ℝ) := by exact_mod_cast he
  have hendpoint :
      ((2 ^ i.1 : ℕ) : ℝ) /
          (4 * ((2 ^ i.2.1 : ℕ) : ℝ)) ≤
        (d : ℝ) / (2 * (e : ℝ)) := by
    apply (div_le_div_iff₀
      (mul_pos (by norm_num) hEposR)
      (mul_pos (by norm_num) heRpos)).mpr
    calc
      ((2 ^ i.1 : ℕ) : ℝ) * (2 * (e : ℝ)) ≤
          (d : ℝ) * (2 * (e : ℝ)) :=
        mul_le_mul_of_nonneg_right hDle (by positivity)
      _ ≤ (d : ℝ) * (4 * ((2 ^ i.2.1 : ℕ) : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hdRnonneg
        nlinarith [he_upper]
  exact hendpoint.trans hlocal

/-- A local source interval in a dyadic box supplies the denominator scale
needed for the `T - S²` displacement estimate once the explicit lower
scale comparison `32 X ≤ D² U` is given, where `D,E,U` are the lower
dyadic endpoints.  This is a conditional transport of the source scale;
the comparison itself remains an external input. -/
theorem two_mul_le_local_displacement_denominator_of_dyadicBox_localized_source
    {i : ℕ × ℕ × ℕ × ℕ} {d e u v : ℕ} {s₀ M X : ℝ}
    (hbox : (d, e, u, v) ∈ dyadicBox i)
    (hM : 1 ≤ M)
    (hupper : (d : ℝ) / (e : ℝ) ≤ s₀ * (1 + 1 / M))
    (hsource_scale : 32 * X ≤
      ((2 ^ i.1 : ℕ) : ℝ) ^ 2 * ((2 ^ i.2.2.1 : ℕ) : ℝ)) :
    2 * X ≤ s₀ ^ 2 * (e : ℝ) ^ 2 * (u : ℝ) := by
  have hbox_lower := dyadicBox_coordinate_lower_bounds hbox
  have hDpos : 0 < ((2 ^ i.1 : ℕ) : ℝ) := by positivity
  have hEpos : 0 < ((2 ^ i.2.1 : ℕ) : ℝ) := by positivity
  have hUpos : 0 < ((2 ^ i.2.2.1 : ℕ) : ℝ) := by positivity
  have hsₗ_pos : 0 <
      ((2 ^ i.1 : ℕ) : ℝ) /
        (4 * ((2 ^ i.2.1 : ℕ) : ℝ)) :=
    div_pos hDpos (mul_pos (by norm_num) hEpos)
  have hsₗ := dyadicBox_center_lower_bound_of_localized_source_upper
    hbox hM hupper
  have he_lower : ((2 ^ i.2.1 : ℕ) : ℝ) ≤ (e : ℝ) := by
    exact_mod_cast hbox_lower.2.1
  have hu_lower : ((2 ^ i.2.2.1 : ℕ) : ℝ) ≤ (u : ℝ) := by
    exact_mod_cast hbox_lower.2.2.1
  have hbase_scale : 2 * X ≤
      (((2 ^ i.1 : ℕ) : ℝ) /
        (4 * ((2 ^ i.2.1 : ℕ) : ℝ))) ^ 2 *
          ((2 ^ i.2.1 : ℕ) : ℝ) ^ 2 *
            ((2 ^ i.2.2.1 : ℕ) : ℝ) := by
    have hidentity :
        (((2 ^ i.1 : ℕ) : ℝ) /
          (4 * ((2 ^ i.2.1 : ℕ) : ℝ))) ^ 2 *
            ((2 ^ i.2.1 : ℕ) : ℝ) ^ 2 *
              ((2 ^ i.2.2.1 : ℕ) : ℝ) =
          (((2 ^ i.1 : ℕ) : ℝ) ^ 2 *
            ((2 ^ i.2.2.1 : ℕ) : ℝ)) / 16 := by
      field_simp [hEpos.ne']
      ring
    rw [hidentity]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 16)).mpr
    nlinarith [hsource_scale]
  exact two_mul_le_local_displacement_denominator_of_lower_scales
    hsₗ_pos hEpos hUpos hsₗ he_lower hu_lower hbase_scale

end PellPaper
