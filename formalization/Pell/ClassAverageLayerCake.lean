import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# A layer-cake estimate for finite class-number sums

The pointwise estimate proved here is the reciprocal-weight step in the
class-number-average argument of `main.tex`.  All arithmetic and analytic
estimates for the weighted counting function remain separate inputs.
-/

namespace PellPaper

open MeasureTheory Set
open scoped BigOperators Interval

noncomputable section

/-- Integrating the reciprocal square between two positive endpoints. -/
theorem inverse_square_interval_integral {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ θ in a..b, 1 / θ ^ 2) = 1 / a - 1 / b := by
  have h := integral_zpow (a := a) (b := b) (n := -2)
    (Or.inr ⟨by norm_num, notMem_uIcc_of_lt ha hb⟩)
  norm_num [zpow_neg, zpow_ofNat, one_div] at h ⊢
  linarith

/-- Exact evaluation of the moving-threshold kernel. -/
theorem threshold_inverse_square_integral {r₀ r T : ℝ}
    (hr₀ : 0 < r₀) (hr : r₀ ≤ r) (hT : r₀ ≤ T) :
    (∫ θ in r₀..T, if r < θ then 1 / θ ^ 2 else 0) =
      if r ≤ T then 1 / r - 1 / T else 0 := by
  by_cases hrT : r ≤ T
  · rw [if_pos hrT]
    have hinter : Ioi r ∩ Ioc r₀ T = Ioc r T := by
      ext θ
      simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
      constructor
      · rintro ⟨h, _, hT'⟩
        exact ⟨h, hT'⟩
      · rintro ⟨h, hT'⟩
        exact ⟨h, lt_of_le_of_lt hr h, hT'⟩
    calc
      (∫ θ in r₀..T, if r < θ then 1 / θ ^ 2 else 0) =
          ∫ θ in r..T, 1 / θ ^ 2 := by
        change (∫ θ in r₀..T, (Ioi r).indicator (fun θ : ℝ ↦ 1 / θ ^ 2) θ) = _
        rw [intervalIntegral.integral_of_le hT,
          intervalIntegral.integral_of_le hrT,
          MeasureTheory.integral_indicator measurableSet_Ioi,
          Measure.restrict_restrict measurableSet_Ioi, hinter]
      _ = 1 / r - 1 / T :=
        inverse_square_interval_integral (hr₀.trans_le hr) (hr₀.trans_le hT)
  · rw [if_neg hrT]
    calc
      (∫ θ in r₀..T, if r < θ then 1 / θ ^ 2 else 0) = ∫ _ in r₀..T, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro θ hθ
        rw [uIcc_of_le hT] at hθ
        exact if_neg (not_lt_of_ge (hθ.2.trans (le_of_not_ge hrT)))
      _ = 0 := by simp

/-- The reciprocal-weight layer-cake inequality with a strict threshold. -/
theorem one_div_le_cutoff_add_layer_cake {r₀ r T : ℝ}
    (hr₀ : 0 < r₀) (hr : r₀ ≤ r) (hT : r₀ ≤ T) :
    1 / r ≤ 1 / T + ∫ θ in r₀..T, if r < θ then 1 / θ ^ 2 else 0 := by
  rw [threshold_inverse_square_integral hr₀ hr hT]
  split_ifs with hrT
  · linarith
  · simpa only [add_zero] using one_div_le_one_div_of_le (hr₀.trans_le hT)
      (le_of_not_ge hrT)

/-- The choice of strict or nonstrict threshold changes the kernel only at a
single point and therefore does not change its integral. -/
theorem threshold_integral_strict_eq_nonstrict (r₀ r T : ℝ) :
    (∫ θ in r₀..T, if r < θ then 1 / θ ^ 2 else 0) =
      ∫ θ in r₀..T, if r ≤ θ then 1 / θ ^ 2 else 0 := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [volume.ae_ne r] with θ hθ
  intro _
  by_cases h : r < θ
  · simp only [if_pos h, if_pos h.le]
  · have h' : ¬ r ≤ θ := fun h' ↦ hθ (le_antisymm (le_of_not_gt h) h')
    simp only [if_neg h, if_neg h']

/-- The pointwise layer-cake inequality in the nonstrict-threshold convention
used in the manuscript. -/
theorem one_div_le_cutoff_add_layer_cake_nonstrict {r₀ r T : ℝ}
    (hr₀ : 0 < r₀) (hr : r₀ ≤ r) (hT : r₀ ≤ T) :
    1 / r ≤ 1 / T + ∫ θ in r₀..T, if r ≤ θ then 1 / θ ^ 2 else 0 := by
  rw [← threshold_integral_strict_eq_nonstrict]
  exact one_div_le_cutoff_add_layer_cake hr₀ hr hT

/-- The strict threshold used in the integral formulas is interval integrable.
There is no regularity hypothesis on the threshold `r`. -/
theorem intervalIntegrable_threshold_inverse_square {r₀ T : ℝ} (r : ℝ)
    (hr₀ : 0 < r₀) (hT : r₀ ≤ T) :
    IntervalIntegrable (fun θ : ℝ ↦ if r < θ then 1 / θ ^ 2 else 0)
      volume r₀ T := by
  have hk : IntervalIntegrable (fun θ : ℝ ↦ 1 / θ ^ 2) volume r₀ T := by
    have h := intervalIntegral.intervalIntegrable_zpow (a := r₀) (b := T) (n := -2)
      (μ := volume) (Or.inr (notMem_uIcc_of_lt hr₀ (hr₀.trans_le hT)))
    simpa only [zpow_neg, zpow_ofNat, one_div] using h
  exact ⟨hk.1.indicator measurableSet_Ioi, hk.2.indicator measurableSet_Ioi⟩

/-- Weighted finite layer cake: reciprocal denominators are bounded by the total
weight above the cutoff plus the integral of the weighted counting function below
the moving threshold.  In the class-number application the weights are real
quadratic `L`-values and the denominators are normalized regulators. -/
theorem finite_sum_div_le_cutoff_add_layer_cake {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (L r : ι → ℝ) (r₀ T : ℝ)
    (hL : ∀ i ∈ s, 0 ≤ L i) (hr : ∀ i ∈ s, r₀ ≤ r i)
    (hr₀ : 0 < r₀) (hT : r₀ ≤ T) :
    (∑ i ∈ s, L i / r i) ≤ (∑ i ∈ s, L i) / T +
      ∫ θ in r₀..T, (∑ i ∈ s.filter (fun i ↦ r i < θ), L i) / θ ^ 2 := by
  have h_integral :
      (∫ θ in r₀..T, (∑ i ∈ s.filter (fun i ↦ r i < θ), L i) / θ ^ 2) =
        ∑ i ∈ s, L i * ∫ θ in r₀..T, if r i < θ then 1 / θ ^ 2 else 0 := by
    calc
      _ = ∫ θ in r₀..T, ∑ i ∈ s, L i * (if r i < θ then 1 / θ ^ 2 else 0) := by
        apply intervalIntegral.integral_congr
        intro θ _
        dsimp only
        rw [Finset.sum_filter, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        split_ifs <;> simp [div_eq_mul_inv]
      _ = ∑ i ∈ s, ∫ θ in r₀..T, L i * (if r i < θ then 1 / θ ^ 2 else 0) :=
        intervalIntegral.integral_finsetSum fun i _ ↦
          (intervalIntegrable_threshold_inverse_square (r i) hr₀ hT).const_mul (L i)
      _ = _ := by simp only [intervalIntegral.integral_const_mul]
  rw [h_integral]
  calc
    (∑ i ∈ s, L i / r i) ≤
        ∑ i ∈ s, L i * (1 / T + ∫ θ in r₀..T, if r i < θ then 1 / θ ^ 2 else 0) := by
      apply Finset.sum_le_sum
      intro i hi
      simpa only [mul_one_div] using
        mul_le_mul_of_nonneg_left (one_div_le_cutoff_add_layer_cake hr₀ (hr i hi) hT)
          (hL i hi)
    _ = _ := by simp only [mul_add, mul_one_div, Finset.sum_add_distrib, Finset.sum_div]

/-- Combine pointwise class-number-formula bounds with the weighted layer cake.
This is the exact finite manipulation used after the analytic estimates for the
weighted exceptional subfamilies have been supplied. -/
theorem finite_sum_class_bound_layer_cake {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (h L r : ι → ℝ) (A r₀ T : ℝ)
    (hA : 0 ≤ A)
    (hL : ∀ i ∈ s, 0 ≤ L i)
    (hr : ∀ i ∈ s, r₀ ≤ r i)
    (hr₀ : 0 < r₀) (hT : r₀ ≤ T)
    (hpoint : ∀ i ∈ s, h i ≤ A * (L i / r i)) :
    (∑ i ∈ s, h i) ≤ A * ((∑ i ∈ s, L i) / T +
      ∫ θ in r₀..T, (∑ i ∈ s.filter (fun i ↦ r i < θ), L i) / θ ^ 2) := by
  calc
    (∑ i ∈ s, h i) ≤ ∑ i ∈ s, A * (L i / r i) := by
      exact Finset.sum_le_sum fun i hi ↦ hpoint i hi
    _ = A * ∑ i ∈ s, L i / r i := by
      rw [Finset.mul_sum]
    _ ≤ A * ((∑ i ∈ s, L i) / T +
        ∫ θ in r₀..T, (∑ i ∈ s.filter (fun i ↦ r i < θ), L i) / θ ^ 2) := by
      exact mul_le_mul_of_nonneg_left
        (finite_sum_div_le_cutoff_add_layer_cake s L r r₀ T hL hr hr₀ hT) hA

end

end PellPaper
