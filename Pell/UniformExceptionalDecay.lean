import Pell.UniformExceptional

/-!
# Exponential decay from the uniform exceptional-set bound

The uniform estimate has a saving expressed using the ceiling parameter `Q`.
This file proves the elementary conversion to an exponential bound after
division by `X`.  The uniform estimate itself remains an explicit hypothesis.
-/

open Filter

namespace PellPaper

/-- In the range relevant to the uniform estimate, `Q(θ) ≤ θ + 1`. -/
theorem uniformQ_le_theta_add_one {θ : ℝ} (hθ : 3 ≤ θ) :
    (uniformQ θ : ℝ) ≤ θ + 1 := by
  linarith [uniformQ_lt_add_one hθ]

/-- Replacing `Q²` by `(θ + 1)²` weakens a nonnegative saving. -/
theorem uniformQ_saving_ge {θ c : ℝ} (hθ : 3 ≤ θ) (hc : 0 ≤ c) :
    c / (θ + 1) ^ 2 ≤ c / (uniformQ θ : ℝ) ^ 2 := by
  have hQ := uniformQ_pos hθ
  have hQle := uniformQ_le_theta_add_one hθ
  have hsq : (uniformQ θ : ℝ) ^ 2 ≤ (θ + 1) ^ 2 := by
    nlinarith
  exact div_le_div_of_nonneg_left hc (sq_pos_of_pos hQ) hsq

/-- The normalized power in the uniform estimate is exactly an exponential. -/
theorem normalized_uniform_power {θ c X : ℝ} (hX : 0 < X) :
    X ^ (1 - c / (uniformQ θ : ℝ) ^ 2) / X =
      Real.exp (-c * Real.log X / (uniformQ θ : ℝ) ^ 2) := by
  rw [← Real.rpow_sub_one (ne_of_gt hX), Real.rpow_def_of_pos hX]
  congr 1
  ring

/-- A pointwise uniform exceptional-set estimate gives normalized exponential
decay, with the same nonnegative saving constant `c`. -/
theorem exceptional_ratio_le_exp {θ c C X : ℝ}
    (hθ : 3 ≤ θ) (hc : 0 ≤ c) (hC : 0 ≤ C) (hX : 1 ≤ X)
    (hbound : E θ X ≤ C * X ^ (1 - c / (uniformQ θ : ℝ) ^ 2)) :
    E θ X / X ≤ C * Real.exp (-c * Real.log X / (θ + 1) ^ 2) := by
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hlog : 0 ≤ Real.log X := Real.log_nonneg hX
  have hsaving := uniformQ_saving_ge hθ hc
  have hexponent :
      -c * Real.log X / (uniformQ θ : ℝ) ^ 2 ≤
        -c * Real.log X / (θ + 1) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hsaving hlog
    calc
      -c * Real.log X / (uniformQ θ : ℝ) ^ 2 =
          -(c / (uniformQ θ : ℝ) ^ 2 * Real.log X) := by ring
      _ ≤ -(c / (θ + 1) ^ 2 * Real.log X) := neg_le_neg hmul
      _ = -c * Real.log X / (θ + 1) ^ 2 := by ring
  calc
    E θ X / X ≤ (C * X ^ (1 - c / (uniformQ θ : ℝ) ^ 2)) / X :=
      div_le_div_of_nonneg_right hbound (le_of_lt hXpos)
    _ = C * Real.exp (-c * Real.log X / (uniformQ θ : ℝ) ^ 2) := by
      rw [mul_div_assoc, normalized_uniform_power hXpos]
    _ ≤ C * Real.exp (-c * Real.log X / (θ + 1) ^ 2) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) hC

/-- The constants and the common cutoff remain uniform in `θ` when converting
`UniformExceptionalEstimate` to normalized exponential decay. -/
theorem uniformExceptionalEstimate_normalized {cSave : ℝ}
    (h : UniformExceptionalEstimate cSave) :
    ∃ cExc C : ℝ, 0 < cExc ∧ 0 < C ∧
      ∀ᶠ X : ℝ in atTop, ∀ θ : ℝ, 3 ≤ θ →
        UniformAdmissible cExc θ X →
          E θ X / X ≤ C * Real.exp (-cSave * Real.log X / (θ + 1) ^ 2) := by
  obtain ⟨hcSave, cExc, C, hcExc, hC, hbound⟩ := h
  refine ⟨cExc, C, hcExc, hC, ?_⟩
  filter_upwards [hbound, eventually_ge_atTop (1 : ℝ)] with X hbound hX
  intro θ hθ hadmissible
  exact exceptional_ratio_le_exp hθ hcSave.le hC.le hX (hbound θ hθ hadmissible)

end PellPaper
