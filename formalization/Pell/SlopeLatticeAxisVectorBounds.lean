import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Int.Cast.Lemmas

/-!
# Exact axis-vector thresholds for the normalized slope map

These are literal evaluations and existence criteria for nonzero integer
vectors on either coordinate axis.  They do not define or assume a lattice
minimum, and do not count centers or curve points.
-/

namespace PellPaper

/-- On the horizontal integer axis the normalized sup norm is exactly
`(M/V)*|a|`. -/
theorem slope_vector_sup_norm_fst_axis
    (U V M z : ℝ) (hV : 0 < V) (hM : 0 ≤ M) (a : ℤ) :
    max |M * (a : ℝ) / V - z * (0 : ℤ) / U| |((0 : ℤ) : ℝ) / U| =
      (M / V) * |(a : ℝ)| := by
  simp only [Int.cast_zero, mul_zero, zero_div, sub_zero, abs_zero]
  rw [max_eq_left (abs_nonneg _), abs_div, abs_mul, abs_of_nonneg hM, abs_of_pos hV]
  ring

/-- On the vertical integer axis the normalized sup norm is exactly
`max |z| 1 / U` times `|b|`. -/
theorem slope_vector_sup_norm_snd_axis
    (U V M z : ℝ) (hU : 0 < U) (b : ℤ) :
    max |M * (0 : ℤ) / V - z * (b : ℝ) / U| |(b : ℝ) / U| =
      (max |z| 1 / U) * |(b : ℝ)| := by
  simp only [Int.cast_zero, mul_zero, zero_div, zero_sub, abs_neg, abs_div,
    abs_mul, abs_of_pos hU]
  have hb : 0 ≤ |(b : ℝ)| / U := by positivity
  calc
    max (|z| * |(b : ℝ)| / U) (|(b : ℝ)| / U) =
        max (|z| * (|(b : ℝ)| / U)) (1 * (|(b : ℝ)| / U)) := by ring_nf
    _ = max |z| 1 * (|(b : ℝ)| / U) := (max_mul_of_nonneg _ _ hb).symm
    _ = (max |z| 1 / U) * |(b : ℝ)| := by ring

/-- Existence of a nonzero horizontal-axis integer vector below a real
radius is equivalent to the exact horizontal-axis threshold. -/
theorem exists_fst_axis_slope_vector_iff
    (U V M z R : ℝ) (hV : 0 < V) (hM : 0 ≤ M) :
    (∃ a : ℤ, a ≠ 0 ∧
      max |M * (a : ℝ) / V - z * (0 : ℤ) / U| |((0 : ℤ) : ℝ) / U| ≤ R) ↔
      M / V ≤ R := by
  simp_rw [slope_vector_sup_norm_fst_axis U V M z hV hM]
  constructor
  · rintro ⟨a, ha, hbound⟩
    have haone : (1 : ℝ) ≤ |(a : ℝ)| := by exact_mod_cast Int.one_le_abs ha
    calc
      M / V = (M / V) * 1 := by ring
      _ ≤ (M / V) * |(a : ℝ)| := mul_le_mul_of_nonneg_left haone (div_nonneg hM hV.le)
      _ ≤ R := hbound
  · intro hbound
    exact ⟨1, by norm_num, by simpa using hbound⟩

/-- Existence of a nonzero vertical-axis integer vector below a real
radius is equivalent to the exact vertical-axis threshold. -/
theorem exists_snd_axis_slope_vector_iff
    (U V M z R : ℝ) (hU : 0 < U) :
    (∃ b : ℤ, b ≠ 0 ∧
      max |M * (0 : ℤ) / V - z * (b : ℝ) / U| |(b : ℝ) / U| ≤ R) ↔
      max |z| 1 / U ≤ R := by
  simp_rw [slope_vector_sup_norm_snd_axis U V M z hU]
  constructor
  · rintro ⟨b, hb, hbound⟩
    have hbone : (1 : ℝ) ≤ |(b : ℝ)| := by exact_mod_cast Int.one_le_abs hb
    calc
      max |z| 1 / U = (max |z| 1 / U) * 1 := by ring
      _ ≤ (max |z| 1 / U) * |(b : ℝ)| := mul_le_mul_of_nonneg_left hbone (by positivity)
      _ ≤ R := hbound
  · intro hbound
    exact ⟨1, by norm_num, by simpa using hbound⟩

end PellPaper
