import Pell.SeparatedRealCenterCounting

/-!
# Quadratic transport of separated source centers

On `z ≥ M/2`, the actual quadratic map `F(z)=R*z²/M` expands distances
by at least `R`.  Its inverse image of a bounded real window therefore
has an explicit finite-index multiplicity bound.  This does not identify
source indices with an integer grid and does not yet transfer any points.
-/

namespace PellPaper

noncomputable section

/-- The normalized quadratic source-to-target center map. -/
def quadraticTargetCenter (M R z : ℝ) : ℝ := R * z ^ 2 / M

/-- Genuine distance expansion on the positive source-center range. -/
theorem quadraticTargetCenter_separation
    (M R z w : ℝ) (hM : 0 < M) (hR : 0 ≤ R)
    (hz : M / 2 ≤ z) (hw : M / 2 ≤ w) :
    R * |z - w| ≤ |quadraticTargetCenter M R z - quadraticTargetCenter M R w| := by
  have hsum : M ≤ z + w := by linarith
  have hsumpos : 0 < z + w := hM.trans_le hsum
  have hid : quadraticTargetCenter M R z - quadraticTargetCenter M R w =
      (R / M) * (z - w) * (z + w) := by dsimp [quadraticTargetCenter]; ring
  rw [hid, abs_mul, abs_mul, abs_of_nonneg (div_nonneg hR hM.le), abs_of_pos hsumpos]
  calc
    R * |z - w| = (R / M) * |z - w| * M := by field_simp
    _ ≤ (R / M) * |z - w| * (z + w) := mul_le_mul_of_nonneg_left hsum (by positivity)

/-- Actual source indices whose quadratic center lies in the indicated window. -/
def quadraticTargetWindowIndices {ι : Type*}
    (J : Finset ι) (z : ι → ℝ) (M R k A : ℝ) : Finset ι := by
  classical
  exact J.filter fun i => |quadraticTargetCenter M R (z i) - k| ≤ A

/-- A target window has finite source-index multiplicity controlled by
the quadratic expansion and the actual source-center separation. -/
theorem card_quadraticTargetWindowIndices_le
    {ι : Type*} (J : Finset ι) (z : ι → ℝ) (M R k A sep : ℝ)
    (hM : 0 < M) (hR : 0 < R) (hA : 0 ≤ A) (hsep : 0 < sep)
    (hz : ∀ i ∈ J, M / 2 ≤ z i)
    (hseparated : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → sep ≤ |z i - z j|) :
    ((quadraticTargetWindowIndices J z M R k A).card : ℝ) ≤ 1 + 2 * A / (R * sep) := by
  classical
  have hbound := card_le_one_add_div_of_separated_real_centers
    (quadraticTargetWindowIndices J z M R k A) (fun i => quadraticTargetCenter M R (z i))
    (k - A) (k + A) (R * sep) (mul_pos hR hsep) (by linarith) (by
      intro i hi
      have hwindow := abs_le.mp (Finset.mem_filter.mp hi).2
      constructor <;> linarith) (by
      intro i hi j hj hij
      have hiJ := (Finset.mem_filter.mp hi).1
      have hjJ := (Finset.mem_filter.mp hj).1
      exact (mul_le_mul_of_nonneg_left (hseparated i hiJ j hjJ hij) hR.le).trans
        (quadraticTargetCenter_separation M R (z i) (z j) hM hR.le (hz i hiJ) (hz j hjJ)))
  convert hbound using 1; ring

/-- The explicit uniform multiplicity used for a width `12R+3` window,
source separation one half, and scale ratio at least one twenty-fourth. -/
theorem card_quadraticTargetWindowIndices_le_337
    {ι : Type*} (J : Finset ι) (z : ι → ℝ) (M R k : ℝ)
    (hM : 0 < M) (hR : 1 / 24 ≤ R)
    (hz : ∀ i ∈ J, M / 2 ≤ z i)
    (hseparated : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → (1 / 2 : ℝ) ≤ |z i - z j|) :
    (quadraticTargetWindowIndices J z M R k (12 * R + 3)).card ≤ 337 := by
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) hR
  have hbound := card_quadraticTargetWindowIndices_le J z M R k (12 * R + 3) (1 / 2)
    hM hRpos (by positivity) (by norm_num) hz hseparated
  have hinv : 12 / R ≤ 288 := (div_le_iff₀ hRpos).mpr (by nlinarith)
  have heq : 1 + 2 * (12 * R + 3) / (R * (1 / 2)) = 49 + 12 / R := by field_simp; ring
  rw [heq] at hbound
  have hreal : ((quadraticTargetWindowIndices J z M R k (12 * R + 3)).card : ℝ) ≤ 337 := by linarith
  exact_mod_cast hreal

end

end PellPaper
