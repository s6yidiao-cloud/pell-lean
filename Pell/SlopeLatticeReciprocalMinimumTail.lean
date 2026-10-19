import Pell.SlopeLatticeFirstMinimum
import Pell.SlopeLatticeAxisVectorBounds
import Pell.SlopeLatticeShortVectorLogCounting

/-!
# Actual reciprocal-first-minimum tails at separated centers

The reciprocal is taken from the proved, attained positive first sup-norm
minimum of the displayed slope map.  Above the strict axis thresholds,
its actual tail is exactly the non-axis short-vector set, so the separated
center logarithmic estimate applies.  No minimum, capacity, center-cover
construction, curve count, or tail summation is supplied as a premise.
-/

namespace PellPaper

noncomputable section

/-- The reciprocal of the actual first sup-norm minimum. -/
def reciprocalFirstSlopeSupNorm (U V M z : ℝ) : ℝ :=
  1 / firstSlopeSupNorm U V M z

theorem reciprocalFirstSlopeSupNorm_pos
    (U V M z : ℝ) (hU : 0 < U) (hV : 0 < V) (hM : 0 < M) :
    0 < reciprocalFirstSlopeSupNorm U V M z :=
  one_div_pos.mpr (firstSlopeSupNorm_pos U V M z hU hV hM)

/-- The weak reciprocal tail is exactly existence of a nonzero integer
vector in the closed sup-norm ball of radius `1/T`. -/
theorem le_reciprocalFirstSlopeSupNorm_iff
    (U V M z T : ℝ) (hU : 0 < U) (hV : 0 < V) (hM : 0 < M) (hT : 0 < T) :
    T ≤ reciprocalFirstSlopeSupNorm U V M z ↔
      ∃ v : ℤ × ℤ, v ≠ 0 ∧ slopeVectorSupNorm U V M z v ≤ 1 / T := by
  have hminpos := firstSlopeSupNorm_pos U V M z hU hV hM
  have hinverse : T ≤ reciprocalFirstSlopeSupNorm U V M z ↔
      firstSlopeSupNorm U V M z ≤ 1 / T := by
    rw [reciprocalFirstSlopeSupNorm, le_div_iff₀ hminpos, le_div_iff₀ hT]
    rw [mul_comm]
  rw [hinverse]
  constructor
  · intro htail
    obtain ⟨v, hv, heq⟩ := exists_nonzero_slopeVector_attaining_firstSupNorm U V M z hU hV hM
    exact ⟨v, hv, heq.trans_le htail⟩
  · rintro ⟨v, hv, hbound⟩
    exact (firstSlopeSupNorm_le U V M z hU hV hM v hv).trans hbound

/-- Every nonzero short vector below both strict axis thresholds is non-axis. -/
theorem nonaxis_of_slopeVectorSupNorm_le_of_axis_thresholds
    (U V M z R : ℝ) (hU : 0 < U) (hV : 0 < V) (hM : 0 ≤ M)
    (hfst : R < M / V) (hsnd : R < max |z| 1 / U)
    (v : ℤ × ℤ) (hvne : v ≠ 0) (hv : slopeVectorSupNorm U V M z v ≤ R) :
    v.1 ≠ 0 ∧ v.2 ≠ 0 := by
  rcases v with ⟨a, b⟩
  constructor
  · intro ha
    change a = 0 at ha
    have hb : b ≠ 0 := by
      intro hb
      apply hvne
      simp [ha, hb]
    have hbound := (exists_snd_axis_slope_vector_iff U V M z R hU).mp
      ⟨b, hb, by simpa only [slopeVectorSupNorm, ha] using hv⟩
    exact (not_le_of_gt hsnd) hbound
  · intro hb
    change b = 0 at hb
    have ha : a ≠ 0 := by
      intro ha
      apply hvne
      simp [ha, hb]
    have hbound := (exists_fst_axis_slope_vector_iff U V M z R hV hM).mp
      ⟨a, ha, by simpa only [slopeVectorSupNorm, hb] using hv⟩
    exact (not_le_of_gt hfst) hbound

/-- At centers at least `M/2`, reciprocal levels strictly above `V/M` and
`2*U/M` exclude both integer axes.  The weak tail is thus exactly non-axis. -/
theorem le_reciprocalFirstSlopeSupNorm_iff_nonAxis
    (U V M z T : ℝ) (hU : 0 < U) (hV : 0 < V) (hM : 0 < M) (hT : 0 < T)
    (hz : M / 2 ≤ z) (hfst : V / M < T) (hsnd : 2 * U / M < T) :
    T ≤ reciprocalFirstSlopeSupNorm U V M z ↔ NonAxisSlopeShortVector U V M T z := by
  have hfst' : 1 / T < M / V := by
    calc
      1 / T < 1 / (V / M) := one_div_lt_one_div_of_lt (div_pos hV hM) hfst
      _ = M / V := by field_simp
  have hsnd' : 1 / T < max |z| 1 / U := by
    have hzmax : M / 2 ≤ max |z| 1 := hz.trans ((le_abs_self z).trans (le_max_left _ _))
    calc
      1 / T < 1 / (2 * U / M) := one_div_lt_one_div_of_lt (by positivity) hsnd
      _ = (M / 2) / U := by field_simp
      _ ≤ max |z| 1 / U := div_le_div_of_nonneg_right hzmax hU.le
  rw [le_reciprocalFirstSlopeSupNorm_iff U V M z T hU hV hM hT]
  constructor
  · rintro ⟨v, hvne, hv⟩
    obtain ⟨ha, hb⟩ := nonaxis_of_slopeVectorSupNorm_le_of_axis_thresholds
      U V M z (1 / T) hU hV hM.le hfst' hsnd' v hvne hv
    exact ⟨v.1, v.2, ha, hb, hv⟩
  · rintro ⟨a, b, ha, hb, hv⟩
    refine ⟨(a, b), ?_, hv⟩
    intro heq
    exact ha (congrArg Prod.fst heq)

/-- The actual finite family in the weak reciprocal-first-minimum tail. -/
def reciprocalFirstSlopeSupNormTail
    {ι : Type*} (J : Finset ι) (z : ι → ℝ) (U V M T : ℝ) : Finset ι := by
  classical
  exact J.filter fun i => T ≤ reciprocalFirstSlopeSupNorm U V M (z i)

/-- The actual tail agrees with the already counted non-axis short-vector
family above the strict axis thresholds. -/
theorem reciprocalFirstSlopeSupNormTail_eq_nonAxis
    {ι : Type*} (J : Finset ι) (z : ι → ℝ) (U V M T : ℝ)
    (hU : 0 < U) (hV : 0 < V) (hM : 0 < M) (hT : 0 < T)
    (hz : ∀ i ∈ J, M / 2 ≤ z i) (hfst : V / M < T) (hsnd : 2 * U / M < T) :
    reciprocalFirstSlopeSupNormTail J z U V M T = nonAxisSlopeShortVectorCells J z U V M T := by
  classical
  apply Finset.filter_congr
  intro i hi
  exact le_reciprocalFirstSlopeSupNorm_iff_nonAxis U V M (z i) T hU hV hM hT (hz i hi) hfst hsnd

/-- The actual reciprocal-minimum tail satisfies the quadratic-decay
logarithmic count, with every normalization and separation hypothesis explicit. -/
theorem card_reciprocalFirstSlopeSupNormTail_le_log
    {ι : Type*} (J : Finset ι) (z : ι → ℝ) (U V M T C sep : ℝ)
    (hU : 0 < U) (hV : 0 < V) (hM : 1 ≤ M) (hT : 0 < T)
    (hC : 0 ≤ C) (hsep : 0 < sep)
    (hcenters : ∀ i ∈ J, M / 2 ≤ z i ∧ z i ≤ C * M)
    (hseparated : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → sep ≤ |z i - z j|)
    (hfst : V / M < T) (hsnd : 2 * U / M < T) :
    ((reciprocalFirstSlopeSupNormTail J z U V M T).card : ℝ) ≤
      (4 + 8 / sep) * (C + 1) * (U * V / T ^ 2) * (1 + Real.log (1 + U / T)) := by
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  rw [reciprocalFirstSlopeSupNormTail_eq_nonAxis J z U V M T hU hV hMpos hT
    (fun i hi => (hcenters i hi).1) hfst hsnd]
  apply card_nonAxisSlopeShortVectorCells_le_log J z U V M T C sep
    hU hV hM hT hC hsep _ hseparated
  intro i hi
  exact ⟨(by linarith [(hcenters i hi).1]), (hcenters i hi).2⟩

end

end PellPaper
