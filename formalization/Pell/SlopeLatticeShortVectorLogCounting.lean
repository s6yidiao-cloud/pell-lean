import Pell.SlopeLatticeShortVectorCounting

/-!
# A logarithmic budget for non-axis slope short vectors

This is the explicit real logarithmic consequence of the finite harmonic
count.  It concerns only the displayed normalized slope map at a finite
separated family of centers.  Curve counts, geometric minima, center-cover
construction, and dyadic aggregation remain separate statements.
-/

namespace PellPaper

noncomputable section

/-- The non-axis short-vector center count has a genuine quadratic decay in
`T`, up to the displayed logarithm, under the explicit normalization bounds. -/
theorem card_nonAxisSlopeShortVectorCells_le_log
    {ι : Type*} (J : Finset ι) (z : ι → ℝ) (U V M T C sep : ℝ)
    (hU : 0 < U) (hV : 0 < V) (hM : 1 ≤ M) (hT : 0 < T)
    (hC : 0 ≤ C) (hsep : 0 < sep)
    (hcenters : ∀ i ∈ J, 0 ≤ z i ∧ z i ≤ C * M)
    (hseparated : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → sep ≤ |z i - z j|) :
    ((nonAxisSlopeShortVectorCells J z U V M T).card : ℝ) ≤
      (4 + 8 / sep) * (C + 1) * (U * V / T ^ 2) *
        (1 + Real.log (1 + U / T)) := by
  have ha : 0 ≤ (C + 1) * V / T := by positivity
  have hb : 0 < U / T := by positivity
  have hA : (⌊(C + 1) * V / T⌋₊ : ℝ) ≤ (C + 1) * V / T := Nat.floor_le ha
  have hB : (⌊U / T⌋₊ : ℝ) ≤ U / T := Nat.floor_le hb.le
  have hlog : 0 ≤ Real.log (1 + U / T) := Real.log_nonneg (by linarith)
  have hH : (harmonic ⌊U / T⌋₊ : ℝ) ≤ 1 + Real.log (1 + U / T) := by
    by_cases hzero : ⌊U / T⌋₊ = 0
    · simp only [hzero, harmonic_zero, Rat.cast_zero]
      linarith
    · have hpos : 0 < (⌊U / T⌋₊ : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hzero
      have hlogmon : Real.log (⌊U / T⌋₊ : ℝ) ≤ Real.log (1 + U / T) :=
        Real.log_le_log hpos (by linarith)
      exact (harmonic_le_one_add_log _).trans (add_le_add le_rfl hlogmon)
  have hfirst : 4 * (⌊(C + 1) * V / T⌋₊ : ℝ) * ⌊U / T⌋₊ ≤
      4 * ((C + 1) * V / T) * (U / T) * (1 + Real.log (1 + U / T)) := by
    calc
      4 * (⌊(C + 1) * V / T⌋₊ : ℝ) * ⌊U / T⌋₊ ≤
          4 * ((C + 1) * V / T) * (U / T) := by gcongr
      _ = 4 * ((C + 1) * V / T) * (U / T) * 1 := by ring
      _ ≤ 4 * ((C + 1) * V / T) * (U / T) *
          (1 + Real.log (1 + U / T)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hsecond : 8 * (⌊(C + 1) * V / T⌋₊ : ℝ) * (U / T) / sep *
      (harmonic ⌊U / T⌋₊ : ℝ) ≤
      8 * ((C + 1) * V / T) * (U / T) / sep *
        (1 + Real.log (1 + U / T)) := by
    calc
      8 * (⌊(C + 1) * V / T⌋₊ : ℝ) * (U / T) / sep *
          (harmonic ⌊U / T⌋₊ : ℝ) ≤
          8 * (⌊(C + 1) * V / T⌋₊ : ℝ) * (U / T) / sep *
            (1 + Real.log (1 + U / T)) :=
        mul_le_mul_of_nonneg_left hH (by positivity)
      _ ≤ 8 * ((C + 1) * V / T) * (U / T) / sep *
          (1 + Real.log (1 + U / T)) := by gcongr
  calc
    ((nonAxisSlopeShortVectorCells J z U V M T).card : ℝ) ≤
        4 * (⌊(C + 1) * V / T⌋₊ : ℝ) * ⌊U / T⌋₊ +
        8 * (⌊(C + 1) * V / T⌋₊ : ℝ) * (U / T) / sep *
          (harmonic ⌊U / T⌋₊ : ℝ) :=
      card_nonAxisSlopeShortVectorCells_le_harmonic J z U V M T C sep
        hU hV hM hT hC hsep hcenters hseparated
    _ ≤ 4 * ((C + 1) * V / T) * (U / T) * (1 + Real.log (1 + U / T)) +
        8 * ((C + 1) * V / T) * (U / T) / sep *
          (1 + Real.log (1 + U / T)) := add_le_add hfirst hsecond
    _ = (4 + 8 / sep) * (C + 1) * (U * V / T ^ 2) *
        (1 + Real.log (1 + U / T)) := by ring

end

end PellPaper
