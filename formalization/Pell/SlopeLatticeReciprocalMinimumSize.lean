import Pell.SlopeLatticeReciprocalMinimumTail

/-!
# Actual reciprocal-minimum size bounds for interval counting

Attainment and integer coordinates give an upper bound independent of the
center: the reciprocal first minimum is at most max(U,V/M). For M at least
one this is at most U+V, the polynomial-scale bound needed to absorb small
powers in the interval count. A nonzero vector of bounded norm supplies a
lower reciprocal bound, as needed for nonempty cells.
-/

namespace PellPaper

noncomputable section

/-- An actual nonzero bounded vector gives a lower bound for the reciprocal
first minimum. Positivity of the radius follows from the vector, not a premise. -/
theorem one_div_le_reciprocalFirstSlopeSupNorm_of_vector
    (U V M z B : ℝ) (hU : 0 < U) (hV : 0 < V) (hM : 0 < M)
    (v : ℤ × ℤ) (hv : v ≠ 0) (hbound : slopeVectorSupNorm U V M z v ≤ B) :
    1 / B ≤ reciprocalFirstSlopeSupNorm U V M z := by
  exact one_div_le_one_div_of_le (firstSlopeSupNorm_pos U V M z hU hV hM)
    ((firstSlopeSupNorm_le U V M z hU hV hM v hv).trans hbound)

/-- Integer coordinates bound the actual reciprocal minimum independently
of the slope center. No witness, minimum or coordinate bound is supplied. -/
theorem reciprocalFirstSlopeSupNorm_le_max
    (U V M z : ℝ) (hU : 0 < U) (hV : 0 < V) (hM : 0 < M) :
    reciprocalFirstSlopeSupNorm U V M z ≤ max U (V / M) := by
  obtain ⟨⟨a, b⟩, hv, heq⟩ :=
    exists_nonzero_slopeVector_attaining_firstSupNorm U V M z hU hV hM
  by_cases hb : b = 0
  · subst b
    have ha : a ≠ 0 := by
      intro ha
      apply hv
      simp [ha]
    have haxis : M / V ≤ firstSlopeSupNorm U V M z :=
      (exists_fst_axis_slope_vector_iff U V M z _ hV hM.le).mp
        ⟨a, ha, heq.le⟩
    have hinv := one_div_le_one_div_of_le (div_pos hM hV) haxis
    have hbound : reciprocalFirstSlopeSupNorm U V M z ≤ V / M := by
      simpa only [reciprocalFirstSlopeSupNorm, one_div_div] using hinv
    exact hbound.trans (le_max_right _ _)
  · have hbone : (1 : ℝ) ≤ |(b : ℝ)| := by exact_mod_cast Int.one_le_abs hb
    have hcoord : |(b : ℝ) / U| ≤ firstSlopeSupNorm U V M z := by
      rw [← heq]
      exact le_max_right _ _
    rw [abs_div, abs_of_pos hU] at hcoord
    have hmin : 1 / U ≤ firstSlopeSupNorm U V M z :=
      (div_le_div_of_nonneg_right hbone hU.le).trans hcoord
    have hinv := one_div_le_one_div_of_le (one_div_pos.mpr hU) hmin
    have hbound : reciprocalFirstSlopeSupNorm U V M z ≤ U := by
      simpa only [reciprocalFirstSlopeSupNorm, one_div_one_div] using hinv
    exact hbound.trans (le_max_left _ _)

/-- The actual reciprocal minimum has the required U+V size bound for
every center when the localization scale is at least one. -/
theorem reciprocalFirstSlopeSupNorm_le_add
    (U V M z : ℝ) (hU : 0 < U) (hV : 0 < V) (hM : 1 ≤ M) :
    reciprocalFirstSlopeSupNorm U V M z ≤ U + V := by
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hVM : V / M ≤ V := (div_le_iff₀ hMpos).mpr (by nlinarith)
  exact (reciprocalFirstSlopeSupNorm_le_max U V M z hU hV hMpos).trans
    (max_le (by linarith) (by linarith))

end
end PellPaper

