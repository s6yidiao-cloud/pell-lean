import Pell.DyadicLocalRatioCover

/-!
# Normalized geometric centers of the actual source-ratio cells

The source mesh remains the multiplicative mesh of `DyadicLocalRatioCover`.
Multiplying its actual center by `M*E/D` gives exactly
`(M/2)*(1+1/M)^k`. Distinct natural indices are separated by at least
one half. A nonempty actual source cell forces its normalized center into
`[M/2,2M]` by the literal dyadic source-coordinate bounds.

These geometric centers are not identified with the integer target grid.
No curve count, source/target multiplicity, or minimum estimate is asserted.
-/

namespace PellPaper

noncomputable section

/-- The actual source-ratio center in the `M*E/D` normalization. -/
def dyadicFactorBoxLocalRatioNormalizedCenter
    (i : ℕ × ℕ × ℕ × ℕ) (M k : ℕ) : ℝ :=
  (M : ℝ) * ((2 ^ i.2.1 : ℕ) : ℝ) * dyadicFactorBoxLocalRatioCenter i M k /
    ((2 ^ i.1 : ℕ) : ℝ)

/-- The normalized center has a box-independent exact geometric formula. -/
theorem dyadicFactorBoxLocalRatioNormalizedCenter_eq
    (i : ℕ × ℕ × ℕ × ℕ) (M k : ℕ) :
    dyadicFactorBoxLocalRatioNormalizedCenter i M k =
      ((M : ℝ) / 2) * localRatioMeshStep M ^ k := by
  have hD : ((2 ^ i.1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hE : ((2 ^ i.2.1 : ℕ) : ℝ) ≠ 0 := by positivity
  unfold dyadicFactorBoxLocalRatioNormalizedCenter dyadicFactorBoxLocalRatioCenter
    dyadicFactorBoxLocalRatioStart
  field_simp

private theorem localRatioMeshStep_one_le (M : ℕ) : 1 ≤ localRatioMeshStep M := by
  unfold localRatioMeshStep
  have h : (0 : ℝ) ≤ 1 / (M : ℝ) := by positivity
  linarith

/-- All geometric indices have normalized center at least `M/2`. -/
theorem dyadicFactorBoxLocalRatioNormalizedCenter_lower
    (i : ℕ × ℕ × ℕ × ℕ) (M k : ℕ) :
    (M : ℝ) / 2 ≤ dyadicFactorBoxLocalRatioNormalizedCenter i M k := by
  rw [dyadicFactorBoxLocalRatioNormalizedCenter_eq]
  have hpow : (1 : ℝ) ≤ localRatioMeshStep M ^ k := one_le_pow₀ (localRatioMeshStep_one_le M)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow (by positivity : (0 : ℝ) ≤ M / 2)

/-- Successive normalized centers differ by half the current mesh power. -/
theorem dyadicFactorBoxLocalRatioNormalizedCenter_succ_sub
    (i : ℕ × ℕ × ℕ × ℕ) {M : ℕ} (hM : 0 < M) (k : ℕ) :
    dyadicFactorBoxLocalRatioNormalizedCenter i M (k + 1) -
      dyadicFactorBoxLocalRatioNormalizedCenter i M k = localRatioMeshStep M ^ k / 2 := by
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  rw [dyadicFactorBoxLocalRatioNormalizedCenter_eq, dyadicFactorBoxLocalRatioNormalizedCenter_eq,
    pow_succ]
  unfold localRatioMeshStep
  field_simp
  ring

/-- The natural-index geometric source centers are monotone. -/
theorem dyadicFactorBoxLocalRatioNormalizedCenter_mono
    (i : ℕ × ℕ × ℕ × ℕ) (M : ℕ) {k l : ℕ} (hkl : k ≤ l) :
    dyadicFactorBoxLocalRatioNormalizedCenter i M k ≤
      dyadicFactorBoxLocalRatioNormalizedCenter i M l := by
  rw [dyadicFactorBoxLocalRatioNormalizedCenter_eq, dyadicFactorBoxLocalRatioNormalizedCenter_eq]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (localRatioMeshStep_one_le M) hkl)
    (by positivity)

private theorem normalizedCenter_half_le_sub_of_lt
    (i : ℕ × ℕ × ℕ × ℕ) {M : ℕ} (hM : 0 < M) {k l : ℕ} (hkl : k < l) :
    (1 / 2 : ℝ) ≤ dyadicFactorBoxLocalRatioNormalizedCenter i M l -
      dyadicFactorBoxLocalRatioNormalizedCenter i M k := by
  have hnext := dyadicFactorBoxLocalRatioNormalizedCenter_succ_sub i hM k
  have hpow : (1 : ℝ) ≤ localRatioMeshStep M ^ k := one_le_pow₀ (localRatioMeshStep_one_le M)
  have hmono := dyadicFactorBoxLocalRatioNormalizedCenter_mono i M (Nat.succ_le_of_lt hkl)
  linarith

/-- Distinct geometric source indices have separation at least one half. -/
theorem dyadicFactorBoxLocalRatioNormalizedCenter_separated
    (i : ℕ × ℕ × ℕ × ℕ) {M : ℕ} (hM : 0 < M) {k l : ℕ} (hkl : k ≠ l) :
    (1 / 2 : ℝ) ≤ |dyadicFactorBoxLocalRatioNormalizedCenter i M k -
      dyadicFactorBoxLocalRatioNormalizedCenter i M l| := by
  rcases lt_or_gt_of_ne hkl with h | h
  · have hsub := normalizedCenter_half_le_sub_of_lt i hM h
    rw [abs_sub_comm]
    exact hsub.trans (le_abs_self _)
  · exact (normalizedCenter_half_le_sub_of_lt i hM h).trans (le_abs_self _)

/-- Nonemptiness of the literal source cell supplies the upper center bound. -/
theorem dyadicFactorBoxLocalRatioNormalizedCenter_upper_of_nonempty
    (theta : ℝ) (Y : ℕ) (i : ℕ × ℕ × ℕ × ℕ) (M k : ℕ)
    (hne : (dyadicFactorBoxLocalRatioCell theta Y i M k).Nonempty) :
    dyadicFactorBoxLocalRatioNormalizedCenter i M k ≤ 2 * (M : ℝ) := by
  obtain ⟨q, hq⟩ := hne
  obtain ⟨hqbox, hcenter, _⟩ := mem_dyadicFactorBoxLocalRatioCell hq
  have hbox : (q.1, q.2.1, q.2.2.1, q.2.2.2) ∈ dyadicBox i := (Finset.mem_inter.mp hqbox).2
  have hupper := (dyadicBox_sourceRatio_between_localRatioStart_and_four_mul hbox).2
  have hD : ((2 ^ i.1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hE : ((2 ^ i.2.1 : ℕ) : ℝ) ≠ 0 := by positivity
  calc
    dyadicFactorBoxLocalRatioNormalizedCenter i M k ≤
        (M : ℝ) * ((2 ^ i.2.1 : ℕ) : ℝ) * (4 * dyadicFactorBoxLocalRatioStart i) /
          ((2 ^ i.1 : ℕ) : ℝ) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left (hcenter.trans hupper) (by positivity)
    _ = 2 * (M : ℝ) := by
      unfold dyadicFactorBoxLocalRatioStart
      field_simp
      ring

/-- The first `2M` geometric source indices whose actual cells are nonempty. -/
def activeDyadicSourceRatioIndices
    (theta : ℝ) (Y : ℕ) (i : ℕ × ℕ × ℕ × ℕ) (M : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (2 * M)).filter fun k =>
    (dyadicFactorBoxLocalRatioCell theta Y i M k).Nonempty

/-- Every active geometric source index has its derived normalized range. -/
theorem activeDyadicSourceRatioIndices_range
    (theta : ℝ) (Y : ℕ) (i : ℕ × ℕ × ℕ × ℕ) (M : ℕ) {k : ℕ}
    (hk : k ∈ activeDyadicSourceRatioIndices theta Y i M) :
    k < 2 * M ∧ (M : ℝ) / 2 ≤ dyadicFactorBoxLocalRatioNormalizedCenter i M k ∧
      dyadicFactorBoxLocalRatioNormalizedCenter i M k ≤ 2 * (M : ℝ) := by
  have h := Finset.mem_filter.mp hk
  exact ⟨Finset.mem_range.mp h.1, dyadicFactorBoxLocalRatioNormalizedCenter_lower i M k,
    dyadicFactorBoxLocalRatioNormalizedCenter_upper_of_nonempty theta Y i M k h.2⟩

end
end PellPaper
