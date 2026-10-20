import Pell.FiniteReciprocalLinearSquareTailSummation

/-!
# Weighted finite incidence sums from radial ball growth

Let a finite family have radii in `[1, H]`.  A radial counting estimate

`#{v : r v ≤ t} ≤ A * t + B * t^2`, for `1 ≤ t ≤ H`,

turns under the reciprocal change of variables `T = H / t` into a weak-tail
estimate for `H / r v`.  The finite mixed-tail summation theorem then bounds
the reciprocal sum, and the count at `t = H` absorbs the additional constant
weight.  No lattice-specific input occurs in this module.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- Linear-plus-square radial ball growth controls the sum of scaled reciprocal
radii.  The tail argument uses the supplied ball estimate only in its stated
range `1 ≤ t ≤ H`; thresholds `T > H` give an empty reciprocal tail. -/
theorem sum_scaledReciprocalRadius_le_of_linear_square_ballGrowth
    {ι : Type*} (V : Finset ι) (r : ι → ℝ) (H A B : ℝ)
    (hH : 1 ≤ H) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hrLower : ∀ v ∈ V, 1 ≤ r v)
    (hrUpper : ∀ v ∈ V, r v ≤ H)
    (hball : ∀ t : ℝ, 1 ≤ t → t ≤ H →
      ((V.filter fun v => r v ≤ t).card : ℝ) ≤ A * t + B * t ^ 2) :
    (∑ v ∈ V, H / r v) ≤
      A * H * (1 + Real.log H) + 2 * B * H ^ 2 := by
  classical
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hHnonneg : 0 ≤ H := hHpos.le
  have hAH : 0 ≤ A * H := mul_nonneg hA hHnonneg
  have hBHsq : 0 ≤ B * H ^ 2 := mul_nonneg hB (sq_nonneg H)
  have hrecipLower : ∀ v ∈ V, (1 : ℝ) ≤ H / r v := by
    intro v hv
    have hrpos : 0 < r v := lt_of_lt_of_le zero_lt_one (hrLower v hv)
    apply (le_div_iff₀ hrpos).2
    simpa only [one_mul] using hrUpper v hv
  have hrecipUpper : ∀ v ∈ V, H / r v ≤ H := by
    intro v hv
    have hrpos : 0 < r v := lt_of_lt_of_le zero_lt_one (hrLower v hv)
    apply (div_le_iff₀ hrpos).2
    have hmul := mul_le_mul_of_nonneg_left (hrLower v hv) hHnonneg
    simpa only [mul_one] using hmul
  have htail : ∀ T : ℝ, (1 : ℝ) ≤ T →
      ((V.filter fun v => T ≤ H / r v).card : ℝ) ≤
        (A * H) / T + (B * H ^ 2) / T ^ 2 := by
    intro T hT
    have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
    by_cases hTH : T ≤ H
    · have htLower : (1 : ℝ) ≤ H / T := by
        apply (le_div_iff₀ hTpos).2
        simpa only [one_mul] using hTH
      have htUpper : H / T ≤ H := by
        apply (div_le_iff₀ hTpos).2
        have hmul := mul_le_mul_of_nonneg_left hT hHnonneg
        simpa only [mul_one] using hmul
      have hfilter :
          V.filter (fun v => T ≤ H / r v) =
            V.filter (fun v => r v ≤ H / T) := by
        ext v
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hv, hvr⟩
          refine ⟨hv, ?_⟩
          have hrpos : 0 < r v :=
            lt_of_lt_of_le zero_lt_one (hrLower v hv)
          apply (le_div_iff₀ hTpos).2
          have hmul := (le_div_iff₀ hrpos).1 hvr
          simpa only [mul_comm] using hmul
        · rintro ⟨hv, hvr⟩
          refine ⟨hv, ?_⟩
          have hrpos : 0 < r v :=
            lt_of_lt_of_le zero_lt_one (hrLower v hv)
          apply (le_div_iff₀ hrpos).2
          have hmul := (le_div_iff₀ hTpos).1 hvr
          simpa only [mul_comm] using hmul
      calc
        ((V.filter fun v => T ≤ H / r v).card : ℝ) =
            ((V.filter fun v => r v ≤ H / T).card : ℝ) := by rw [hfilter]
        _ ≤ A * (H / T) + B * (H / T) ^ 2 :=
          hball (H / T) htLower htUpper
        _ = (A * H) / T + (B * H ^ 2) / T ^ 2 := by
          field_simp [hTpos.ne']
    · have hHT : H < T := lt_of_not_ge hTH
      have hfilter : V.filter (fun v => T ≤ H / r v) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro v hv
        exact not_le_of_gt ((hrecipUpper v hv).trans_lt hHT)
      rw [hfilter]
      simp only [Finset.card_empty, Nat.cast_zero]
      exact add_nonneg (div_nonneg hAH hTpos.le)
        (div_nonneg hBHsq (sq_nonneg T))
  have hsum := sum_le_linear_square_tail_completion
    V (fun v => H / r v) 1 H (A * H) (B * H ^ 2)
    (by norm_num) hH hAH hBHsq hrecipLower hrecipUpper htail
  calc
    (∑ v ∈ V, H / r v) ≤
        A * H * (1 + Real.log H) + 2 * (B * H ^ 2) := by
      simpa only [div_one, Real.log_one, one_mul] using hsum
    _ = A * H * (1 + Real.log H) + 2 * B * H ^ 2 := by ring

/-- The corresponding weighted incidence sum has one additional copy of the
family cardinality.  Evaluating ball growth at `t = H` supplies that copy. -/
theorem sum_one_add_scaledReciprocalRadius_le_of_linear_square_ballGrowth
    {ι : Type*} (V : Finset ι) (r : ι → ℝ) (H A B : ℝ)
    (hH : 1 ≤ H) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hrLower : ∀ v ∈ V, 1 ≤ r v)
    (hrUpper : ∀ v ∈ V, r v ≤ H)
    (hball : ∀ t : ℝ, 1 ≤ t → t ≤ H →
      ((V.filter fun v => r v ≤ t).card : ℝ) ≤ A * t + B * t ^ 2) :
    (∑ v ∈ V, (1 + H / r v)) ≤
      A * H * (2 + Real.log H) + 3 * B * H ^ 2 := by
  classical
  have hfilter : V.filter (fun v => r v ≤ H) = V := by
    exact Finset.filter_eq_self.mpr hrUpper
  have hcard : (V.card : ℝ) ≤ A * H + B * H ^ 2 := by
    have h := hball H hH le_rfl
    rw [hfilter] at h
    exact h
  have hrecip := sum_scaledReciprocalRadius_le_of_linear_square_ballGrowth
    V r H A B hH hA hB hrLower hrUpper hball
  calc
    (∑ v ∈ V, (1 + H / r v)) =
        (V.card : ℝ) + ∑ v ∈ V, H / r v := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
        mul_one]
    _ ≤ (A * H + B * H ^ 2) +
        (A * H * (1 + Real.log H) + 2 * B * H ^ 2) :=
      add_le_add hcard hrecip
    _ = A * H * (2 + Real.log H) + 3 * B * H ^ 2 := by ring

end

end PellPaper
