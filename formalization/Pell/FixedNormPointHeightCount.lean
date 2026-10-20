import Pell.FiniteZpowHeightCount
import Pell.PositiveFixedNormOrbitCover

/-!
# Counting actual Pell points within a real-height window

The counted objects are integer pairs `(d,e)`, not exponents supplied by a
caller. A chosen exponent map is injective because the two literal action
coordinates determine the point. The residue cover then bounds an entire
fixed nonzero norm level within an explicitly supplied positive height window.
No dyadic or source-scale height inequality is assumed proved here.
-/

namespace PellPaper

/-- A finite set of actual integer pairs on one supplied cyclic Pell orbit
has the exact logarithmic height bound. The positive basepoint need not
belong to the finite set or lie in its height interval. -/
theorem card_pellPowerOrbit_points_le_log_height
    (u v : ℤ) {a : Pell.Solution₁ (u * v)} (ha : Pell.IsFundamental a)
    (r : ℤ × ℤ) (S : Finset (ℤ × ℤ)) (L H : ℝ)
    (hr : 0 < (v : ℝ) * r.2 + (r.1 : ℝ) * Real.sqrt ((u * v : ℤ) : ℝ))
    (hL : 0 < L) (hLH : L ≤ H)
    (hheight : ∀ z ∈ S,
      L ≤ (v : ℝ) * z.2 + (z.1 : ℝ) * Real.sqrt ((u * v : ℤ) : ℝ) ∧
        (v : ℝ) * z.2 + (z.1 : ℝ) * Real.sqrt ((u * v : ℤ) : ℝ) ≤ H)
    (horbit : ∀ z ∈ S, ∃ n : ℤ,
      z.2 = (a ^ n).x * r.2 + u * (a ^ n).y * r.1 ∧
      z.1 = v * (a ^ n).y * r.2 + (a ^ n).x * r.1) :
    (S.card : ℝ) ≤ 1 + Real.log (H / L) / Real.log (epsilon a) := by
  classical
  choose n he hd using (fun z : S => horbit z z.property)
  have hinj : Function.Injective n := by
    intro z w hzw
    apply Subtype.ext
    apply Prod.ext
    · exact (hd z).trans (by rw [hzw]; exact (hd w).symm)
    · exact (he z).trans (by rw [hzw]; exact (he w).symm)
  let E : Finset ℤ := Finset.univ.image n
  have hcard : E.card = S.card := by
    dsimp [E]
    rw [Finset.card_image_of_injective _ hinj]
    exact Finset.card_attach
  have hE : ∀ k ∈ E,
      L ≤ ((v : ℝ) * r.2 + (r.1 : ℝ) * Real.sqrt ((u * v : ℤ) : ℝ)) *
        epsilon a ^ k ∧
      ((v : ℝ) * r.2 + (r.1 : ℝ) * Real.sqrt ((u * v : ℤ) : ℝ)) *
        epsilon a ^ k ≤ H := by
    intro k hk
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hk
    have hz := hheight z z.property
    have hv := pell_transform_real_value u v r.1 r.2 z.val.1 z.val.2
      ha.d_pos.le (a ^ n z) (he z) (hd z)
    rw [epsilon_zpow ha.d_pos.le] at hv
    rw [hv] at hz
    simpa only [mul_comm] using hz
  have hc := card_finset_zpow_height_le E (epsilon a)
    ((v : ℝ) * r.2 + (r.1 : ℝ) * Real.sqrt ((u * v : ℤ) : ℝ)) L H
    (one_lt_epsilon_of_isFundamental ha) hr hL hLH hE
  simpa only [hcard] using hc

/-- The literal finite fixed-norm family in a positive real-height window
has a uniform `h.natAbs^2` times logarithmic cardinality bound. An orbit
budget and an exponent parametrization are both supplied internally. -/
theorem card_fixedNorm_points_le_natAbs_sq_mul_log_height
    (u v h : ℤ) (hh : h ≠ 0)
    {a : Pell.Solution₁ (u * v)} (ha : Pell.IsFundamental a)
    (S : Finset (ℤ × ℤ)) (L H : ℝ) (hL : 0 < L) (hLH : L ≤ H)
    (hn : ∀ z ∈ S, v * z.2 ^ 2 - u * z.1 ^ 2 = h)
    (hheight : ∀ z ∈ S,
      L ≤ (v : ℝ) * z.2 + (z.1 : ℝ) * Real.sqrt ((u * v : ℤ) : ℝ) ∧
        (v : ℝ) * z.2 + (z.1 : ℝ) * Real.sqrt ((u * v : ℤ) : ℝ) ≤ H) :
    (S.card : ℝ) ≤ (h.natAbs : ℝ) ^ 2 *
      (1 + Real.log (H / L) / Real.log (epsilon a)) := by
  classical
  let C := 1 + Real.log (H / L) / Real.log (epsilon a)
  have hC : 0 ≤ C := by
    simpa [C] using card_finset_zpow_height_le ∅ (epsilon a) 1 L H
      (one_lt_epsilon_of_isFundamental ha) zero_lt_one hL hLH (by simp)
  obtain ⟨R, hR, hcard, hcover⟩ := exists_positive_fixedNorm_pellPower_representatives
    u v h hh ha (↑S : Set (ℤ × ℤ)) hn
      (fun z hz => hL.trans_le (hheight z hz).1)
  let F : (ℤ × ℤ) → Finset (ℤ × ℤ) := fun r => S.filter fun z => ∃ n : ℤ,
    z.2 = (a ^ n).x * r.2 + u * (a ^ n).y * r.1 ∧
    z.1 = v * (a ^ n).y * r.2 + (a ^ n).x * r.1
  have hsub : S ⊆ R.biUnion F := by
    intro z hz
    obtain ⟨r, hr, n, he, hd⟩ := hcover z hz
    exact Finset.mem_biUnion.mpr ⟨r, hr, Finset.mem_filter.mpr ⟨hz, n, he, hd⟩⟩
  have hF : ∀ r ∈ R, ((F r).card : ℝ) ≤ C := by
    intro r hr
    apply card_pellPowerOrbit_points_le_log_height u v ha r (F r) L H
      (hL.trans_le (hheight r (hR hr)).1) hL hLH
    · intro z hz
      exact hheight z (Finset.mem_filter.mp hz).1
    · intro z hz
      exact (Finset.mem_filter.mp hz).2
  have hcNat : S.card ≤ ∑ r ∈ R, (F r).card :=
    (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  calc
    (S.card : ℝ) ≤ ∑ r ∈ R, ((F r).card : ℝ) := by exact_mod_cast hcNat
    _ ≤ ∑ _ ∈ R, C := Finset.sum_le_sum hF
    _ = (R.card : ℝ) * C := by simp
    _ ≤ (h.natAbs : ℝ) ^ 2 * C :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hC

/-- At one of the four signed Pell differences, the whole fixed-norm
finite family costs at most four logarithmic orbit capacities. -/
theorem card_fixedNorm_points_le_four_mul_log_height
    (u v h : ℤ) (hh : IsSignedDyadicDifference h)
    {a : Pell.Solution₁ (u * v)} (ha : Pell.IsFundamental a)
    (S : Finset (ℤ × ℤ)) (L H : ℝ) (hL : 0 < L) (hLH : L ≤ H)
    (hn : ∀ z ∈ S, v * z.2 ^ 2 - u * z.1 ^ 2 = h)
    (hheight : ∀ z ∈ S,
      L ≤ (v : ℝ) * z.2 + (z.1 : ℝ) * Real.sqrt ((u * v : ℤ) : ℝ) ∧
        (v : ℝ) * z.2 + (z.1 : ℝ) * Real.sqrt ((u * v : ℤ) : ℝ) ≤ H) :
    (S.card : ℝ) ≤ 4 * (1 + Real.log (H / L) / Real.log (epsilon a)) := by
  have hC : 0 ≤ 1 + Real.log (H / L) / Real.log (epsilon a) := by
    simpa using card_finset_zpow_height_le ∅ (epsilon a) 1 L H
      (one_lt_epsilon_of_isFundamental ha) zero_lt_one hL hLH (by simp)
  have habs : (h.natAbs : ℝ) ≤ 2 := by
    exact_mod_cast natAbs_le_two_of_isSignedDyadicDifference hh
  have hsq : (h.natAbs : ℝ) ^ 2 ≤ 4 := by nlinarith [sq_nonneg (h.natAbs - 2 : ℝ)]
  exact (card_fixedNorm_points_le_natAbs_sq_mul_log_height u v h
    (isSignedDyadicDifference_ne_zero hh) ha S L H hL hLH hn hheight).trans
      (mul_le_mul_of_nonneg_right hsq hC)

end PellPaper
