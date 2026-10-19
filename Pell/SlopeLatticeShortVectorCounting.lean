import Pell.SeparatedRealCenterCounting

/-!
# Non-axis short vectors at separated normalized slope centers

The normalized target map at center `z` is
`(a,b) ↦ (M*a/V - z*b/U, b/U)`.  This module counts a finite separated
family of centers admitting an actual non-axis integer vector of sup norm
at most `1/T`.  It asserts no first-minimum, source/target pairing, curve
count, or dyadic aggregation statement.
-/

namespace PellPaper

noncomputable section

/-- Literal non-axis integer short-vector certificates for the normalized
slope map, using the sup norm on the two displayed real coordinates. -/
def NonAxisSlopeShortVector (U V M T z : ℝ) : Prop :=
  ∃ a b : ℤ, a ≠ 0 ∧ b ≠ 0 ∧
    max |M * (a : ℝ) / V - z * (b : ℝ) / U| |(b : ℝ) / U| ≤ 1 / T

/-- The actual centers in a finite family with a non-axis short-vector
certificate.  No choice of a shortest vector is part of the definition. -/
noncomputable def nonAxisSlopeShortVectorCells
    {ι : Type*} (J : Finset ι) (z : ι → ℝ) (U V M T : ℝ) : Finset ι := by
  classical
  exact J.filter fun i => NonAxisSlopeShortVector U V M T (z i)

/-- A normalized short vector at a center in `[0,C*M]` has bounded integer
coordinates.  This estimate does not require the coordinates to be nonzero. -/
theorem abs_coordinates_le_of_slope_short_vector
    (U V M T C z : ℝ) (hU : 0 < U) (hV : 0 < V) (hM : 1 ≤ M)
    (hT : 0 < T) (hz : 0 ≤ z ∧ z ≤ C * M)
    (a b : ℤ)
    (hv : max |M * (a : ℝ) / V - z * (b : ℝ) / U| |(b : ℝ) / U| ≤ 1 / T) :
    |(a : ℝ)| ≤ (C + 1) * V / T ∧ |(b : ℝ)| ≤ U / T := by
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  obtain ⟨hfirst, hsecond⟩ := max_le_iff.mp hv
  have hb : |(b : ℝ)| ≤ U / T := by
    rw [abs_div, abs_of_pos hU] at hsecond
    calc
      |(b : ℝ)| ≤ (1 / T) * U := (div_le_iff₀ hU).mp hsecond
      _ = U / T := by ring
  have hzterm : |z * (b : ℝ) / U| ≤ C * M / T := by
    calc
      |z * (b : ℝ) / U| = z * |(b : ℝ)| / U := by
        rw [abs_div, abs_mul, abs_of_nonneg hz.1, abs_of_pos hU]
      _ ≤ z * (U / T) / U := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hb hz.1) hU.le
      _ = z / T := by field_simp
      _ ≤ C * M / T := div_le_div_of_nonneg_right hz.2 hT.le
  have haterm : |M * (a : ℝ) / V| ≤ (C + 1) * M / T := by
    calc
      |M * (a : ℝ) / V| =
          |(M * (a : ℝ) / V - z * (b : ℝ) / U) + z * (b : ℝ) / U| := by
        congr 1
        ring
      _ ≤ |M * (a : ℝ) / V - z * (b : ℝ) / U| + |z * (b : ℝ) / U| := abs_add_le _ _
      _ ≤ 1 / T + C * M / T := add_le_add hfirst hzterm
      _ ≤ M / T + C * M / T := add_le_add
        (div_le_div_of_nonneg_right hM hT.le) le_rfl
      _ = (C + 1) * M / T := by ring
  have ha : |(a : ℝ)| ≤ (C + 1) * V / T := by
    rw [abs_div, abs_mul, abs_of_pos hMpos, abs_of_pos hV] at haterm
    have hh := (div_le_iff₀ hV).mp haterm
    have hh' : M * |(a : ℝ)| ≤ M * ((C + 1) * V / T) := by
      calc
        M * |(a : ℝ)| ≤ ((C + 1) * M / T) * V := hh
        _ = M * ((C + 1) * V / T) := by ring
    exact (mul_le_mul_iff_right₀ hMpos).mp hh'
  exact ⟨ha, hb⟩

private theorem fixed_vector_center_count
    {ι : Type*} (J : Finset ι) (z : ι → ℝ) (U V M T sep : ℝ)
    (hU : 0 < U) (hT : 0 < T) (hsep : 0 < sep)
    (hseparated : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → sep ≤ |z i - z j|)
    (a b : ℤ) (hb : b ≠ 0) :
    let S := J.filter fun i => |M * (a : ℝ) / V - z i * (b : ℝ) / U| ≤ 1 / T
    (S.card : ℝ) ≤ 1 + (2 * U / (sep * T)) / |(b : ℝ)| := by
  classical
  dsimp only
  let S := J.filter fun i => |M * (a : ℝ) / V - z i * (b : ℝ) / U| ≤ 1 / T
  let w : ι → ℝ := fun i => M * (a : ℝ) / V - z i * (b : ℝ) / U
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  have habs : 0 < |(b : ℝ)| := abs_pos.mpr hbR
  have hspacing : 0 < sep * |(b : ℝ)| / U := by positivity
  have hbound := card_le_one_add_div_of_separated_real_centers
    S w (-(1 / T)) (1 / T) (sep * |(b : ℝ)| / U) hspacing
    (by
      have hnonneg : 0 ≤ 1 / T := by positivity
      linarith) (by
      intro i hi
      exact abs_le.mp (Finset.mem_filter.mp hi).2) (by
      intro i hi j hj hne
      have hs := hseparated i (Finset.mem_filter.mp hi).1
        j (Finset.mem_filter.mp hj).1 hne
      have hid : w i - w j = -(z i - z j) * (b : ℝ) / U := by
        dsimp [w]
        ring
      rw [hid, abs_div, abs_mul, abs_neg, abs_of_pos hU]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hs habs.le) hU.le)
  have heq : 1 + (1 / T - -(1 / T)) / (sep * |(b : ℝ)| / U) =
      1 + (2 * U / (sep * T)) / |(b : ℝ)| := by field_simp; ring
  simpa only [heq] using hbound

private def signedMagnitude (s : Bool) (n : ℕ) : ℤ := if s then n else -n

private theorem abs_cast_signedMagnitude (s : Bool) (n : ℕ) :
    |(signedMagnitude s n : ℝ)| = (n : ℝ) := by
  cases s <;> simp [signedMagnitude]

private theorem signedMagnitude_ne_zero (s : Bool) {n : ℕ} (hn : 0 < n) :
    signedMagnitude s n ≠ 0 := by
  cases s <;> simp [signedMagnitude, Nat.ne_of_gt hn]

open scoped Finset

private def signedMagnitudePairs (A B : ℕ) :
    Finset ((Bool × ℕ) × (Bool × ℕ)) :=
  ((Finset.univ : Finset Bool) ×ˢ (Finset.Icc 1 A)) ×ˢ
    ((Finset.univ : Finset Bool) ×ˢ (Finset.Icc 1 B))

private theorem sum_signedMagnitudePairs_capacity (A B : ℕ) (R : ℝ) :
    ∑ c ∈ signedMagnitudePairs A B, (1 + R / (c.2.2 : ℝ)) =
      4 * (A : ℝ) * B + 4 * (A : ℝ) * R * (harmonic B : ℝ) := by
  have hinner : ∑ b ∈ Finset.Icc 1 B, (1 + R / (b : ℝ)) =
      (B : ℝ) + R * (harmonic B : ℝ) := by
    simp only [Finset.sum_add_distrib, div_eq_mul_inv, ← Finset.mul_sum]
    simp [harmonic_eq_sum_Icc]
  unfold signedMagnitudePairs
  rw [Finset.sum_product]
  simp only [Finset.sum_product]
  simp only [hinner, Finset.sum_const, Finset.card_univ, Fintype.card_bool,
    nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]
  ring

private theorem card_centers_le_signedMagnitudePairs_capacity
    {ι : Type*} (J : Finset ι) (z : ι → ℝ) (U V M T sep : ℝ)
    (hU : 0 < U) (hT : 0 < T) (hsep : 0 < sep)
    (hseparated : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → sep ≤ |z i - z j|)
    (A B : ℕ)
    (hwitness : ∀ i ∈ J, ∃ a b : ℤ, a ≠ 0 ∧ b ≠ 0 ∧
      a.natAbs ≤ A ∧ b.natAbs ≤ B ∧
      |M * (a : ℝ) / V - z i * (b : ℝ) / U| ≤ 1 / T) :
    (J.card : ℝ) ≤ 4 * (A : ℝ) * B +
      8 * (A : ℝ) * (U / T) / sep * (harmonic B : ℝ) := by
  classical
  let cells : ((Bool × ℕ) × (Bool × ℕ)) → Finset ι := fun c =>
    J.filter fun i =>
      |M * (signedMagnitude c.1.1 c.1.2 : ℝ) / V -
        z i * (signedMagnitude c.2.1 c.2.2 : ℝ) / U| ≤ 1 / T
  have hcover : J ⊆ (signedMagnitudePairs A B).biUnion cells := by
    intro i hi
    obtain ⟨a, b, ha, hb, hA, hB, hv⟩ := hwitness i hi
    have haN : 0 < a.natAbs := Int.natAbs_pos.mpr ha
    have hbN : 0 < b.natAbs := Int.natAbs_pos.mpr hb
    obtain ⟨sa, hsa⟩ : ∃ sa : Bool, signedMagnitude sa a.natAbs = a := by
      rcases (Int.natAbs_eq_iff.mp (rfl : a.natAbs = a.natAbs)) with h | h
      · exact ⟨true, h.symm⟩
      · exact ⟨false, h.symm⟩
    obtain ⟨sb, hsb⟩ : ∃ sb : Bool, signedMagnitude sb b.natAbs = b := by
      rcases (Int.natAbs_eq_iff.mp (rfl : b.natAbs = b.natAbs)) with h | h
      · exact ⟨true, h.symm⟩
      · exact ⟨false, h.symm⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨((sa, a.natAbs), (sb, b.natAbs)), ?_, ?_⟩
    · unfold signedMagnitudePairs
      simp only [Finset.mem_product, Finset.mem_univ,
        true_and, Finset.mem_Icc]
      exact ⟨⟨haN, hA⟩, ⟨hbN, hB⟩⟩
    · simp only [cells, hsa, hsb, Finset.mem_filter]
      exact ⟨hi, hv⟩
  have hcapacity : ∀ c ∈ signedMagnitudePairs A B,
      ((cells c).card : ℝ) ≤ 1 + (2 * U / (sep * T)) / (c.2.2 : ℝ) := by
    intro c hc
    have hbpos : 0 < c.2.2 := by
      have hmem := (Finset.mem_product.mp hc).2
      exact (Finset.mem_Icc.mp (Finset.mem_product.mp hmem).2).1
    have hbound := fixed_vector_center_count J z U V M T sep hU hT hsep hseparated
      (signedMagnitude c.1.1 c.1.2) (signedMagnitude c.2.1 c.2.2)
      (signedMagnitude_ne_zero _ hbpos)
    simpa only [abs_cast_signedMagnitude] using hbound
  calc
    (J.card : ℝ) ≤ ∑ c ∈ signedMagnitudePairs A B, ((cells c).card : ℝ) := by
      exact_mod_cast (Finset.card_le_card hcover).trans Finset.card_biUnion_le
    _ ≤ ∑ c ∈ signedMagnitudePairs A B,
        (1 + (2 * U / (sep * T)) / (c.2.2 : ℝ)) := Finset.sum_le_sum hcapacity
    _ = 4 * (A : ℝ) * B +
        8 * (A : ℝ) * (U / T) / sep * (harmonic B : ℝ) := by
      rw [sum_signedMagnitudePairs_capacity]
      ring

/-- The finite harmonic estimate for actual non-axis short-vector centers.
Both signed integer coordinates are enumerated up to their proved bounds;
in particular there is no assumed witness-capacity or minima hypothesis. -/
theorem card_nonAxisSlopeShortVectorCells_le_harmonic
    {ι : Type*} (J : Finset ι) (z : ι → ℝ) (U V M T C sep : ℝ)
    (hU : 0 < U) (hV : 0 < V) (hM : 1 ≤ M) (hT : 0 < T)
    (hC : 0 ≤ C) (hsep : 0 < sep)
    (hcenters : ∀ i ∈ J, 0 ≤ z i ∧ z i ≤ C * M)
    (hseparated : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → sep ≤ |z i - z j|) :
    ((nonAxisSlopeShortVectorCells J z U V M T).card : ℝ) ≤
      4 * (⌊(C + 1) * V / T⌋₊ : ℝ) * ⌊U / T⌋₊ +
      8 * (⌊(C + 1) * V / T⌋₊ : ℝ) * (U / T) / sep *
        (harmonic ⌊U / T⌋₊ : ℝ) := by
  classical
  apply card_centers_le_signedMagnitudePairs_capacity
    (nonAxisSlopeShortVectorCells J z U V M T) z U V M T sep hU hT hsep
  · intro i hi j hj hij
    exact hseparated i (Finset.mem_filter.mp hi).1
      j (Finset.mem_filter.mp hj).1 hij
  · intro i hi
    have himem := Finset.mem_filter.mp hi
    obtain ⟨a, b, ha, hb, hv⟩ := himem.2
    have hcoords := abs_coordinates_le_of_slope_short_vector U V M T C (z i)
      hU hV hM hT (hcenters i himem.1) a b hv
    refine ⟨a, b, ha, hb, ?_, ?_, (max_le_iff.mp hv).1⟩
    · apply (Nat.le_floor_iff (show 0 ≤ (C + 1) * V / T by positivity)).mpr
      simpa only [Nat.cast_natAbs, Int.cast_abs] using hcoords.1
    · apply (Nat.le_floor_iff (show 0 ≤ U / T by positivity)).mpr
      simpa only [Nat.cast_natAbs, Int.cast_abs] using hcoords.2

end

end PellPaper
