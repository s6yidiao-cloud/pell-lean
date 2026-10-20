import Pell.FiniteReciprocalSquareTailSummation
import Pell.SlopeLatticeReciprocalMinimumTail

/-!
# Summing actual reciprocal first minima at separated centers

This bounds the sum of the actual reciprocal first sup-norm minima of the
displayed slope maps.  The centers, their range, and separation are explicit.
Attainment, axis exclusion, tail estimates, and finite-tail summation are
proved dependencies, not hypotheses.  Construction of a source/target cover
and any general-curve point count remain separate.
-/

namespace PellPaper

noncomputable section

/-- An explicit square-root-scale budget for the sum of actual reciprocal
first sup-norm minima over a finite separated family of normalized centers. -/
theorem sum_reciprocalFirstSlopeSupNorm_le
    {ι : Type*} (J : Finset ι) (z : ι → ℝ) (U V M C sep : ℝ)
    (hU : 0 < U) (hV : 0 < V) (hM : 1 ≤ M) (hC : 0 ≤ C) (hsep : 0 < sep)
    (hcenters : ∀ i ∈ J, M / 2 ≤ z i ∧ z i ≤ C * M)
    (hseparated : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → sep ≤ |z i - z j|) :
    (∑ i ∈ J, reciprocalFirstSlopeSupNorm U V M (z i)) ≤
      (4 * (1 + C / sep) + (4 + 8 / sep) * (C + 1)) *
        (Real.sqrt (U * V * M) + U + V) *
        (1 + Real.log (1 + U / Real.sqrt (U * V / M))) := by
  classical
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  let q := Real.sqrt (U * V / M)
  let W := Real.sqrt (U * V * M)
  let S := 2 * (V + 2 * U) / M + q
  let K := 1 + C / sep
  let A := (4 + 8 / sep) * (C + 1)
  let L := 1 + Real.log (1 + U / q)
  let B := A * (U * V) * L
  have hq : 0 < q := Real.sqrt_pos.mpr (by positivity)
  have hWnonneg : 0 ≤ W := Real.sqrt_nonneg _
  have hS : 0 < S := by dsimp [S]; positivity
  have hqS : q ≤ S := by
    dsimp [S]
    have hpart : 0 ≤ 2 * (V + 2 * U) / M := by positivity
    linarith
  have hfstS : V / M < S := by
    have hpart : 0 < (V + 4 * U) / M := by positivity
    have hdiff : S - V / M = (V + 4 * U) / M + q := by dsimp [S]; ring
    linarith
  have hsndS : 2 * U / M < S := by
    have hpart : 0 < (2 * V + 2 * U) / M := by positivity
    have hdiff : S - 2 * U / M = (2 * V + 2 * U) / M + q := by dsimp [S]; ring
    linarith
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hL : 1 ≤ L := by
    have hratio : 0 ≤ U / q := by positivity
    have hlog := Real.log_nonneg (show 1 ≤ 1 + U / q by linarith)
    dsimp [L]
    linarith
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hrel : U * V = M * q ^ 2 := by
    have hsq : q ^ 2 = U * V / M := Real.sq_sqrt (by positivity)
    have hh := (eq_div_iff hMpos.ne').mp hsq
    nlinarith
  have hMq : M * q = W := by
    dsimp [W]
    rw [hrel]
    have heq : M * q ^ 2 * M = (M * q) ^ 2 := by ring
    rw [heq, Real.sqrt_sq (mul_nonneg hMpos.le hq.le)]
  have hUVq : U * V / q = W := by
    rw [hrel, ← hMq]
    field_simp
  have hcard : (J.card : ℝ) ≤ K * M := by
    have hpack := card_le_one_add_div_of_separated_real_centers J z 0 (C * M) sep
      hsep (by positivity) (by
        intro i hi
        exact ⟨by linarith [(hcenters i hi).1], (hcenters i hi).2⟩) hseparated
    dsimp [K]
    calc
      (J.card : ℝ) ≤ 1 + (C * M - 0) / sep := hpack
      _ ≤ M + (C * M - 0) / sep := add_le_add hM le_rfl
      _ = (1 + C / sep) * M := by ring
  have htail : ∀ T : ℝ, S ≤ T →
      ((J.filter fun i => T ≤ reciprocalFirstSlopeSupNorm U V M (z i)).card : ℝ) ≤ B / T ^ 2 := by
    intro T hST
    have hT : 0 < T := hS.trans_le hST
    have hraw := card_reciprocalFirstSlopeSupNormTail_le_log J z U V M T C sep
      hU hV hM hT hC hsep hcenters hseparated (hfstS.trans_le hST) (hsndS.trans_le hST)
    have hlog : 1 + Real.log (1 + U / T) ≤ L := by
      apply add_le_add le_rfl
      apply Real.log_le_log (by positivity)
      exact add_le_add le_rfl (div_le_div_of_nonneg_left hU.le hq (hqS.trans hST))
    calc
      ((J.filter fun i => T ≤ reciprocalFirstSlopeSupNorm U V M (z i)).card : ℝ) ≤
          A * (U * V / T ^ 2) * (1 + Real.log (1 + U / T)) := hraw
      _ ≤ A * (U * V / T ^ 2) * L := mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = B / T ^ 2 := by dsimp [B]; ring
  have hsum := sum_le_card_mul_cutoff_add_div_of_weak_tail_bound J
    (fun i => reciprocalFirstSlopeSupNorm U V M (z i)) S B hS hB htail
  have hNS : (J.card : ℝ) * S ≤ 4 * K * (W + U + V) * L := by
    calc
      (J.card : ℝ) * S ≤ (K * M) * S := mul_le_mul_of_nonneg_right hcard hS.le
      _ = K * (W + 4 * U + 2 * V) := by
        dsimp [S]
        rw [← hMq]
        field_simp
        ring
      _ ≤ 4 * K * (W + U + V) := by nlinarith
      _ ≤ 4 * K * (W + U + V) * L := by
        have hnonneg : 0 ≤ 4 * K * (W + U + V) := by positivity
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hL hnonneg
  have hBS : B / S ≤ A * (W + U + V) * L := by
    calc
      B / S ≤ B / q := div_le_div_of_nonneg_left hB hq hqS
      _ = A * (U * V / q) * L := by dsimp [B]; ring
      _ = A * W * L := by rw [hUVq]
      _ ≤ A * (W + U + V) * L := by gcongr; linarith
  calc
    (∑ i ∈ J, reciprocalFirstSlopeSupNorm U V M (z i)) ≤ (J.card : ℝ) * S + B / S := hsum
    _ ≤ 4 * K * (W + U + V) * L + A * (W + U + V) * L := add_le_add hNS hBS
    _ = _ := by dsimp [K, A, W, L, q]; ring

end

end PellPaper
