import Pell.GeneralBidegreePositiveRealWeightedCount
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# A sharp triangular cap for positive real weighted lattice balls

The exact floor sum for a two-dimensional positive weighted ball has the
expected half-area leading term.  This file makes that estimate finite and
explicit, retaining only linear lattice-boundary terms.  It is designed for
the low-radius branch of the two-regime greedy filtration.
-/

namespace PellPaper

/-- The positive real weighted lattice ball is at most its triangular area,
with explicit linear boundary losses.  In particular, the quadratic leading
coefficient is `1 / (2 * ellM * ellX)`, rather than the rectangular
coefficient `1 / (ellM * ellX)`. -/
theorem card_generalBidegreePositiveRealWeightedBall_cast_le_triangularArea
    (ellM ellX R : ℝ) (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX)
    (hR : 0 ≤ R) :
    ((generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell).card : ℕ) ≤
      R ^ 2 / (2 * ellM * ellX) + R / ellM + R / ellX + 1 := by
  have hellX_pos : 0 < ellX := hellM_pos.trans_le hell
  let J : ℕ := ⌊R / ellX⌋₊
  have hJ_def : J = ⌊R / ellX⌋₊ := rfl
  have hterm (j : ℕ) (hj : j ∈ Finset.range (J + 1)) :
      ((⌊(R - (j : ℝ) * ellX) / ellM⌋₊ + 1 : ℕ) : ℝ) ≤
        (R - (j : ℝ) * ellX) / ellM + 1 := by
    have hjle : j ≤ J := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hR_div_nonneg : 0 ≤ R / ellX := div_nonneg hR hellX_pos.le
    have hjdiv : (j : ℝ) ≤ R / ellX := by
      rw [hJ_def] at hjle
      exact (Nat.le_floor_iff hR_div_nonneg).mp hjle
    have hjmul : (j : ℝ) * ellX ≤ R :=
      (le_div_iff₀ hellX_pos).mp hjdiv
    have hres_nonneg : 0 ≤ R - (j : ℝ) * ellX := by linarith
    have hres_div_nonneg : 0 ≤ (R - (j : ℝ) * ellX) / ellM :=
      div_nonneg hres_nonneg hellM_pos.le
    push_cast
    linarith [Nat.floor_le hres_div_nonneg]
  have hsum := Finset.sum_le_sum hterm
  have hcard :
      ((generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell).card : ℕ) =
        ∑ j ∈ Finset.range (J + 1),
          ((⌊(R - (j : ℝ) * ellX) / ellM⌋₊ + 1 : ℕ) : ℝ) := by
    rw [card_generalBidegreePositiveRealWeightedBall_eq_floorSum'
      ellM ellX R hellM_pos hell hR]
    change ((∑ j ∈ Finset.range (J + 1),
      (⌊(R - (j : ℝ) * ellX) / ellM⌋₊ + 1) : ℕ) : ℝ) = _
    push_cast
    rfl
  have hsum_id_twice :
      (∑ j ∈ Finset.range (J + 1), (j : ℝ)) * 2 =
        (J : ℝ) * ((J : ℝ) + 1) := by
    have h := congrArg (fun n : ℕ => (n : ℝ))
      (Finset.sum_range_id_mul_two (J + 1))
    norm_num [Nat.cast_mul, Nat.cast_sub, Nat.succ_sub_one] at h ⊢
    linarith
  have hsum_id :
      ∑ j ∈ Finset.range (J + 1), (j : ℝ) =
        (J : ℝ) * ((J : ℝ) + 1) / 2 := by
    linarith [hsum_id_twice]
  have hsum_eval :
      ∑ j ∈ Finset.range (J + 1),
          ((R - (j : ℝ) * ellX) / ellM + 1) =
        ((J : ℝ) + 1) * (R / ellM + 1) -
          (ellX / ellM) * ((J : ℝ) * ((J : ℝ) + 1) / 2) := by
    calc
      ∑ j ∈ Finset.range (J + 1),
          ((R - (j : ℝ) * ellX) / ellM + 1) =
        ∑ j ∈ Finset.range (J + 1),
          (R / ellM + 1 - (j : ℝ) * (ellX / ellM)) := by
            apply Finset.sum_congr rfl
            intro j hj
            field_simp
            ring
      _ = ∑ j ∈ Finset.range (J + 1), (R / ellM + 1) -
          ∑ j ∈ Finset.range (J + 1), (j : ℝ) * (ellX / ellM) := by
            rw [Finset.sum_sub_distrib]
      _ = ((J : ℝ) + 1) * (R / ellM + 1) -
          (ellX / ellM) * ((J : ℝ) * ((J : ℝ) + 1) / 2) := by
            rw [Finset.sum_const, ← Finset.sum_mul, hsum_id]
            simp
            ring
  have hJ_upper : (J : ℝ) ≤ R / ellX := by
    rw [hJ_def]
    exact Nat.floor_le (div_nonneg hR hellX_pos.le)
  have hdelta_nonneg : 0 ≤ R / ellX - (J : ℝ) := sub_nonneg.mpr hJ_upper
  have hJ_nonneg : 0 ≤ (J : ℝ) := by positivity
  have hbracket_nonneg : 0 ≤ (R / ellX - (J : ℝ)) ^ 2 + (J : ℝ) :=
    add_nonneg (sq_nonneg _) hJ_nonneg
  have hcoefficient_nonneg : 0 ≤ (ellX / ellM) / 2 :=
    div_nonneg (div_nonneg hellX_pos.le hellM_pos.le) (by norm_num)
  have hidentity :
      (R ^ 2 / (2 * ellM * ellX) + R / ellM + R / ellX + 1) -
        (((J : ℝ) + 1) * (R / ellM + 1) -
          (ellX / ellM) * ((J : ℝ) * ((J : ℝ) + 1) / 2)) =
      (R / ellX - (J : ℝ)) + (ellX / ellM) / 2 *
        ((R / ellX - (J : ℝ)) ^ 2 + (J : ℝ)) := by
    field_simp [ne_of_gt hellM_pos, ne_of_gt hellX_pos]
    ring
  have hfinal :
      ((J : ℝ) + 1) * (R / ellM + 1) -
          (ellX / ellM) * ((J : ℝ) * ((J : ℝ) + 1) / 2) ≤
      R ^ 2 / (2 * ellM * ellX) + R / ellM + R / ellX + 1 := by
    rw [← sub_nonneg]
    rw [hidentity]
    exact add_nonneg hdelta_nonneg (mul_nonneg hcoefficient_nonneg hbracket_nonneg)
  rw [hcard]
  exact hsum.trans (hsum_eval.le.trans hfinal)

end PellPaper
