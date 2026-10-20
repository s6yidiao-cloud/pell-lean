import Pell.GeneralBidegreePositiveRealWeightedTriangularUpper
import Pell.GeneralBidegreePositiveRealWeightedShellLower

/-!
# A shifted sharp triangular cap for the positive real weighted rank

The high branch in the sheared determinant calculation is a difference of
two weighted triangles.  This module supplies the missing lower triangular
lattice bound for the inner triangle and subtracts it from the existing
sharp upper bound for the outer triangle.  The resulting cap retains the
negative quadratic shift term and makes every boundary loss explicit.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- A positive real weighted lattice triangle contains at least its
continuous triangular area, together with a positive half-boundary term. -/
theorem triangularAreaLower_le_card_generalBidegreePositiveRealWeightedBall
    (ellM ellX S : ℝ) (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX)
    (hS : 0 ≤ S) :
    S ^ 2 / (2 * ellM * ellX) + S / (2 * ellM) ≤
      ((generalBidegreePositiveRealWeightedBall ellM ellX S hellM_pos hell).card : ℝ) := by
  have hellX_pos : 0 < ellX := hellM_pos.trans_le hell
  let J : ℕ := ⌊S / ellX⌋₊
  have hJ_def : J = ⌊S / ellX⌋₊ := rfl
  have hterm (j : ℕ) (_hj : j ∈ Finset.range (J + 1)) :
      (S - (j : ℝ) * ellX) / ellM ≤
        ((⌊(S - (j : ℝ) * ellX) / ellM⌋₊ + 1 : ℕ) : ℝ) := by
    have hlt := Nat.lt_floor_add_one
      ((S - (j : ℝ) * ellX) / ellM)
    push_cast
    exact hlt.le
  have hsum := Finset.sum_le_sum hterm
  have hcard :
      ((generalBidegreePositiveRealWeightedBall ellM ellX S hellM_pos hell).card : ℝ) =
        ∑ j ∈ Finset.range (J + 1),
          ((⌊(S - (j : ℝ) * ellX) / ellM⌋₊ + 1 : ℕ) : ℝ) := by
    rw [card_generalBidegreePositiveRealWeightedBall_eq_floorSum'
      ellM ellX S hellM_pos hell hS]
    change ((∑ j ∈ Finset.range (J + 1),
      (⌊(S - (j : ℝ) * ellX) / ellM⌋₊ + 1) : ℕ) : ℝ) = _
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
          (S - (j : ℝ) * ellX) / ellM =
        ((J : ℝ) + 1) * (S / ellM) -
          (ellX / ellM) * ((J : ℝ) * ((J : ℝ) + 1) / 2) := by
    calc
      ∑ j ∈ Finset.range (J + 1),
          (S - (j : ℝ) * ellX) / ellM =
        ∑ j ∈ Finset.range (J + 1),
          (S / ellM - (j : ℝ) * (ellX / ellM)) := by
            apply Finset.sum_congr rfl
            intro j hj
            field_simp [ne_of_gt hellM_pos]
      _ = ∑ j ∈ Finset.range (J + 1), (S / ellM) -
          ∑ j ∈ Finset.range (J + 1), (j : ℝ) * (ellX / ellM) := by
            rw [Finset.sum_sub_distrib]
      _ = ((J : ℝ) + 1) * (S / ellM) -
          (ellX / ellM) * ((J : ℝ) * ((J : ℝ) + 1) / 2) := by
            rw [Finset.sum_const, ← Finset.sum_mul, hsum_id]
            simp
            ring
  have hJ_upper : (J : ℝ) ≤ S / ellX := by
    rw [hJ_def]
    exact Nat.floor_le (div_nonneg hS hellX_pos.le)
  have hdelta_nonneg : 0 ≤ S / ellX - (J : ℝ) := sub_nonneg.mpr hJ_upper
  have hJ_lt : S / ellX < (J : ℝ) + 1 := by
    rw [hJ_def]
    exact Nat.lt_floor_add_one _
  have hdelta_le_one : S / ellX - (J : ℝ) ≤ 1 := by linarith
  have hdelta_tail_nonneg : 0 ≤ 1 - (S / ellX - (J : ℝ)) := by linarith
  have hcoefficient_nonneg : 0 ≤ (ellX / ellM) / 2 := by
    positivity
  have hidentity :
      (((J : ℝ) + 1) * (S / ellM) -
        (ellX / ellM) * ((J : ℝ) * ((J : ℝ) + 1) / 2)) -
          (S ^ 2 / (2 * ellM * ellX) + S / (2 * ellM)) =
        (ellX / ellM) / 2 *
          (S / ellX - (J : ℝ)) * (1 - (S / ellX - (J : ℝ))) := by
    field_simp [ne_of_gt hellM_pos, ne_of_gt hellX_pos]
    ring
  have hmain :
      S ^ 2 / (2 * ellM * ellX) + S / (2 * ellM) ≤
        ((J : ℝ) + 1) * (S / ellM) -
          (ellX / ellM) * ((J : ℝ) * ((J : ℝ) + 1) / 2) := by
    rw [← sub_nonneg, hidentity]
    exact mul_nonneg (mul_nonneg hcoefficient_nonneg hdelta_nonneg)
      hdelta_tail_nonneg
  calc
    S ^ 2 / (2 * ellM * ellX) + S / (2 * ellM) ≤
        ((J : ℝ) + 1) * (S / ellM) -
          (ellX / ellM) * ((J : ℝ) * ((J : ℝ) + 1) / 2) := hmain
    _ = ∑ j ∈ Finset.range (J + 1),
          (S - (j : ℝ) * ellX) / ellM := hsum_eval.symm
    _ ≤ ∑ j ∈ Finset.range (J + 1),
          ((⌊(S - (j : ℝ) * ellX) / ellM⌋₊ + 1 : ℕ) : ℝ) := hsum
    _ = ((generalBidegreePositiveRealWeightedBall ellM ellX S hellM_pos hell).card : ℝ) :=
      hcard.symm

/-- Subtracting the lower inner triangle from the sharp outer triangle gives
the shifted high-branch lattice cap.  Its main part is
`d * R / (ellM * ellX) - d^2 / (2 * ellM * ellX)`; the remaining terms are
the displayed linear boundary loss. -/
theorem cast_card_sub_card_generalBidegreePositiveRealWeightedBall_le_shiftedSharpArea
    (ellM ellX R d : ℝ) (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX)
    (hd : 0 ≤ d) (hshift : 0 ≤ R - d) :
    ((
      (generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell).card -
        (generalBidegreePositiveRealWeightedBall ellM ellX (R - d)
          hellM_pos hell).card : ℕ) : ℝ) ≤
      d * R / (ellM * ellX) - d ^ 2 / (2 * ellM * ellX) +
        R / (2 * ellM) + R / ellX + d / (2 * ellM) + 1 := by
  have hellX_pos : 0 < ellX := hellM_pos.trans_le hell
  have hR : 0 ≤ R := by linarith
  have hsubset :
      generalBidegreePositiveRealWeightedBall ellM ellX (R - d) hellM_pos hell ⊆
        generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell := by
    apply generalBidegreePositiveRealWeightedBall_subset_of_radius_le
    linarith
  have hcard_nat :
      (generalBidegreePositiveRealWeightedBall ellM ellX (R - d)
        hellM_pos hell).card ≤
        (generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell).card :=
    Finset.card_le_card hsubset
  have houter := card_generalBidegreePositiveRealWeightedBall_cast_le_triangularArea
    ellM ellX R hellM_pos hell hR
  have hinner := triangularAreaLower_le_card_generalBidegreePositiveRealWeightedBall
    ellM ellX (R - d) hellM_pos hell hshift
  rw [Nat.cast_sub hcard_nat]
  calc
    ((generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell).card : ℝ) -
        ((generalBidegreePositiveRealWeightedBall ellM ellX (R - d)
          hellM_pos hell).card : ℝ) ≤
        (R ^ 2 / (2 * ellM * ellX) + R / ellM + R / ellX + 1) -
          ((R - d) ^ 2 / (2 * ellM * ellX) + (R - d) / (2 * ellM)) :=
      sub_le_sub houter hinner
    _ = d * R / (ellM * ellX) - d ^ 2 / (2 * ellM * ellX) +
          R / (2 * ellM) + R / ellX + d / (2 * ellM) + 1 := by
      field_simp [ne_of_gt hellM_pos, ne_of_gt hellX_pos]
      ring

/-- The shifted sharp lattice estimate applied to the coefficient-evaluation
rank.  This is the high branch whose negative quadratic shift supplies the
last cubic term in the source's two-regime integral. -/
theorem generalBidegreeCoefficientEvaluationRank_positiveRealWeightedBall_cast_le_shiftedSharpArea
    (A B : ℕ) (ellM ellX R : ℝ)
    (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX)
    (hshift : 0 ≤ R - ((A + 1 : ℕ) : ℝ) * ellX) :
    (generalBidegreeCoefficientEvaluationRank A B
      (generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell) : ℝ) ≤
      ((A + 1 : ℕ) : ℝ) * ellX * R / (ellM * ellX) -
          (((A + 1 : ℕ) : ℝ) * ellX) ^ 2 / (2 * ellM * ellX) +
        R / (2 * ellM) + R / ellX +
          ((A + 1 : ℕ) : ℝ) * ellX / (2 * ellM) + 1 := by
  have hellX_pos : 0 < ellX := hellM_pos.trans_le hell
  have hshift_nonneg : 0 ≤ ((A + 1 : ℕ) : ℝ) * ellX := by
    positivity
  have hrank_nat :=
    generalBidegreeCoefficientEvaluationRank_positiveRealWeightedBall_le_shifted
      A B ellM ellX R hellM_pos hell
  have hrank_cast :
      (generalBidegreeCoefficientEvaluationRank A B
        (generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell) : ℝ) ≤
        ((
          (generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell).card -
            (generalBidegreePositiveRealWeightedBall ellM ellX
              (R - ((A + 1 : ℕ) : ℝ) * ellX) hellM_pos hell).card : ℕ) : ℝ) := by
    exact_mod_cast hrank_nat
  exact hrank_cast.trans
    (cast_card_sub_card_generalBidegreePositiveRealWeightedBall_le_shiftedSharpArea
      ellM ellX R (((A + 1 : ℕ) : ℝ) * ellX) hellM_pos hell hshift_nonneg hshift)

end

end PellPaper
