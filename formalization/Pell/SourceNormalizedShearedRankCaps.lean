import Pell.GeneralBidegreePositiveRealWeightedShiftedSharpUpper
import Pell.ShearedContinuousCubicIntegral

/-!
# Source-normalized sheared rank caps

This file is the finite normalization adapter from the positive-real weighted
rank bounds to the variables used in the two-regime sheared calculation.  We
put

`ellM = m * L`, `ellX = x * L`, `R = lambda * B * L`, and
`rho = A / B`.

The leading pieces of the triangular and shifted-shell rank bounds then are
exactly `B^2` times `shearedTriangularCap` and `shearedShellCap`.  The
remaining lattice boundary terms are retained as explicit real expressions.
-/

namespace PellPaper

noncomputable section

/-- The explicit boundary error in the source-normalized triangular cap. -/
def sourceNormalizedTriangularCapError (B : ℕ) (m x lambda : ℝ) : ℝ :=
  (B : ℝ) * (lambda / m + lambda / x) + 1

/-- The exact boundary remainder after expressing the shifted sharp area
bound in terms of `rho = A / B`.  Its final negative summand can be dropped
when a manifestly nonnegative `O(B)` envelope is more convenient. -/
def sourceNormalizedShellCapExactRemainder (B : ℕ) (rho m x lambda : ℝ) : ℝ :=
  (B : ℝ) *
      (3 * lambda / (2 * m) + lambda / x - rho * x / (2 * m)) + 1

/-- A manifestly nonnegative explicit `O(B)` boundary envelope for the
source-normalized shifted-shell cap. -/
def sourceNormalizedShellCapError (B : ℕ) (m x lambda : ℝ) : ℝ :=
  (B : ℝ) * (3 * lambda / (2 * m) + lambda / x) + 1

/-- The triangular boundary error is nonnegative in the range relevant to
the sheared filtration. -/
theorem sourceNormalizedTriangularCapError_nonneg
    (B : ℕ) {m x lambda : ℝ}
    (hB : 0 < B) (hm : 0 < m) (hx : 0 < x) (hlambda : 0 ≤ lambda) :
    0 ≤ sourceNormalizedTriangularCapError B m x lambda := by
  rw [sourceNormalizedTriangularCapError]
  have hB_real : 0 ≤ (B : ℝ) := by positivity
  have hm_ne : m ≠ 0 := ne_of_gt hm
  have hx_ne : x ≠ 0 := ne_of_gt hx
  have hbody : 0 ≤ lambda / m + lambda / x := by
    exact add_nonneg (div_nonneg hlambda hm.le) (div_nonneg hlambda hx.le)
  positivity

/-- The shifted-shell boundary error is nonnegative when the inner shifted
radius is nonnegative.  This is also the hypothesis needed by the sharp
shifted lattice estimate. -/
theorem sourceNormalizedShellCapExactRemainder_nonneg_of_shift
    (A B : ℕ) {m x lambda L : ℝ}
    (hB : 0 < B) (hm : 0 < m) (hx : 0 < x) (hL : 0 < L)
    (hshift : 0 ≤ lambda * (B : ℝ) * L -
      ((A + 1 : ℕ) : ℝ) * (x * L)) :
    0 ≤ sourceNormalizedShellCapExactRemainder B ((A : ℝ) / (B : ℝ)) m x lambda := by
  have hB_real : 0 < (B : ℝ) := by exact_mod_cast hB
  have hA_nonneg : 0 ≤ (A : ℝ) := by positivity
  have hAone_nonneg : 0 ≤ ((A + 1 : ℕ) : ℝ) := by positivity
  have hRHS_nonneg : 0 ≤ ((A + 1 : ℕ) : ℝ) * (x * L) := by positivity
  have hlambdaB : ((A + 1 : ℕ) : ℝ) * x ≤ lambda * (B : ℝ) := by
    have hmul : ((A + 1 : ℕ) : ℝ) * (x * L) ≤
        lambda * (B : ℝ) * L := by
      linarith
    have hL_ne : L ≠ 0 := ne_of_gt hL
    calc
      ((A + 1 : ℕ) : ℝ) * x =
          (((A + 1 : ℕ) : ℝ) * (x * L)) / L := by
            field_simp [hL_ne]
      _ ≤ (lambda * (B : ℝ) * L) / L :=
          (div_le_div_iff_of_pos_right hL).mpr hmul
      _ = lambda * (B : ℝ) := by field_simp [hL_ne]
  have hAx : (A : ℝ) * x ≤ lambda * (B : ℝ) := by
    calc
      (A : ℝ) * x ≤ ((A + 1 : ℕ) : ℝ) * x := by
        have hA_le : (A : ℝ) ≤ ((A + 1 : ℕ) : ℝ) := by
          norm_num
        exact mul_le_mul_of_nonneg_right hA_le hx.le
      _ ≤ lambda * (B : ℝ) := hlambdaB
  have hrho_x : ((A : ℝ) / (B : ℝ)) * x ≤ lambda := by
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hB_real).mpr (by simpa [mul_comm] using hAx)
  have hlambda_nonneg : 0 ≤ lambda := by
    have hAx_nonneg : 0 ≤ (A : ℝ) * x := mul_nonneg hA_nonneg hx.le
    have hlambdaB_nonneg : 0 ≤ lambda * (B : ℝ) := hAx_nonneg.trans hAx
    by_contra hnot
    have hneg : lambda < 0 := lt_of_not_ge hnot
    have hprod_neg : lambda * (B : ℝ) < 0 :=
      mul_neg_of_neg_of_pos hneg hB_real
    linarith
  have hthree_lambda : 0 ≤ 3 * lambda - ((A : ℝ) / (B : ℝ)) * x := by
    nlinarith
  have hfirst : 0 ≤
      3 * lambda / (2 * m) - ((A : ℝ) / (B : ℝ)) * x / (2 * m) := by
    rw [← sub_div]
    exact div_nonneg hthree_lambda (by positivity)
  have hbody : 0 ≤
      3 * lambda / (2 * m) + lambda / x -
        ((A : ℝ) / (B : ℝ)) * x / (2 * m) := by
    linarith [div_nonneg hlambda_nonneg hx.le]
  rw [sourceNormalizedShellCapExactRemainder]
  positivity

/-- The manifestly nonnegative shell error follows from the exact shifted
radius condition. -/
theorem sourceNormalizedShellCapError_nonneg_of_shift
    (A B : ℕ) {m x lambda L : ℝ}
    (hB : 0 < B) (hm : 0 < m) (hx : 0 < x) (hL : 0 < L)
    (hshift : 0 ≤ lambda * (B : ℝ) * L -
      ((A + 1 : ℕ) : ℝ) * (x * L)) :
    0 ≤ sourceNormalizedShellCapError B m x lambda := by
  have hB_real : 0 < (B : ℝ) := by exact_mod_cast hB
  have hRHS_nonneg : 0 ≤ ((A + 1 : ℕ) : ℝ) * (x * L) := by positivity
  have hlambdaB_L : 0 ≤ lambda * (B : ℝ) * L := by linarith
  have hlambda_nonneg : 0 ≤ lambda := by
    by_contra hnot
    have hneg : lambda < 0 := lt_of_not_ge hnot
    have hprod_neg : lambda * (B : ℝ) * L < 0 := by
      exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hneg hB_real) hL
    linarith
  rw [sourceNormalizedShellCapError]
  have hbody : 0 ≤ 3 * lambda / (2 * m) + lambda / x := by
    exact add_nonneg (div_nonneg (by positivity) (by positivity))
      (div_nonneg hlambda_nonneg hx.le)
  positivity

/-- Under the source normalization, the positive-real weighted coefficient
rank obeys the sharp triangular cap, with its complete finite boundary
error displayed. -/
theorem generalBidegreeCoefficientEvaluationRank_sourceNormalized_le_triangularCap
    (A B : ℕ) (m x lambda L : ℝ)
    (hB : 0 < B) (hm : 0 < m) (hmx : m ≤ x) (hL : 0 < L)
    (hlambda : 0 ≤ lambda) :
    (generalBidegreeCoefficientEvaluationRank A B
      (generalBidegreePositiveRealWeightedBall (m * L) (x * L)
        (lambda * (B : ℝ) * L) (mul_pos hm hL)
        (mul_le_mul_of_nonneg_right hmx hL.le) :
        Finset generalBidegreeWeightedMonomialIndex) : ℝ) ≤
      (B : ℝ) ^ 2 * shearedTriangularCap m x lambda +
        sourceNormalizedTriangularCapError B m x lambda := by
  have hB_real : 0 < (B : ℝ) := by exact_mod_cast hB
  have hx : 0 < x := hm.trans_le hmx
  have hellM_pos : 0 < m * L := mul_pos hm hL
  have hell : m * L ≤ x * L := mul_le_mul_of_nonneg_right hmx hL.le
  have hR : 0 ≤ lambda * (B : ℝ) * L := by positivity
  have hrank_nat :
      generalBidegreeCoefficientEvaluationRank A B
          (generalBidegreePositiveRealWeightedBall (m * L) (x * L)
            (lambda * (B : ℝ) * L) hellM_pos hell) ≤
        (generalBidegreePositiveRealWeightedBall (m * L) (x * L)
          (lambda * (B : ℝ) * L) hellM_pos hell).card := by
    calc
      generalBidegreeCoefficientEvaluationRank A B
          (generalBidegreePositiveRealWeightedBall (m * L) (x * L)
            (lambda * (B : ℝ) * L) hellM_pos hell) ≤
          (generalBidegreePositiveRealWeightedBall (m * L) (x * L)
            (lambda * (B : ℝ) * L) hellM_pos hell).card -
            (generalBidegreePositiveRealWeightedBall (m * L) (x * L)
              (lambda * (B : ℝ) * L - ((A + 1 : ℕ) : ℝ) * (x * L))
              hellM_pos hell).card :=
        generalBidegreeCoefficientEvaluationRank_positiveRealWeightedBall_le_shifted
          A B (m * L) (x * L) (lambda * (B : ℝ) * L) hellM_pos hell
      _ ≤ (generalBidegreePositiveRealWeightedBall (m * L) (x * L)
          (lambda * (B : ℝ) * L) hellM_pos hell).card := Nat.sub_le _ _
  have hrank_cast :
      (generalBidegreeCoefficientEvaluationRank A B
          (generalBidegreePositiveRealWeightedBall (m * L) (x * L)
            (lambda * (B : ℝ) * L) hellM_pos hell) : ℝ) ≤
        ((generalBidegreePositiveRealWeightedBall (m * L) (x * L)
          (lambda * (B : ℝ) * L) hellM_pos hell).card : ℝ) := by
    exact_mod_cast hrank_nat
  have htriangle := card_generalBidegreePositiveRealWeightedBall_cast_le_triangularArea
    (m * L) (x * L) (lambda * (B : ℝ) * L) hellM_pos hell hR
  calc
    (generalBidegreeCoefficientEvaluationRank A B
      (generalBidegreePositiveRealWeightedBall (m * L) (x * L)
        (lambda * (B : ℝ) * L) (mul_pos hm hL)
        (mul_le_mul_of_nonneg_right hmx hL.le) :
        Finset generalBidegreeWeightedMonomialIndex) : ℝ) =
        (generalBidegreeCoefficientEvaluationRank A B
          (generalBidegreePositiveRealWeightedBall (m * L) (x * L)
            (lambda * (B : ℝ) * L) hellM_pos hell) : ℝ) := by
          congr 3
    _ ≤ ((generalBidegreePositiveRealWeightedBall (m * L) (x * L)
          (lambda * (B : ℝ) * L) hellM_pos hell).card : ℝ) := hrank_cast
    _ ≤ (lambda * (B : ℝ) * L) ^ 2 /
          (2 * (m * L) * (x * L)) +
          (lambda * (B : ℝ) * L) / (m * L) +
          (lambda * (B : ℝ) * L) / (x * L) + 1 := htriangle
    _ = (B : ℝ) ^ 2 * shearedTriangularCap m x lambda +
          sourceNormalizedTriangularCapError B m x lambda := by
      rw [shearedTriangularCap, sourceNormalizedTriangularCapError]
      field_simp [ne_of_gt hB_real, ne_of_gt hm, ne_of_gt hx, ne_of_gt hL]
      ring

/-- Under the source normalization, the shifted sharp rank cap has exactly
the source's parallel-line shell leading term.  The stated explicit error is
nonnegative by `sourceNormalizedShellCapExactRemainder_nonneg_of_shift`. -/
theorem generalBidegreeCoefficientEvaluationRank_sourceNormalized_le_shellCap_exactRemainder
    (A B : ℕ) (m x lambda L : ℝ)
    (hB : 0 < B) (hm : 0 < m) (hmx : m ≤ x) (hL : 0 < L)
    (hshift : 0 ≤ lambda * (B : ℝ) * L -
      ((A + 1 : ℕ) : ℝ) * (x * L)) :
    (generalBidegreeCoefficientEvaluationRank A B
      (generalBidegreePositiveRealWeightedBall (m * L) (x * L)
        (lambda * (B : ℝ) * L) (mul_pos hm hL)
        (mul_le_mul_of_nonneg_right hmx hL.le) :
        Finset generalBidegreeWeightedMonomialIndex) : ℝ) ≤
      (B : ℝ) ^ 2 * shearedShellCap ((A : ℝ) / (B : ℝ)) m x lambda +
        sourceNormalizedShellCapExactRemainder B ((A : ℝ) / (B : ℝ)) m x lambda := by
  have hB_real : 0 < (B : ℝ) := by exact_mod_cast hB
  have hx : 0 < x := hm.trans_le hmx
  have hellM_pos : 0 < m * L := mul_pos hm hL
  have hell : m * L ≤ x * L := mul_le_mul_of_nonneg_right hmx hL.le
  have hsharp :=
    generalBidegreeCoefficientEvaluationRank_positiveRealWeightedBall_cast_le_shiftedSharpArea
      A B (m * L) (x * L) (lambda * (B : ℝ) * L) hellM_pos hell (by
        simpa [sub_eq_add_neg] using hshift)
  calc
    (generalBidegreeCoefficientEvaluationRank A B
      (generalBidegreePositiveRealWeightedBall (m * L) (x * L)
        (lambda * (B : ℝ) * L) (mul_pos hm hL)
        (mul_le_mul_of_nonneg_right hmx hL.le) :
        Finset generalBidegreeWeightedMonomialIndex) : ℝ) =
        (generalBidegreeCoefficientEvaluationRank A B
          (generalBidegreePositiveRealWeightedBall (m * L) (x * L)
            (lambda * (B : ℝ) * L) hellM_pos hell) : ℝ) := by
          congr 3
    _ ≤ ((A + 1 : ℕ) : ℝ) * (x * L) *
          (lambda * (B : ℝ) * L) / ((m * L) * (x * L)) -
          (((A + 1 : ℕ) : ℝ) * (x * L)) ^ 2 /
            (2 * (m * L) * (x * L)) +
          (lambda * (B : ℝ) * L) / (2 * (m * L)) +
          (lambda * (B : ℝ) * L) / (x * L) +
            ((A + 1 : ℕ) : ℝ) * (x * L) / (2 * (m * L)) + 1 := hsharp
    _ = (B : ℝ) ^ 2 *
          shearedShellCap ((A : ℝ) / (B : ℝ)) m x lambda +
          sourceNormalizedShellCapExactRemainder B ((A : ℝ) / (B : ℝ)) m x lambda := by
      rw [shearedShellCap, sourceNormalizedShellCapExactRemainder]
      norm_num [Nat.cast_add, Nat.cast_one]
      field_simp [ne_of_gt hB_real, ne_of_gt hm, ne_of_gt hx, ne_of_gt hL]
      ring

/-- The source-normalized shifted-shell cap with a manifestly nonnegative
explicit `O(B)` boundary error.  The exact shifted-radius hypothesis is
retained, so callers may use it directly at the first high mesh point. -/
theorem generalBidegreeCoefficientEvaluationRank_sourceNormalized_le_shellCap
    (A B : ℕ) (m x lambda L : ℝ)
    (hB : 0 < B) (hm : 0 < m) (hmx : m ≤ x) (hL : 0 < L)
    (hshift : 0 ≤ lambda * (B : ℝ) * L -
      ((A + 1 : ℕ) : ℝ) * (x * L)) :
    (generalBidegreeCoefficientEvaluationRank A B
      (generalBidegreePositiveRealWeightedBall (m * L) (x * L)
        (lambda * (B : ℝ) * L) (mul_pos hm hL)
        (mul_le_mul_of_nonneg_right hmx hL.le) :
        Finset generalBidegreeWeightedMonomialIndex) : ℝ) ≤
      (B : ℝ) ^ 2 * shearedShellCap ((A : ℝ) / (B : ℝ)) m x lambda +
        sourceNormalizedShellCapError B m x lambda := by
  have hB_real : 0 < (B : ℝ) := by exact_mod_cast hB
  have hx : 0 < x := hm.trans_le hmx
  have hexact :=
    generalBidegreeCoefficientEvaluationRank_sourceNormalized_le_shellCap_exactRemainder
      A B m x lambda L hB hm hmx hL hshift
  have hrho_nonneg : 0 ≤ (A : ℝ) / (B : ℝ) := by positivity
  have hdiscard_nonneg :
      0 ≤ ((A : ℝ) / (B : ℝ)) * x / (2 * m) := by positivity
  calc
    (generalBidegreeCoefficientEvaluationRank A B
      (generalBidegreePositiveRealWeightedBall (m * L) (x * L)
        (lambda * (B : ℝ) * L) (mul_pos hm hL)
        (mul_le_mul_of_nonneg_right hmx hL.le) :
        Finset generalBidegreeWeightedMonomialIndex) : ℝ) ≤
        (B : ℝ) ^ 2 * shearedShellCap ((A : ℝ) / (B : ℝ)) m x lambda +
          sourceNormalizedShellCapExactRemainder B ((A : ℝ) / (B : ℝ)) m x lambda :=
      hexact
    _ ≤ (B : ℝ) ^ 2 * shearedShellCap ((A : ℝ) / (B : ℝ)) m x lambda +
          sourceNormalizedShellCapError B m x lambda := by
      apply add_le_add_right
      rw [sourceNormalizedShellCapExactRemainder, sourceNormalizedShellCapError]
      apply add_le_add_left
      exact mul_le_mul_of_nonneg_left (sub_le_self _ hdiscard_nonneg) hB_real.le

/-- With the source mesh size `x / B`, the low-branch endpoint indexed by
`A` is exactly the crossover `x * rho`. -/
theorem sourceNormalized_lowMesh_alignment
    (A B : ℕ) (x : ℝ) (hB : 0 < B) :
    (A : ℝ) * (x / (B : ℝ)) = x * ((A : ℝ) / (B : ℝ)) := by
  have hB_real : 0 < (B : ℝ) := by exact_mod_cast hB
  field_simp [ne_of_gt hB_real]

/-- With the same source mesh size, the first high-branch point has exactly
zero shifted radius, hence satisfies the shifted sharp-cap hypothesis. -/
theorem sourceNormalized_firstHighMesh_shift_radius_eq_zero
    (A B : ℕ) (x L : ℝ) (hB : 0 < B) :
    (x * ((A : ℝ) / (B : ℝ)) + x / (B : ℝ)) * (B : ℝ) * L -
      ((A + 1 : ℕ) : ℝ) * (x * L) = 0 := by
  have hB_real : 0 < (B : ℝ) := by exact_mod_cast hB
  norm_num [Nat.cast_add, Nat.cast_one]
  field_simp [ne_of_gt hB_real]
  ring

end

end PellPaper
