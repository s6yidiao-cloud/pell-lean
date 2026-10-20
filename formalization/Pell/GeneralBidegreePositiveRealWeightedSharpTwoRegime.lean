import Pell.GeneralBidegreePositiveRealWeightedTriangularUpper
import Pell.GeneralBidegreePositiveRealWeightedShellUpper

/-!
# Sharp continuous two-regime cap for the sheared coefficient rank

The exact positive-real weighted rank has both a triangular low-radius cap and
a parallel-line shell cap.  This module packages their real-valued envelopes
as one pointwise minimum, retaining the half-area coefficient in the first
branch needed for the cubic sheared determinant calculation.
-/

namespace PellPaper

/-- The positive-real weighted coefficient rank is bounded by the minimum of
the sharp triangular area cap and the parallel-line shell area cap.  The
first branch has leading term `R^2 / (2 * ellM * ellX)`; all lattice-boundary
losses remain explicit. -/
theorem generalBidegreeCoefficientEvaluationRank_positiveRealWeightedBall_cast_le_sharpTwoRegimeAreaEnvelope
    (A B : ℕ) (ellM ellX R : ℝ)
    (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX) (hR : 0 ≤ R) :
    (generalBidegreeCoefficientEvaluationRank A B
      (generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell) : ℝ) ≤
      min
        (R ^ 2 / (2 * ellM * ellX) + R / ellM + R / ellX + 1)
        ((R / ellX + 1) *
          (((((A + 1 : ℕ) : ℝ) * ellX) / ellM) + 1)) := by
  apply le_min
  · have hrank_nat :
        generalBidegreeCoefficientEvaluationRank A B
          (generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell) ≤
          (generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell).card := by
      calc
        generalBidegreeCoefficientEvaluationRank A B
            (generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell) ≤
            (generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell).card -
              (generalBidegreePositiveRealWeightedBall ellM ellX
                (R - ((A + 1 : ℕ) : ℝ) * ellX) hellM_pos hell).card :=
          generalBidegreeCoefficientEvaluationRank_positiveRealWeightedBall_le_shifted
            A B ellM ellX R hellM_pos hell
        _ ≤ (generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell).card :=
          Nat.sub_le _ _
    have hrank_cast :
        (generalBidegreeCoefficientEvaluationRank A B
          (generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell) : ℝ) ≤
          ((generalBidegreePositiveRealWeightedBall ellM ellX R hellM_pos hell).card : ℝ) := by
      exact_mod_cast hrank_nat
    exact hrank_cast.trans
      (card_generalBidegreePositiveRealWeightedBall_cast_le_triangularArea
        ellM ellX R hellM_pos hell hR)
  · exact generalBidegreeCoefficientEvaluationRank_positiveRealWeightedBall_cast_le_shellArea
      A B ellM ellX R hellM_pos hell hR

end PellPaper
