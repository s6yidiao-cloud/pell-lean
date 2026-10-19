import Pell.GeneralBidegreeParallelRankBound
import Mathlib.Data.Real.Basic

/-!
# Ambient bounds for coefficient-evaluation rank

The weighted rank caps used by the determinant method are always ranks of a
linear map whose codomain is the finite function space on `generalBidegreeGrid`.
This small module records the resulting ambient-dimension bound once, so
finite-mesh arguments can use literal rank deficits without reopening the
linear-algebra definition.
-/

namespace PellPaper

noncomputable section

/-- Every coefficient-evaluation rank is bounded by the cardinality of the
finite sheared grid, independently of its monomial support. -/
theorem generalBidegreeCoefficientEvaluationRank_le_grid_card
    (A B : ℕ) (U : Finset generalBidegreeCoefficientMonomialIndex) :
    generalBidegreeCoefficientEvaluationRank A B U ≤
      Fintype.card (generalBidegreeGrid A B) := by
  unfold generalBidegreeCoefficientEvaluationRank
  calc
    Module.finrank ℚ (LinearMap.range
        ((generalBidegreeGridPolynomialEvaluationLinearMap A B).domRestrict
          (generalBidegreeCoefficientMonomialSpan U))) ≤
        Module.finrank ℚ (generalBidegreeGrid A B → ℚ) :=
      Submodule.finrank_le _
    _ = Fintype.card (generalBidegreeGrid A B) := Module.finrank_pi ℚ

/-- Real-valued form of the ambient finite-grid rank bound. -/
theorem generalBidegreeCoefficientEvaluationRank_cast_le_grid_card
    (A B : ℕ) (U : Finset generalBidegreeCoefficientMonomialIndex) :
    (Nat.cast (generalBidegreeCoefficientEvaluationRank A B U) : ℝ) ≤
      (Nat.cast (Fintype.card (generalBidegreeGrid A B)) : ℝ) := by
  exact_mod_cast generalBidegreeCoefficientEvaluationRank_le_grid_card A B U

end

end PellPaper
