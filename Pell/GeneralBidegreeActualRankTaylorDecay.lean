import Pell.GeneralBidegreeActualRankWeightedFiltration
import Pell.GeneralBidegreeRectangularTaylorDecay

/-!
# Taylor determinant decay from literal positive-ball ranks

This is a conservative supplement to the continuous-envelope decay theorem.
It feeds the generic rectangular Taylor estimate with the exact
coefficient-evaluation rank at each mesh radius.  Consequently any sharper
low/high rank-cap calculation, including the shifted high branch, can provide
a lower bound for the displayed deficit sum without modifying the existing
sharp-area envelope or its Taylor-limit proof.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- The mesh-scaled literal positive-ball rank deficit for the full
`(A,B)` coefficient grid. -/
def generalBidegreeScaledActualPositiveBallRankDeficits
    (A B : ℕ) (ellM ellX mesh : ℝ)
    (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX) (Q : ℕ) : ℝ :=
  (∑ n ∈ Finset.range Q,
    (generalBidegreePositiveRealWeightedRankDeficit A B
      (Fintype.card (generalBidegreeGrid A B)) ellM ellX
      (((n + 1 : ℕ) : ℝ) * mesh) hellM_pos hell : ℝ)) * mesh

/-- A nonzero rectangular coefficient minor has total weight at least the
mesh sum of literal positive-ball rank deficits. -/
theorem scaledActualPositiveBallRankDeficits_le_totalWeight_of_real_rectangularCoefficientMinor_ne_zero
    (A B N : ℕ) (ellM ellX mesh : ℝ)
    (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX)
    (hmesh : 0 < mesh) (Q : ℕ)
    (p : {p : generalBidegreeGrid A B → Fin N × Fin N // Function.Injective p})
    (hreal :
      ((generalBidegreeRectangularCoefficientMatrixReal A B
        (generalBidegreeRectangularTaylorSupport N)).submatrix id p.1).det ≠ 0) :
    (∑ n ∈ Finset.range Q,
      (generalBidegreePositiveRealWeightedRankDeficit A B
        (Fintype.card (generalBidegreeGrid A B)) ellM ellX
        (((n + 1 : ℕ) : ℝ) * mesh) hellM_pos hell : ℝ)) * mesh ≤
      ∑ i, generalBidegreeRealWeight ellM ellX
        (generalBidegreeRectangularTaylorSupport N (p.1 i)) := by
  apply totalWeight_selectedCoefficientEvaluation_ge_scaledActualPositiveBallRankDeficits_of_det_ne_zero
    A B (generalBidegreeRectangularTaylorSupport N ∘ p.1)
    (fun i => generalBidegreeRealWeight ellM ellX
      (generalBidegreeRectangularTaylorSupport N (p.1 i)))
    ellM ellX mesh hellM_pos hell
  · intro i
    rfl
  · exact
      generalBidegreeSelectedCoefficientEvaluationMatrix_det_ne_zero_of_real_submatrix_det_ne_zero
        A B (generalBidegreeRectangularTaylorSupport N) p.1 hreal
  · exact hmesh

/-- A finite rectangular Taylor determinant decays by the literal mesh sum
of positive-ball rank deficits. -/
theorem abs_det_generalBidegreeRectangularTaylorEvaluationMatrix_le_actualPositiveBallRankDeficits_exp_tail
    (A B N : ℕ) (α β : generalBidegreeGrid A B → ℝ)
    (u v ellM ellX mesh : ℝ)
    (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX) (hmesh : 0 < mesh)
    (Q : ℕ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hcoords : ∀ r : generalBidegreeGrid A B,
      |(r.1.1 : ℝ)| ≤ u ∧ |(r.1.2 : ℝ)| ≤ v)
    (hα : ∀ r, |α r| ≤ Real.exp (-ellM))
    (hβ : ∀ r, |β r| ≤ Real.exp (-ellX)) :
    |(generalBidegreeRectangularTaylorEvaluationMatrix A B α β N).det| ≤
      (Nat.factorial (Fintype.card (generalBidegreeGrid A B)) : ℝ) *
        Real.exp (-((∑ n ∈ Finset.range Q,
          (generalBidegreePositiveRealWeightedRankDeficit A B
            (Fintype.card (generalBidegreeGrid A B)) ellM ellX
            (((n + 1 : ℕ) : ℝ) * mesh) hellM_pos hell : ℝ)) * mesh)) *
          (Real.exp (u + v)) ^ Fintype.card (generalBidegreeGrid A B) := by
  apply abs_det_generalBidegreeRectangularTaylorEvaluationMatrix_le_factorial_mul_exp_neg_minWeight_mul_exp_tail
    A B N α β u v ellM ellX
    ((∑ n ∈ Finset.range Q,
      (generalBidegreePositiveRealWeightedRankDeficit A B
        (Fintype.card (generalBidegreeGrid A B)) ellM ellX
        (((n + 1 : ℕ) : ℝ) * mesh) hellM_pos hell : ℝ)) * mesh)
    hu hv hcoords ?_ hα hβ
  intro p hp
  exact scaledActualPositiveBallRankDeficits_le_totalWeight_of_real_rectangularCoefficientMinor_ne_zero
    A B N ellM ellX mesh hellM_pos hell hmesh Q p hp

/-- The literal exponential determinant inherits the same actual-rank
deficit estimate from the uniform rectangular Taylor bounds. -/
theorem abs_det_generalBidegreeExponentialEvaluationMatrix_le_actualPositiveBallRankDeficits_exp_tail
    (A B : ℕ) (α β : generalBidegreeGrid A B → ℝ)
    (u v ellM ellX mesh : ℝ)
    (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX) (hmesh : 0 < mesh)
    (Q : ℕ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hcoords : ∀ r : generalBidegreeGrid A B,
      |(r.1.1 : ℝ)| ≤ u ∧ |(r.1.2 : ℝ)| ≤ v)
    (hα : ∀ r, |α r| ≤ Real.exp (-ellM))
    (hβ : ∀ r, |β r| ≤ Real.exp (-ellX)) :
    |(generalBidegreeExponentialEvaluationMatrix A B α β).det| ≤
      (Nat.factorial (Fintype.card (generalBidegreeGrid A B)) : ℝ) *
        Real.exp (-((∑ n ∈ Finset.range Q,
          (generalBidegreePositiveRealWeightedRankDeficit A B
            (Fintype.card (generalBidegreeGrid A B)) ellM ellX
            (((n + 1 : ℕ) : ℝ) * mesh) hellM_pos hell : ℝ)) * mesh)) *
          (Real.exp (u + v)) ^ Fintype.card (generalBidegreeGrid A B) := by
  apply le_of_tendsto'
    (tendsto_det_generalBidegreeRectangularTaylorEvaluationMatrix A B α β).abs
  intro N
  exact abs_det_generalBidegreeRectangularTaylorEvaluationMatrix_le_actualPositiveBallRankDeficits_exp_tail
    A B N α β u v ellM ellX mesh hellM_pos hell hmesh Q hu hv hcoords hα hβ

/-- The actual-rank exponential estimate with the intrinsic coordinate bounds
of the sheared coefficient grid substituted. -/
theorem abs_det_generalBidegreeExponentialEvaluationMatrix_le_actualPositiveBallRankDeficits_exp_tail_gridBounds
    (A B : ℕ) (α β : generalBidegreeGrid A B → ℝ)
    (ellM ellX mesh : ℝ)
    (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX) (hmesh : 0 < mesh)
    (Q : ℕ)
    (hα : ∀ r, |α r| ≤ Real.exp (-ellM))
    (hβ : ∀ r, |β r| ≤ Real.exp (-ellX)) :
    |(generalBidegreeExponentialEvaluationMatrix A B α β).det| ≤
      (Nat.factorial (Fintype.card (generalBidegreeGrid A B)) : ℝ) *
        Real.exp (-((∑ n ∈ Finset.range Q,
          (generalBidegreePositiveRealWeightedRankDeficit A B
            (Fintype.card (generalBidegreeGrid A B)) ellM ellX
            (((n + 1 : ℕ) : ℝ) * mesh) hellM_pos hell : ℝ)) * mesh)) *
          (Real.exp (((A + 2 * B : ℕ) : ℝ) + (B : ℝ))) ^
            Fintype.card (generalBidegreeGrid A B) := by
  apply abs_det_generalBidegreeExponentialEvaluationMatrix_le_actualPositiveBallRankDeficits_exp_tail
    A B α β ((A + 2 * B : ℕ) : ℝ) (B : ℝ) ellM ellX mesh
    hellM_pos hell hmesh Q (by positivity) (by positivity)
    (generalBidegreeGrid_coordinate_abs_bounds A B) hα hβ

/-- Source-side actual-rank determinant decay after the natural row and
column reindexings.  A source-normalized low/high cap may be compared directly
to this literal deficit sum. -/
theorem abs_det_reindex_shearedExponentialEvaluationMatrix_le_actualPositiveBallRankDeficits_exp_tail
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : ℕ) (eRows : ι ≃ generalBidegreeGrid A B)
    (S T : ι → ℝ) (ellM ellX mesh : ℝ)
    (hellM_pos : 0 < ellM) (hell : ellM ≤ ellX) (hmesh : 0 < mesh)
    (Q : ℕ)
    (hα : ∀ r,
      |generalBidegreeReindexedLogS A B eRows S r| ≤ Real.exp (-ellM))
    (hβ : ∀ r,
      |generalBidegreeReindexedShearedLogT A B eRows S T r| ≤ Real.exp (-ellX)) :
    |(Matrix.reindex eRows (generalBidegreeGridPointEquiv A B)
      (shearedExponentialEvaluationMatrix A B S T)).det| ≤
      (Nat.factorial (Fintype.card (generalBidegreeGrid A B)) : ℝ) *
        Real.exp (-((∑ n ∈ Finset.range Q,
          (generalBidegreePositiveRealWeightedRankDeficit A B
            (Fintype.card (generalBidegreeGrid A B)) ellM ellX
            (((n + 1 : ℕ) : ℝ) * mesh) hellM_pos hell : ℝ)) * mesh)) *
          (Real.exp (((A + 2 * B : ℕ) : ℝ) + (B : ℝ))) ^
            Fintype.card (generalBidegreeGrid A B) := by
  calc
    |(Matrix.reindex eRows (generalBidegreeGridPointEquiv A B)
        (shearedExponentialEvaluationMatrix A B S T)).det| =
        |(generalBidegreeShearedExponentialEvaluationMatrix A B
          (generalBidegreeReindexedLogS A B eRows S)
          (generalBidegreeReindexedShearedLogT A B eRows S T)).det| := by
            rw [reindex_shearedExponentialEvaluationMatrix_eq_generalBidegreeSheared]
    _ = |(generalBidegreeExponentialEvaluationMatrix A B
        (generalBidegreeReindexedLogS A B eRows S)
        (generalBidegreeReindexedShearedLogT A B eRows S T)).det| := by
          rw [generalBidegreeExponentialEvaluationMatrix_eq_sheared]
    _ ≤ _ :=
      abs_det_generalBidegreeExponentialEvaluationMatrix_le_actualPositiveBallRankDeficits_exp_tail_gridBounds
        A B (generalBidegreeReindexedLogS A B eRows S)
        (generalBidegreeReindexedShearedLogT A B eRows S T)
        ellM ellX mesh hellM_pos hell hmesh Q hα hβ

end

end PellPaper
