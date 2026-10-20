import Pell.TwoLayerFanMinimum
import Pell.GeneralBidegreeRectangularTaylorDecay

/-!
# Exact determinant decay in the two-layer fan

This module composes the exact minimum-weight theorem for
`generalBidegreeGrid 1 B` with the rectangular Taylor Cauchy--Binet bound.
The resulting estimate has the manuscript's exact exponent
`twoLayerWeight B k ellM ellX`; its factorial and Taylor-tail factors are
left unchanged.  Uniformity in the Taylor cutoff then gives the literal
exponential determinant bound, including its source-row reindexed form.
-/

namespace PellPaper

open scoped BigOperators

/-- The real coefficient minor occurring in rectangular Cauchy--Binet has
total logarithmic weight at least the exact two-layer fan weight. -/
theorem twoLayerWeight_le_totalWeight_of_real_rectangularCoefficientMinor_ne_zero
    (B k N : ℕ) (ellM ellX : ℝ)
    (hellM : 0 < ellM)
    (hkpos : 1 ≤ k) (hkB : k ≤ B)
    (hfanLower : (2 * (k : ℝ) - 1) * ellM ≤ ellX)
    (hfanUpper : ellX ≤ (2 * (k : ℝ) + 1) * ellM)
    (p : {p : generalBidegreeGrid 1 B → Fin N × Fin N //
      Function.Injective p})
    (hreal :
      ((generalBidegreeRectangularCoefficientMatrixReal 1 B
        (generalBidegreeRectangularTaylorSupport N)).submatrix id p.1).det ≠ 0) :
    twoLayerWeight B k ellM ellX ≤
      ∑ i, generalBidegreeRealWeight ellM ellX
        (generalBidegreeRectangularTaylorSupport N (p.1 i)) := by
  apply twoLayerWeight_le_sum_realWeight_of_selectedCoefficientMinor_ne_zero
    B k ellM ellX hellM hkpos hkB hfanLower hfanUpper
    (generalBidegreeRectangularTaylorSupport N ∘ p.1)
  exact
    generalBidegreeSelectedCoefficientEvaluationMatrix_det_ne_zero_of_real_submatrix_det_ne_zero
      1 B (generalBidegreeRectangularTaylorSupport N) p.1 hreal

/-- A finite `A = 1` rectangular Taylor determinant has exact two-layer fan
decay.  The factorial and exponential Taylor-tail constants are precisely
those of the generic rectangular estimate. -/
theorem abs_det_generalBidegreeRectangularTaylorEvaluationMatrix_le_twoLayerFan_exp_tail
    (B k N : ℕ) (α β : generalBidegreeGrid 1 B → ℝ)
    (u v ellM ellX : ℝ)
    (hellM : 0 < ellM)
    (hkpos : 1 ≤ k) (hkB : k ≤ B)
    (hfanLower : (2 * (k : ℝ) - 1) * ellM ≤ ellX)
    (hfanUpper : ellX ≤ (2 * (k : ℝ) + 1) * ellM)
    (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hcoords : ∀ r : generalBidegreeGrid 1 B,
      |(r.1.1 : ℝ)| ≤ u ∧ |(r.1.2 : ℝ)| ≤ v)
    (hα : ∀ r, |α r| ≤ Real.exp (-ellM))
    (hβ : ∀ r, |β r| ≤ Real.exp (-ellX)) :
    |(generalBidegreeRectangularTaylorEvaluationMatrix 1 B α β N).det| ≤
      (Nat.factorial (Fintype.card (generalBidegreeGrid 1 B)) : ℝ) *
        Real.exp (-twoLayerWeight B k ellM ellX) *
          (Real.exp (u + v)) ^ Fintype.card (generalBidegreeGrid 1 B) := by
  apply
    abs_det_generalBidegreeRectangularTaylorEvaluationMatrix_le_factorial_mul_exp_neg_minWeight_mul_exp_tail
      1 B N α β u v ellM ellX (twoLayerWeight B k ellM ellX)
      hu hv hcoords ?_ hα hβ
  intro p hp
  exact
    twoLayerWeight_le_totalWeight_of_real_rectangularCoefficientMinor_ne_zero
      B k N ellM ellX hellM hkpos hkB hfanLower hfanUpper p hp

/-- The exact finite two-layer fan estimate survives the rectangular Taylor
limit and bounds the literal exponential evaluation determinant. -/
theorem abs_det_generalBidegreeExponentialEvaluationMatrix_le_twoLayerFan_exp_tail
    (B k : ℕ) (α β : generalBidegreeGrid 1 B → ℝ)
    (u v ellM ellX : ℝ)
    (hellM : 0 < ellM)
    (hkpos : 1 ≤ k) (hkB : k ≤ B)
    (hfanLower : (2 * (k : ℝ) - 1) * ellM ≤ ellX)
    (hfanUpper : ellX ≤ (2 * (k : ℝ) + 1) * ellM)
    (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hcoords : ∀ r : generalBidegreeGrid 1 B,
      |(r.1.1 : ℝ)| ≤ u ∧ |(r.1.2 : ℝ)| ≤ v)
    (hα : ∀ r, |α r| ≤ Real.exp (-ellM))
    (hβ : ∀ r, |β r| ≤ Real.exp (-ellX)) :
    |(generalBidegreeExponentialEvaluationMatrix 1 B α β).det| ≤
      (Nat.factorial (Fintype.card (generalBidegreeGrid 1 B)) : ℝ) *
        Real.exp (-twoLayerWeight B k ellM ellX) *
          (Real.exp (u + v)) ^ Fintype.card (generalBidegreeGrid 1 B) := by
  apply le_of_tendsto'
    (tendsto_det_generalBidegreeRectangularTaylorEvaluationMatrix 1 B α β).abs
  intro N
  exact
    abs_det_generalBidegreeRectangularTaylorEvaluationMatrix_le_twoLayerFan_exp_tail
      B k N α β u v ellM ellX hellM hkpos hkB hfanLower hfanUpper
      hu hv hcoords hα hβ

/-- The exact two-layer fan estimate with the intrinsic coordinate bounds of
`generalBidegreeGrid 1 B` substituted. -/
theorem abs_det_generalBidegreeExponentialEvaluationMatrix_le_twoLayerFan_exp_tail_gridBounds
    (B k : ℕ) (α β : generalBidegreeGrid 1 B → ℝ)
    (ellM ellX : ℝ)
    (hellM : 0 < ellM)
    (hkpos : 1 ≤ k) (hkB : k ≤ B)
    (hfanLower : (2 * (k : ℝ) - 1) * ellM ≤ ellX)
    (hfanUpper : ellX ≤ (2 * (k : ℝ) + 1) * ellM)
    (hα : ∀ r, |α r| ≤ Real.exp (-ellM))
    (hβ : ∀ r, |β r| ≤ Real.exp (-ellX)) :
    |(generalBidegreeExponentialEvaluationMatrix 1 B α β).det| ≤
      (Nat.factorial (Fintype.card (generalBidegreeGrid 1 B)) : ℝ) *
        Real.exp (-twoLayerWeight B k ellM ellX) *
          (Real.exp (((1 + 2 * B : ℕ) : ℝ) + (B : ℝ))) ^
            Fintype.card (generalBidegreeGrid 1 B) := by
  apply abs_det_generalBidegreeExponentialEvaluationMatrix_le_twoLayerFan_exp_tail
    B k α β ((1 + 2 * B : ℕ) : ℝ) (B : ℝ) ellM ellX
    hellM hkpos hkB hfanLower hfanUpper (by positivity) (by positivity)
    (generalBidegreeGrid_coordinate_abs_bounds 1 B) hα hβ

/-- Source-side exact fan determinant decay after the natural row and column
reindexings.  This is an upper bound only; it assumes no determinant
nonvanishing and introduces no mesh or area-envelope correction. -/
theorem abs_det_reindex_shearedExponentialEvaluationMatrix_le_twoLayerFan_exp_tail
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B k : ℕ) (eRows : ι ≃ generalBidegreeGrid 1 B)
    (S T : ι → ℝ) (ellM ellX : ℝ)
    (hellM : 0 < ellM)
    (hkpos : 1 ≤ k) (hkB : k ≤ B)
    (hfanLower : (2 * (k : ℝ) - 1) * ellM ≤ ellX)
    (hfanUpper : ellX ≤ (2 * (k : ℝ) + 1) * ellM)
    (hα : ∀ r,
      |generalBidegreeReindexedLogS 1 B eRows S r| ≤ Real.exp (-ellM))
    (hβ : ∀ r,
      |generalBidegreeReindexedShearedLogT 1 B eRows S T r| ≤
        Real.exp (-ellX)) :
    |(Matrix.reindex eRows (generalBidegreeGridPointEquiv 1 B)
      (shearedExponentialEvaluationMatrix 1 B S T)).det| ≤
      (Nat.factorial (Fintype.card (generalBidegreeGrid 1 B)) : ℝ) *
        Real.exp (-twoLayerWeight B k ellM ellX) *
          (Real.exp (((1 + 2 * B : ℕ) : ℝ) + (B : ℝ))) ^
            Fintype.card (generalBidegreeGrid 1 B) := by
  calc
    |(Matrix.reindex eRows (generalBidegreeGridPointEquiv 1 B)
        (shearedExponentialEvaluationMatrix 1 B S T)).det| =
        |(generalBidegreeShearedExponentialEvaluationMatrix 1 B
          (generalBidegreeReindexedLogS 1 B eRows S)
          (generalBidegreeReindexedShearedLogT 1 B eRows S T)).det| := by
            rw [reindex_shearedExponentialEvaluationMatrix_eq_generalBidegreeSheared]
    _ = |(generalBidegreeExponentialEvaluationMatrix 1 B
        (generalBidegreeReindexedLogS 1 B eRows S)
        (generalBidegreeReindexedShearedLogT 1 B eRows S T)).det| := by
          rw [generalBidegreeExponentialEvaluationMatrix_eq_sheared]
    _ ≤ _ :=
      abs_det_generalBidegreeExponentialEvaluationMatrix_le_twoLayerFan_exp_tail_gridBounds
        B k (generalBidegreeReindexedLogS 1 B eRows S)
        (generalBidegreeReindexedShearedLogT 1 B eRows S T)
        ellM ellX hellM hkpos hkB hfanLower hfanUpper hα hβ

end PellPaper
