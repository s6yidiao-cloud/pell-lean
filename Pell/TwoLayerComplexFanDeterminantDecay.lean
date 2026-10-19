import Pell.GeneralBidegreeComplexTaylorLimit
import Pell.TwoLayerFanMinimum
import Pell.GeneralBidegreeRectangularTaylorDecay

/-!
# Exact complex determinant decay in the two-layer fan

This is the complex-norm analogue of `TwoLayerFanDeterminantDecay`.  It
combines the rational selected-minor filtration with the finite complex
Taylor Cauchy--Binet estimate, controls the rectangular Taylor mass
uniformly in the cutoff, and passes to the limiting complex exponential
matrix.

No local logarithm, embedding-matrix alignment, radial estimate, integral
minor vanishing, or point count is asserted here.
-/

namespace PellPaper

open scoped BigOperators

/-- A nonzero complex rectangular coefficient minor forces the same rational
minor to be nonzero and hence has total weight at least the exact two-layer
fan weight. -/
theorem twoLayerWeight_le_totalWeight_of_complex_rectangularCoefficientMinor_ne_zero
    (B k N : ℕ) (ellM ellX : ℝ)
    (hellM : 0 < ellM)
    (hkpos : 1 ≤ k) (hkB : k ≤ B)
    (hfanLower : (2 * (k : ℝ) - 1) * ellM ≤ ellX)
    (hfanUpper : ellX ≤ (2 * (k : ℝ) + 1) * ellM)
    (p : {p : generalBidegreeGrid 1 B → Fin N × Fin N //
      Function.Injective p})
    (hcomplex :
      ((generalBidegreeRectangularCoefficientMatrixComplex 1 B
        (generalBidegreeRectangularTaylorSupport N)).submatrix id p.1).det ≠ 0) :
    twoLayerWeight B k ellM ellX ≤
      ∑ i, generalBidegreeRealWeight ellM ellX
        (generalBidegreeRectangularTaylorSupport N (p.1 i)) := by
  apply twoLayerWeight_le_sum_realWeight_of_selectedCoefficientMinor_ne_zero
    B k ellM ellX hellM hkpos hkB hfanLower hfanUpper
    (generalBidegreeRectangularTaylorSupport N ∘ p.1)
  exact
    generalBidegreeSelectedCoefficientEvaluationMatrix_det_ne_zero_of_complex
      1 B (generalBidegreeRectangularTaylorSupport N) p.1 hcomplex

/-- A finite complex `A = 1` rectangular Taylor determinant has exact
two-layer fan decay, with a Taylor-tail factor independent of the cutoff. -/
theorem norm_det_generalBidegreeRectangularTaylorEvaluationMatrixComplex_le_twoLayerFan_exp_tail
    (B k N : ℕ) (alpha delta : generalBidegreeGrid 1 B → ℂ)
    (u v ellM ellX : ℝ)
    (hellM : 0 < ellM)
    (hkpos : 1 ≤ k) (hkB : k ≤ B)
    (hfanLower : (2 * (k : ℝ) - 1) * ellM ≤ ellX)
    (hfanUpper : ellX ≤ (2 * (k : ℝ) + 1) * ellM)
    (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hcoords : ∀ r : generalBidegreeGrid 1 B,
      |(r.1.1 : ℝ)| ≤ u ∧ |(r.1.2 : ℝ)| ≤ v)
    (halpha : ∀ r, ‖alpha r‖ ≤ Real.exp (-ellM))
    (hdelta : ∀ r, ‖delta r‖ ≤ Real.exp (-ellX)) :
    ‖(generalBidegreeRectangularTaylorEvaluationMatrixComplex
      1 B alpha delta N).det‖ ≤
      (Nat.factorial (Fintype.card (generalBidegreeGrid 1 B)) : ℝ) *
        Real.exp (-twoLayerWeight B k ellM ellX) *
          (Real.exp (u + v)) ^ Fintype.card (generalBidegreeGrid 1 B) := by
  have hfinite :=
    norm_det_generalBidegreeFiniteTaylorEvaluationMatrixComplex_le_of_rationalMinorWeight
      1 B alpha delta (generalBidegreeRectangularTaylorSupport N)
      (fun q => u ^ q.1.1 * v ^ q.2.1) ellM ellX
      (twoLayerWeight B k ellM ellX)
      (fun q => mul_nonneg (pow_nonneg hu _) (pow_nonneg hv _))
      (fun r q =>
        abs_generalBidegreeRectangularCoefficientMatrixReal_rectangularTaylorSupport_le_pows
          1 B N u v hu hcoords r q)
      (fun p hp =>
        twoLayerWeight_le_sum_realWeight_of_selectedCoefficientMinor_ne_zero
          B k ellM ellX hellM hkpos hkB hfanLower hfanUpper
          (generalBidegreeRectangularTaylorSupport N ∘ p.1) hp)
      halpha hdelta
  rw [generalBidegreeFiniteTaylorEvaluationMatrixComplex_rectangularTaylorSupport]
    at hfinite
  simp only [generalBidegreeRectangularTaylorSupport_zero,
    generalBidegreeRectangularTaylorSupport_one] at hfinite
  calc
    ‖(generalBidegreeRectangularTaylorEvaluationMatrixComplex
        1 B alpha delta N).det‖ ≤
        (Nat.factorial (Fintype.card (generalBidegreeGrid 1 B)) : ℝ) *
          Real.exp (-twoLayerWeight B k ellM ellX) *
          (∑ q : Fin N × Fin N,
            (u ^ q.1.1 * v ^ q.2.1) *
              ((Nat.factorial q.1.1 : ℝ)⁻¹ *
                (Nat.factorial q.2.1 : ℝ)⁻¹)) ^
              Fintype.card (generalBidegreeGrid 1 B) := hfinite
    _ = (Nat.factorial (Fintype.card (generalBidegreeGrid 1 B)) : ℝ) *
          Real.exp (-twoLayerWeight B k ellM ellX) *
          (rectangularFactorialTaylorMass u v N) ^
            Fintype.card (generalBidegreeGrid 1 B) := by
      rw [sum_rectangularCoefficientScale_mul_invFactorials_eq_rectangularFactorialTaylorMass]
    _ ≤ (Nat.factorial (Fintype.card (generalBidegreeGrid 1 B)) : ℝ) *
          Real.exp (-twoLayerWeight B k ellM ellX) *
          (Real.exp (u + v)) ^ Fintype.card (generalBidegreeGrid 1 B) := by
      apply mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀
          (Finset.sum_nonneg fun q _ =>
            mul_nonneg (div_nonneg (pow_nonneg hu _) (by positivity))
              (div_nonneg (pow_nonneg hv _) (by positivity)))
          (rectangularFactorialTaylorMass_le_exp_add u v N hu hv) _)
      exact mul_nonneg (by positivity) (Real.exp_pos _).le

/-- The exact finite complex two-layer fan estimate survives the rectangular
Taylor limit and bounds the limiting complex exponential determinant. -/
theorem norm_det_generalBidegreeExponentialEvaluationMatrixComplex_le_twoLayerFan_exp_tail
    (B k : ℕ) (alpha delta : generalBidegreeGrid 1 B → ℂ)
    (u v ellM ellX : ℝ)
    (hellM : 0 < ellM)
    (hkpos : 1 ≤ k) (hkB : k ≤ B)
    (hfanLower : (2 * (k : ℝ) - 1) * ellM ≤ ellX)
    (hfanUpper : ellX ≤ (2 * (k : ℝ) + 1) * ellM)
    (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hcoords : ∀ r : generalBidegreeGrid 1 B,
      |(r.1.1 : ℝ)| ≤ u ∧ |(r.1.2 : ℝ)| ≤ v)
    (halpha : ∀ r, ‖alpha r‖ ≤ Real.exp (-ellM))
    (hdelta : ∀ r, ‖delta r‖ ≤ Real.exp (-ellX)) :
    ‖(generalBidegreeExponentialEvaluationMatrixComplex
      1 B alpha delta).det‖ ≤
      (Nat.factorial (Fintype.card (generalBidegreeGrid 1 B)) : ℝ) *
        Real.exp (-twoLayerWeight B k ellM ellX) *
          (Real.exp (u + v)) ^ Fintype.card (generalBidegreeGrid 1 B) := by
  apply le_of_tendsto'
    (tendsto_det_generalBidegreeRectangularTaylorEvaluationMatrixComplex
      1 B alpha delta).norm
  intro N
  exact
    norm_det_generalBidegreeRectangularTaylorEvaluationMatrixComplex_le_twoLayerFan_exp_tail
      B k N alpha delta u v ellM ellX hellM hkpos hkB hfanLower hfanUpper
      hu hv hcoords halpha hdelta

/-- The complex exponential determinant estimate with the intrinsic
coordinates of `generalBidegreeGrid 1 B` substituted. -/
theorem norm_det_generalBidegreeExponentialEvaluationMatrixComplex_le_twoLayerFan_exp_tail_gridBounds
    (B k : ℕ) (alpha delta : generalBidegreeGrid 1 B → ℂ)
    (ellM ellX : ℝ)
    (hellM : 0 < ellM)
    (hkpos : 1 ≤ k) (hkB : k ≤ B)
    (hfanLower : (2 * (k : ℝ) - 1) * ellM ≤ ellX)
    (hfanUpper : ellX ≤ (2 * (k : ℝ) + 1) * ellM)
    (halpha : ∀ r, ‖alpha r‖ ≤ Real.exp (-ellM))
    (hdelta : ∀ r, ‖delta r‖ ≤ Real.exp (-ellX)) :
    ‖(generalBidegreeExponentialEvaluationMatrixComplex
      1 B alpha delta).det‖ ≤
      (Nat.factorial (Fintype.card (generalBidegreeGrid 1 B)) : ℝ) *
        Real.exp (-twoLayerWeight B k ellM ellX) *
          (Real.exp (((1 + 2 * B : ℕ) : ℝ) + (B : ℝ))) ^
            Fintype.card (generalBidegreeGrid 1 B) := by
  apply
    norm_det_generalBidegreeExponentialEvaluationMatrixComplex_le_twoLayerFan_exp_tail
      B k alpha delta ((1 + 2 * B : ℕ) : ℝ) (B : ℝ)
        ellM ellX hellM hkpos hkB hfanLower hfanUpper
        (by positivity) (by positivity)
        (generalBidegreeGrid_coordinate_abs_bounds 1 B) halpha hdelta

end PellPaper
