import Pell.Main3ComplexRatioFanDecay
import Pell.TwoLayerFanDeterminantStrictness
import Pell.IntegralDeterminantVanishing

/-!
# Complex-place vanishing of selected main3 integral minors

This module restores the radial row factors and the exact discriminant
division around the complex normalized-ratio determinant.  A single explicit
logarithmic cost hypothesis then combines with the complex two-layer fan
bound to force a selected integral bidegree-`(1,B)` minor to vanish.

The final theorem is local to one complex square-map cell.  It deliberately
leaves the project-specific radial/discriminant cost estimate and its
numerical rate inequality as visible hypotheses.  No fibre count or common
auxiliary form is asserted.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

local instance main3ComplexEmbeddingMinorVanishing_numberField
    (a : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

/-- The exact positive multiplier left after restoring all selected radial
row factors and dividing by the fixed embedding-basis discriminant factor. -/
def main3ComplexSelectedRadialDiscriminantCostFactor
    {ι : Type*} {a : ℤ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (B : ℕ) (F : ShiftedSquareFixedExplicitIntegralBasisData a)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ)
    (points : ι → GeneralBidegreeFormPoint)
    (s : generalBidegreeFormIndex 1 B ↪ ι) : ℝ :=
  (∏ r : generalBidegreeFormIndex 1 B,
      ‖main3EmbeddingRadialRowFactor B
        (sigma F.omega) (sigma (star F.omega)) (points (s r))‖) /
    Real.rpow
      |(NumberField.discr (rationalQuadraticAlgebra (-a)) : ℝ)|
      (((((B + 1) ^ 2 : ℕ) : ℝ)) / 2)

/-- The radial/discriminant cost factor is nonnegative. -/
theorem main3ComplexSelectedRadialDiscriminantCostFactor_nonneg
    {ι : Type*} {a : ℤ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (B : ℕ) (F : ShiftedSquareFixedExplicitIntegralBasisData a)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ)
    (points : ι → GeneralBidegreeFormPoint)
    (s : generalBidegreeFormIndex 1 B ↪ ι) :
    0 ≤ main3ComplexSelectedRadialDiscriminantCostFactor
      B F sigma points s := by
  unfold main3ComplexSelectedRadialDiscriminantCostFactor
  exact div_nonneg (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    (main3ShiftedSquare_discriminantRpowFactor_pos B).le

/-- Exact absolute-value factorization of a selected integral minor into
the radial/discriminant cost and the normalized ratio determinant. -/
theorem abs_cast_det_generalBidegreeMinor_eq_radialDiscriminantCost_mul_norm_ratioPower
    {ι : Type*} [Fintype ι]
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (B : ℕ) (F : ShiftedSquareFixedExplicitIntegralBasisData a)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ)
    (points : ι → GeneralBidegreeFormPoint)
    (s : generalBidegreeFormIndex 1 B ↪ ι)
    (hsourceDen : ∀ r,
      ((points r).1.1 : ℂ) + sigma (star F.omega) * ((points r).1.2 : ℂ) ≠ 0)
    (htargetDen : ∀ r,
      ((points r).2.1 : ℂ) + sigma F.omega * ((points r).2.2 : ℂ) ≠ 0) :
    |(((generalBidegreeFormEvaluationMatrix
        1 B points).submatrix s id).det : ℝ)| =
      main3ComplexSelectedRadialDiscriminantCostFactor B F sigma points s *
        ‖((main3RatioPowerEvaluationMatrix B
          (sigma F.omega) (sigma (star F.omega)) points).submatrix s id).det‖ := by
  rw [
    abs_cast_det_generalBidegreeMinor_eq_norm_reflectedEmbeddingBasis_det_div_discrRpow
      B F sigma points s]
  change
    ‖((main3ReflectedEmbeddingBasisEvaluationMatrix B
      (sigma F.omega) (sigma (star F.omega)) points).submatrix s id).det‖ /
        Real.rpow
          |(NumberField.discr (rationalQuadraticAlgebra (-a)) : ℝ)|
          (((((B + 1) ^ 2 : ℕ) : ℝ)) / 2) = _
  rw [
    norm_det_main3ReflectedEmbeddingBasisEvaluationMatrix_selected_eq_prod_norm_radial_mul_norm_det_ratioPower
      B (sigma F.omega) (sigma (star F.omega)) points s
        hsourceDen htargetDen]
  unfold main3ComplexSelectedRadialDiscriminantCostFactor
  ring

/-- A logarithmic bound for the radial/discriminant multiplier and the exact
complex fan rate force the selected integral minor below one. -/
theorem abs_cast_det_generalBidegreeMinor_lt_one_of_mem_complexSquareMapCell_rate
    {ι : Type*} [Fintype ι]
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {M : ℕ} (hM : 10 ≤ M)
    {i : ComplexUnitCircleSlopeCellIndex}
    (hi : i ∈ complexUnitCircleSlopeCellIndices M)
    (B k : ℕ) (F : ShiftedSquareFixedExplicitIntegralBasisData a)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ)
    (centre : ℂ)
    (points : ι → GeneralBidegreeFormPoint)
    (s : generalBidegreeFormIndex 1 B ↪ ι)
    (hsourceDen : ∀ r,
      ((points r).1.1 : ℂ) + sigma (star F.omega) * ((points r).1.2 : ℂ) ≠ 0)
    (htargetDen : ∀ r,
      ((points r).2.1 : ℂ) + sigma F.omega * ((points r).2.2 : ℂ) ≠ 0)
    (hcell : ∀ r, InComplexUnitCircleSquareMapCellPair M i
      (main3EmbeddingSourceRatio
          (sigma F.omega) (sigma (star F.omega)) (points r),
        main3EmbeddingTargetRatio
          (sigma F.omega) (sigma (star F.omega)) (points r)))
    (hcentre : InComplexUnitCircleSlopeCell M i centre)
    (epsilon : ι → ℝ)
    (herror : ∀ r,
      ‖main3EmbeddingTargetRatio
          (sigma F.omega) (sigma (star F.omega)) (points r) -
        main3EmbeddingSourceRatio
          (sigma F.omega) (sigma (star F.omega)) (points r) ^ 2‖ ≤ epsilon r)
    (hepsilonMesh : ∀ r, epsilon r ≤ 1 / (M : ℝ))
    (ellM ellX : ℝ)
    (hsourceScale : 3 / (M : ℝ) ≤ Real.exp (-ellM))
    (hdefectScale : ∀ r, (3 / 2) * epsilon r ≤ Real.exp (-ellX))
    (hellM : 0 < ellM)
    (hkpos : 1 ≤ k) (hkB : k ≤ B)
    (hfanLower : (2 * (k : ℝ) - 1) * ellM ≤ ellX)
    (hfanUpper : ellX ≤ (2 * (k : ℝ) + 1) * ellM)
    (cost : ℝ)
    (hcost : main3ComplexSelectedRadialDiscriminantCostFactor
      B F sigma points s ≤ Real.exp cost)
    (hrate : cost +
        Real.log (Nat.factorial
          (Fintype.card (generalBidegreeGrid 1 B)) : ℝ) +
        twoLayerFanTaylorTail B *
          (Fintype.card (generalBidegreeGrid 1 B) : ℝ) <
      twoLayerWeight B k ellM ellX) :
    |(((generalBidegreeFormEvaluationMatrix
        1 B points).submatrix s id).det : ℝ)| < 1 := by
  let z := main3ComplexSelectedRadialDiscriminantCostFactor
    B F sigma points s
  let d := ‖((main3RatioPowerEvaluationMatrix B
    (sigma F.omega) (sigma (star F.omega)) points).submatrix s id).det‖
  have hz0 : 0 ≤ z :=
    main3ComplexSelectedRadialDiscriminantCostFactor_nonneg
      B F sigma points s
  have hd0 : 0 ≤ d := norm_nonneg _
  have hratio : d ≤
      (Nat.factorial (Fintype.card (generalBidegreeGrid 1 B)) : ℝ) *
        Real.exp (-twoLayerWeight B k ellM ellX) *
          (Real.exp (twoLayerFanTaylorTail B)) ^
            Fintype.card (generalBidegreeGrid 1 B) := by
    simpa only [d, twoLayerFanTaylorTail] using
      norm_det_main3RatioPowerEvaluationMatrix_selected_le_of_mem_complexSquareMapCell
        hM hi B k (sigma F.omega) (sigma (star F.omega)) centre
          points s hcell hcentre epsilon herror hepsilonMesh ellM ellX
          hsourceScale hdefectScale hellM hkpos hkB hfanLower hfanUpper
  have hsmall : |z * d| < 1 :=
    abs_mul_lt_one_of_exp_cost_and_factorial_exp_decay
      (n := generalBidegreeGrid 1 B)
      cost (twoLayerWeight B k ellM ellX) (twoLayerFanTaylorTail B)
      z d (by simpa only [abs_of_nonneg hz0, z] using hcost)
      (by simpa only [abs_of_nonneg hd0] using hratio) hrate
  rw [
    abs_cast_det_generalBidegreeMinor_eq_radialDiscriminantCost_mul_norm_ratioPower
      B F sigma points s hsourceDen htargetDen]
  simpa only [z, d, abs_of_nonneg (mul_nonneg hz0 hd0)] using hsmall

/-- The preceding strict bound gives literal vanishing of the selected
integral bidegree-`(1,B)` minor. -/
theorem generalBidegreeMinor_det_eq_zero_of_mem_complexSquareMapCell_rate
    {ι : Type*} [Fintype ι]
    {a : ℤ} [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {M : ℕ} (hM : 10 ≤ M)
    {i : ComplexUnitCircleSlopeCellIndex}
    (hi : i ∈ complexUnitCircleSlopeCellIndices M)
    (B k : ℕ) (F : ShiftedSquareFixedExplicitIntegralBasisData a)
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ)
    (centre : ℂ)
    (points : ι → GeneralBidegreeFormPoint)
    (s : generalBidegreeFormIndex 1 B ↪ ι)
    (hsourceDen : ∀ r,
      ((points r).1.1 : ℂ) + sigma (star F.omega) * ((points r).1.2 : ℂ) ≠ 0)
    (htargetDen : ∀ r,
      ((points r).2.1 : ℂ) + sigma F.omega * ((points r).2.2 : ℂ) ≠ 0)
    (hcell : ∀ r, InComplexUnitCircleSquareMapCellPair M i
      (main3EmbeddingSourceRatio
          (sigma F.omega) (sigma (star F.omega)) (points r),
        main3EmbeddingTargetRatio
          (sigma F.omega) (sigma (star F.omega)) (points r)))
    (hcentre : InComplexUnitCircleSlopeCell M i centre)
    (epsilon : ι → ℝ)
    (herror : ∀ r,
      ‖main3EmbeddingTargetRatio
          (sigma F.omega) (sigma (star F.omega)) (points r) -
        main3EmbeddingSourceRatio
          (sigma F.omega) (sigma (star F.omega)) (points r) ^ 2‖ ≤ epsilon r)
    (hepsilonMesh : ∀ r, epsilon r ≤ 1 / (M : ℝ))
    (ellM ellX : ℝ)
    (hsourceScale : 3 / (M : ℝ) ≤ Real.exp (-ellM))
    (hdefectScale : ∀ r, (3 / 2) * epsilon r ≤ Real.exp (-ellX))
    (hellM : 0 < ellM)
    (hkpos : 1 ≤ k) (hkB : k ≤ B)
    (hfanLower : (2 * (k : ℝ) - 1) * ellM ≤ ellX)
    (hfanUpper : ellX ≤ (2 * (k : ℝ) + 1) * ellM)
    (cost : ℝ)
    (hcost : main3ComplexSelectedRadialDiscriminantCostFactor
      B F sigma points s ≤ Real.exp cost)
    (hrate : cost +
        Real.log (Nat.factorial
          (Fintype.card (generalBidegreeGrid 1 B)) : ℝ) +
        twoLayerFanTaylorTail B *
          (Fintype.card (generalBidegreeGrid 1 B) : ℝ) <
      twoLayerWeight B k ellM ellX) :
    ((generalBidegreeFormEvaluationMatrix
      1 B points).submatrix s id).det = 0 := by
  exact integral_det_eq_zero_of_abs_cast_lt_one _
    (abs_cast_det_generalBidegreeMinor_lt_one_of_mem_complexSquareMapCell_rate
      hM hi B k F sigma centre points s hsourceDen htargetDen hcell hcentre
      epsilon herror hepsilonMesh ellM ellX hsourceScale hdefectScale
      hellM hkpos hkB hfanLower hfanUpper cost hcost hrate)

end

end PellPaper
