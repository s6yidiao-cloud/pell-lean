import Pell.ShiftedSquareMinkowskiEmbeddingC0Nu
import Pell.ShiftedSquareSimultaneousNormalizedCoordinates
import Mathlib.Tactic

/-!
# A lower embedding bound from the quadratic product formula

In degree two, a simultaneous upper bound at all infinite places and the
exact absolute norm also give a lower bound at each place.  This is the
product-formula half of the two-sided coordinate estimate.
-/

namespace PellPaper

noncomputable section

open scoped BigOperators

local instance shiftedSquareQuadraticEmbeddingLower_numberField (a : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

/-- In a quadratic number field, if every infinite-place value is at most
`B > 0`, then every one is at least the absolute norm divided by `B`. -/
theorem quadratic_absNorm_div_le_infinitePlace_of_all_le
    (K : Type*) [Field K] [NumberField K]
    (hrank : Module.finrank ℚ K = 2)
    (z : K) (B : ℝ) (hB : 0 < B)
    (hplace : ∀ v : NumberField.InfinitePlace K, v z ≤ B) :
    ∀ v : NumberField.InfinitePlace K,
      ((|Algebra.norm ℚ z| : ℚ) : ℝ) / B ≤ v z := by
  classical
  intro v
  have hsum :
      ∑ u : NumberField.InfinitePlace K,
          NumberField.InfinitePlace.mult u = 2 := by
    rw [NumberField.InfinitePlace.sum_mult_eq, hrank]
  have herase :
      (∑ u ∈ (Finset.univ.erase v),
          NumberField.InfinitePlace.mult u) +
          NumberField.InfinitePlace.mult v = 2 := by
    calc
      (∑ u ∈ (Finset.univ.erase v),
          NumberField.InfinitePlace.mult u) +
          NumberField.InfinitePlace.mult v =
          ∑ u : NumberField.InfinitePlace K,
            NumberField.InfinitePlace.mult u := by
        rw [Finset.sum_erase_add _ _ (Finset.mem_univ v)]
      _ = 2 := hsum
  have hmult : NumberField.InfinitePlace.mult v = 1 ∨
      NumberField.InfinitePlace.mult v = 2 := by
    have hpos := NumberField.InfinitePlace.mult_pos (w := v)
    omega
  have hrest :
      ∏ u ∈ (Finset.univ.erase v),
          u z ^ NumberField.InfinitePlace.mult u ≤
        B ^ (∑ u ∈ (Finset.univ.erase v),
          NumberField.InfinitePlace.mult u) := by
    calc
      ∏ u ∈ (Finset.univ.erase v),
          u z ^ NumberField.InfinitePlace.mult u ≤
          ∏ u ∈ (Finset.univ.erase v),
            B ^ NumberField.InfinitePlace.mult u := by
        refine Finset.prod_le_prod (fun u _ => ?_) (fun u _ => ?_)
        · exact pow_nonneg (apply_nonneg u _) _
        · exact pow_le_pow_left₀
            (apply_nonneg u _) (hplace u) _
      _ = B ^ (∑ u ∈ (Finset.univ.erase v),
          NumberField.InfinitePlace.mult u) := by
        rw [Finset.prod_pow_eq_pow_sum]
  have hnormSplit :
      ((|Algebra.norm ℚ z| : ℚ) : ℝ) =
        v z ^ NumberField.InfinitePlace.mult v *
          ∏ u ∈ (Finset.univ.erase v),
            u z ^ NumberField.InfinitePlace.mult u := by
    rw [← NumberField.InfinitePlace.prod_eq_abs_norm]
    exact (Finset.mul_prod_erase
      (s := Finset.univ)
      (f := fun u : NumberField.InfinitePlace K =>
        u z ^ NumberField.InfinitePlace.mult u)
      (Finset.mem_univ v)).symm
  have hzNonneg : 0 ≤ v z := apply_nonneg v z
  rcases hmult with hmult | hmult
  · have heraseOne :
        ∑ u ∈ (Finset.univ.erase v),
          NumberField.InfinitePlace.mult u = 1 := by omega
    have hnormLe : ((|Algebra.norm ℚ z| : ℚ) : ℝ) ≤ v z * B := by
      rw [hnormSplit, hmult, pow_one]
      have hrest' := hrest
      rw [heraseOne, pow_one] at hrest'
      exact mul_le_mul_of_nonneg_left hrest' hzNonneg
    exact (div_le_iff₀ hB).mpr hnormLe
  · have heraseZero :
        ∑ u ∈ (Finset.univ.erase v),
          NumberField.InfinitePlace.mult u = 0 := by omega
    have hnormLe : ((|Algebra.norm ℚ z| : ℚ) : ℝ) ≤ v z ^ 2 := by
      rw [hnormSplit, hmult]
      have hrest' := hrest
      rw [heraseZero, pow_zero] at hrest'
      simpa using mul_le_mul_of_nonneg_left hrest' (pow_nonneg hzNonneg 2)
    apply (div_le_iff₀ hB).mpr
    calc
      ((|Algebra.norm ℚ z| : ℚ) : ℝ) ≤ v z ^ 2 := hnormLe
      _ ≤ v z * B := by
        rw [pow_two]
        exact mul_le_mul_of_nonneg_left (hplace v) hzNonneg

/-- The absolute-shift radius used by the simultaneous package is positive
when the original source variable is positive. -/
theorem shiftedSquareEmbeddingAbsRadius_pos
    (a : ℤ) (d : ℕ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (hd : 0 < d) :
    0 < 8 * Real.sqrt
      ((shiftedSquareD₀ d : ℝ) * Real.sqrt |a|) := by
  have hnegA : -a ≠ 0 := by
    intro hnegA0
    have hnoRoot :=
      Fact.out (p := rationalQuadraticAlgebraNoRationalRoot (-a)) 0
    apply hnoRoot
    simp [hnegA0]
  have ha0 : a ≠ 0 := neg_ne_zero.mp hnegA
  have haAbs : (0 : ℝ) < (|a| : ℤ) := by
    exact_mod_cast (abs_pos.mpr ha0)
  have hd₀ : (0 : ℝ) < shiftedSquareD₀ d := by
    exact_mod_cast shiftedSquareD₀_pos hd
  have hsqrtA : 0 < Real.sqrt (|a| : ℤ) := Real.sqrt_pos.2 haAbs
  positivity

/-- The same-element package has a pointwise lower embedding bound obtained
from its exact norm and simultaneous upper box. -/
theorem shiftedSquare_mu_norm_div_radius_le_embedding
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (hd : 0 < d) (M : ShiftedSquareMinkowskiEmbeddingC₀NuPackage heq)
    (v : NumberField.InfinitePlace (rationalQuadraticAlgebra (-a))) :
    ((shiftedSquareD₀ d * M.C₀ : ℕ) : ℝ) /
        (8 * Real.sqrt
          ((shiftedSquareD₀ d : ℝ) * Real.sqrt |a|)) ≤
      v M.mu := by
  have hrank : Module.finrank ℚ (rationalQuadraticAlgebra (-a)) = 2 := by
    exact QuadraticAlgebra.finrank_eq_two ((-a : ℤ) : ℚ) 0
  have h := quadratic_absNorm_div_le_infinitePlace_of_all_le
    (rationalQuadraticAlgebra (-a)) hrank
    (M.mu : rationalQuadraticAlgebra (-a))
    (8 * Real.sqrt
      ((shiftedSquareD₀ d : ℝ) * Real.sqrt |a|))
    (shiftedSquareEmbeddingAbsRadius_pos a d hd)
    (fun u => (M.embedding_lt_abs u).le) v
  rw [M.mu_norm] at h
  norm_num at h ⊢
  exact h

/-- Dividing the simultaneous upper bound by the positive source content
gives an upper bound for the primitive source element at every place. -/
theorem shiftedSquare_sourceEmbedding_lt_radius_div_content
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq)
    (v : NumberField.InfinitePlace (rationalQuadraticAlgebra (-a))) :
    v (shiftedSquareIntegralBasisElement P.basis P.x) <
      (8 * Real.sqrt
        ((shiftedSquareD₀ d : ℝ) * Real.sqrt |a|)) / P.r := by
  apply (lt_div_iff₀ (by exact_mod_cast P.r_pos : (0 : ℝ) < P.r)).mpr
  have h := P.minkowski.embedding_lt_abs v
  rw [P.mu_coordinates] at h
  simpa [zsmul_eq_mul, mul_comm] using h

/-- The product formula supplies the matching lower source-coordinate bound,
again for the very same element. -/
theorem shiftedSquare_sourceNorm_div_radius_content_le_embedding
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (hd : 0 < d)
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq)
    (v : NumberField.InfinitePlace (rationalQuadraticAlgebra (-a))) :
    (((shiftedSquareD₀ d * P.minkowski.C₀ : ℕ) : ℝ) /
        (8 * Real.sqrt
          ((shiftedSquareD₀ d : ℝ) * Real.sqrt |a|))) / P.r ≤
      v (shiftedSquareIntegralBasisElement P.basis P.x) := by
  have hr : (0 : ℝ) < P.r := by exact_mod_cast P.r_pos
  apply (div_le_iff₀ hr).mpr
  have h := shiftedSquare_mu_norm_div_radius_le_embedding hd P.minkowski v
  rw [P.mu_coordinates] at h
  simpa [zsmul_eq_mul, mul_comm, div_mul_cancel₀ _ hr.ne'] using h

/-- Route-facing two-sided source-coordinate box, before the later
polynomial simplification in the field parameter. -/
theorem shiftedSquare_sourceEmbedding_twoSided
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (hd : 0 < d)
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq)
    (v : NumberField.InfinitePlace (rationalQuadraticAlgebra (-a))) :
    (((shiftedSquareD₀ d * P.minkowski.C₀ : ℕ) : ℝ) /
        (8 * Real.sqrt
          ((shiftedSquareD₀ d : ℝ) * Real.sqrt |a|))) / P.r ≤
        v (shiftedSquareIntegralBasisElement P.basis P.x) ∧
      v (shiftedSquareIntegralBasisElement P.basis P.x) <
        (8 * Real.sqrt
          ((shiftedSquareD₀ d : ℝ) * Real.sqrt |a|)) / P.r :=
  ⟨shiftedSquare_sourceNorm_div_radius_content_le_embedding hd P v,
    shiftedSquare_sourceEmbedding_lt_radius_div_content P v⟩

end

end PellPaper
