import Pell.ShiftedSquareQuadraticEmbeddingLower
import Mathlib.Tactic

/-!
# Target embedding bounds from the shifted-square factorization

This isolated candidate transfers pointwise bounds for the normalized element
`zeta` to the primitive target element.  The input zeta inequalities are kept
as hypotheses so that this module does not depend on the separately reviewed
zeta-bounds candidate.
-/

namespace PellPaper

noncomputable section

local instance shiftedSquareTargetEmbeddingBounds_numberField (a : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

/-- Applying an infinite-place absolute value to the exact integral
factorization preserves all factors, including the rational factor `C₀²`. -/
theorem shiftedSquare_factorization_infinitePlace
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq)
    (v : NumberField.InfinitePlace (rationalQuadraticAlgebra (-a))) :
    v P.minkowski.mu ^ 2 * v P.minkowski.nu =
      (P.minkowski.C₀ : ℝ) ^ 2 * v (shiftedSquareZeta a d n) := by
  have hC₀ :
      v (((P.minkowski.C₀ : ℕ) :
          NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))) :
          rationalQuadraticAlgebra (-a)) =
        (P.minkowski.C₀ : ℝ) := by
    (convert NumberField.InfinitePlace.map_natCast v P.minkowski.C₀ using 1;
      norm_num)
  have h := congrArg
    (fun z : NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a)) =>
      v (z : rationalQuadraticAlgebra (-a)))
    P.minkowski.factorization
  simpa only [map_mul, map_pow, coe_shiftedSquareZetaInteger,
    NumberField.InfinitePlace.map_natCast,
    ← NumberField.RingOfIntegers.coe_eq_algebraMap, hC₀] using h

/-- The infinite-place factorization after removing the positive target
coordinate content `ell`. -/
theorem shiftedSquare_primitiveTarget_factorization_infinitePlace
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq)
    (v : NumberField.InfinitePlace (rationalQuadraticAlgebra (-a))) :
    v P.minkowski.mu ^ 2 *
        ((P.ell : ℝ) *
          v (shiftedSquareIntegralBasisElement P.basis P.y)) =
      (P.minkowski.C₀ : ℝ) ^ 2 * v (shiftedSquareZeta a d n) := by
  have hell :
      v (((P.ell : ℤ) :
          NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))) :
          rationalQuadraticAlgebra (-a)) =
        (P.ell : ℝ) := by
    (convert NumberField.InfinitePlace.map_natCast v P.ell using 1;
      norm_num)
  have h := shiftedSquare_factorization_infinitePlace P v
  rw [P.nu_coordinates] at h
  simpa only [zsmul_eq_mul, map_mul,
    NumberField.InfinitePlace.map_intCast, Int.norm_natCast,
    ← NumberField.RingOfIntegers.coe_eq_algebraMap, hell] using h

/-- A lower zeta bound and the simultaneous upper source box give a lower
bound for the primitive target embedding. -/
theorem shiftedSquare_targetEmbedding_lower_of_zeta_lower
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (hd : 0 < d)
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq)
    (v : NumberField.InfinitePlace (rationalQuadraticAlgebra (-a)))
    (hζlower : (n : ℝ) / 4 ≤ v (shiftedSquareZeta a d n)) :
    ((P.minkowski.C₀ : ℝ) ^ 2 * ((n : ℝ) / 4)) /
          ((8 * Real.sqrt
            ((shiftedSquareD₀ d : ℝ) * Real.sqrt |a|)) ^ 2 * P.ell) ≤
      v (shiftedSquareIntegralBasisElement P.basis P.y) := by
  let R : ℝ := 8 * Real.sqrt
    ((shiftedSquareD₀ d : ℝ) * Real.sqrt |a|)
  let γ := shiftedSquareIntegralBasisElement P.basis P.y
  have hR : 0 < R := shiftedSquareEmbeddingAbsRadius_pos a d hd
  have hell : (0 : ℝ) < P.ell := by exact_mod_cast P.ell_pos
  have hγnonneg : 0 ≤
      v (γ : rationalQuadraticAlgebra (-a)) :=
    apply_nonneg v (γ : rationalQuadraticAlgebra (-a))
  have hmu : v P.minkowski.mu ≤ R := (P.minkowski.embedding_lt_abs v).le
  have hmuSq : v P.minkowski.mu ^ 2 ≤ R ^ 2 := by
    exact pow_le_pow_left₀ (apply_nonneg v _) hmu 2
  have hfactor := shiftedSquare_primitiveTarget_factorization_infinitePlace P v
  have hcross :
      (P.minkowski.C₀ : ℝ) ^ 2 * ((n : ℝ) / 4) ≤
        R ^ 2 * ((P.ell : ℝ) * v γ) := by
    calc
      (P.minkowski.C₀ : ℝ) ^ 2 * ((n : ℝ) / 4) ≤
          (P.minkowski.C₀ : ℝ) ^ 2 *
            v (shiftedSquareZeta a d n) := by
        gcongr
      _ = v P.minkowski.mu ^ 2 * ((P.ell : ℝ) * v γ) :=
        hfactor.symm
      _ ≤ R ^ 2 * ((P.ell : ℝ) * v γ) := by
        exact mul_le_mul_of_nonneg_right hmuSq (mul_nonneg hell.le hγnonneg)
  apply (div_le_iff₀ (mul_pos (sq_pos_of_pos hR) hell)).mpr
  simpa only [R, γ, mul_assoc, mul_comm, mul_left_comm] using hcross

/-- The product-formula lower source box and an upper zeta bound give an
upper bound for the primitive target embedding. -/
theorem shiftedSquare_targetEmbedding_upper_of_zeta_upper
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (hd : 0 < d)
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq)
    (v : NumberField.InfinitePlace (rationalQuadraticAlgebra (-a)))
    (hζupper : v (shiftedSquareZeta a d n) ≤ 2 * (n : ℝ)) :
    v (shiftedSquareIntegralBasisElement P.basis P.y) ≤
      ((P.minkowski.C₀ : ℝ) ^ 2 * (2 * (n : ℝ))) /
        (((((shiftedSquareD₀ d * P.minkowski.C₀ : ℕ) : ℝ) /
            (8 * Real.sqrt
              ((shiftedSquareD₀ d : ℝ) * Real.sqrt |a|))) ^ 2) * P.ell) := by
  let R : ℝ := 8 * Real.sqrt
    ((shiftedSquareD₀ d : ℝ) * Real.sqrt |a|)
  let L : ℝ :=
    ((shiftedSquareD₀ d * P.minkowski.C₀ : ℕ) : ℝ) / R
  let γ := shiftedSquareIntegralBasisElement P.basis P.y
  have hR : 0 < R := shiftedSquareEmbeddingAbsRadius_pos a d hd
  have hD₀ : 0 < shiftedSquareD₀ d := shiftedSquareD₀_pos hd
  have hC₀ : 0 < P.minkowski.C₀ := P.minkowski.C₀_pos
  have hL : 0 < L := by
    apply div_pos
    · exact_mod_cast Nat.mul_pos hD₀ hC₀
    · exact hR
  have hell : (0 : ℝ) < P.ell := by exact_mod_cast P.ell_pos
  have hγnonneg : 0 ≤
      v (γ : rationalQuadraticAlgebra (-a)) :=
    apply_nonneg v (γ : rationalQuadraticAlgebra (-a))
  have hmu : L ≤ v P.minkowski.mu := by
    simpa only [L, R] using
      shiftedSquare_mu_norm_div_radius_le_embedding hd P.minkowski v
  have hmuSq : L ^ 2 ≤ v P.minkowski.mu ^ 2 := by
    exact pow_le_pow_left₀ hL.le hmu 2
  have hfactor := shiftedSquare_primitiveTarget_factorization_infinitePlace P v
  have hcross : L ^ 2 * ((P.ell : ℝ) * v γ) ≤
      (P.minkowski.C₀ : ℝ) ^ 2 * (2 * (n : ℝ)) := by
    calc
      L ^ 2 * ((P.ell : ℝ) * v γ) ≤
          v P.minkowski.mu ^ 2 * ((P.ell : ℝ) * v γ) := by
        exact mul_le_mul_of_nonneg_right hmuSq (mul_nonneg hell.le hγnonneg)
      _ = (P.minkowski.C₀ : ℝ) ^ 2 *
          v (shiftedSquareZeta a d n) := hfactor
      _ ≤ (P.minkowski.C₀ : ℝ) ^ 2 * (2 * (n : ℝ)) := by
        gcongr
  apply (le_div_iff₀ (mul_pos (sq_pos_of_pos hL) hell)).mpr
  simpa only [L, R, γ, mul_assoc, mul_comm, mul_left_comm] using hcross

/-- Route-facing two-sided primitive target box, conditional only on the
pointwise zeta comparison supplied by the separate zeta-bounds module. -/
theorem shiftedSquare_targetEmbedding_twoSided_of_zeta_bounds
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (hd : 0 < d)
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq)
    (v : NumberField.InfinitePlace (rationalQuadraticAlgebra (-a)))
    (hζ : (n : ℝ) / 4 ≤ v (shiftedSquareZeta a d n) ∧
      v (shiftedSquareZeta a d n) ≤ 2 * (n : ℝ)) :
    ((P.minkowski.C₀ : ℝ) ^ 2 * ((n : ℝ) / 4)) /
          ((8 * Real.sqrt
            ((shiftedSquareD₀ d : ℝ) * Real.sqrt |a|)) ^ 2 * P.ell) ≤
        v (shiftedSquareIntegralBasisElement P.basis P.y) ∧
      v (shiftedSquareIntegralBasisElement P.basis P.y) ≤
        ((P.minkowski.C₀ : ℝ) ^ 2 * (2 * (n : ℝ))) /
          (((((shiftedSquareD₀ d * P.minkowski.C₀ : ℕ) : ℝ) /
              (8 * Real.sqrt
                ((shiftedSquareD₀ d : ℝ) * Real.sqrt |a|))) ^ 2) * P.ell) :=
  ⟨shiftedSquare_targetEmbedding_lower_of_zeta_lower hd P v hζ.1,
    shiftedSquare_targetEmbedding_upper_of_zeta_upper hd P v hζ.2⟩

end

end PellPaper
