import Pell.ShiftedSquareZetaEmbeddingBounds
import Mathlib.Tactic

/-!
# The local-ratio error for the main3 shifted-square map

The manuscript's local square-map relation contains the factor
`star zeta / zeta`.  This isolated candidate first computes
`zeta - star zeta` exactly, including the parity normalization, and then
controls its image under every complex embedding.  A denominator-free
relative estimate is followed by the literal quotient estimate used in
the manuscript.
-/

namespace PellPaper

noncomputable section

local instance main3ShiftedSquareZetaLocalRatioError_numberField (a : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

/-- The difference between the normalized quadratic element and its field
conjugate is exactly `(2/q₂) * omega`. -/
theorem shiftedSquareZeta_sub_star
    (a : ℤ) (d n : ℕ) :
    shiftedSquareZeta a d n - star (shiftedSquareZeta a d n) =
      ((2 : ℚ) / (shiftedSquareQ₂ d : ℚ)) •
        (QuadraticAlgebra.omega : rationalQuadraticAlgebra (-a)) := by
  rw [QuadraticAlgebra.sub_star, shiftedSquareZeta_im]
  apply QuadraticAlgebra.ext
  · simp only [QuadraticAlgebra.re_smul, QuadraticAlgebra.re_sub,
      QuadraticAlgebra.re_star, QuadraticAlgebra.omega_re,
      QuadraticAlgebra.omega_im]
    simp
  · simp only [QuadraticAlgebra.im_smul, QuadraticAlgebra.im_sub,
      QuadraticAlgebra.im_star, QuadraticAlgebra.omega_im]
    simp [div_eq_mul_inv]
    ring

/-- Exact form of the conjugate difference after an arbitrary complex
embedding of the quadratic field. -/
theorem shiftedSquareZeta_embedding_sub_star
    (a : ℤ) (d n : ℕ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ) :
    sigma (shiftedSquareZeta a d n) -
        sigma (star (shiftedSquareZeta a d n)) =
      ((((2 : ℚ) / (shiftedSquareQ₂ d : ℚ)) : ℂ)) *
        sigma (QuadraticAlgebra.omega : rationalQuadraticAlgebra (-a)) := by
  rw [← map_sub, shiftedSquareZeta_sub_star]
  simp only [Algebra.smul_def, map_mul]
  change sigma ((((2 : ℚ) / (shiftedSquareQ₂ d : ℚ)) : ℚ) :
      rationalQuadraticAlgebra (-a)) * sigma QuadraticAlgebra.omega = _
  rw [map_ratCast]
  norm_num

/-- The norm of the conjugate difference is exactly the parity factor
`2/q₂` times `sqrt |a|`. -/
theorem shiftedSquareZeta_embedding_sub_star_norm_eq
    (a : ℤ) (d n : ℕ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ) :
    ‖sigma (shiftedSquareZeta a d n) -
        sigma (star (shiftedSquareZeta a d n))‖ =
      (2 / (shiftedSquareQ₂ d : ℝ)) * Real.sqrt |(a : ℝ)| := by
  have homega :
      ‖sigma (QuadraticAlgebra.omega : rationalQuadraticAlgebra (-a))‖ =
        Real.sqrt |(a : ℝ)| := by
    have h := infinitePlace_rationalQuadraticOmega_eq_sqrt_abs a
      (NumberField.InfinitePlace.mk sigma)
    change ‖sigma (QuadraticAlgebra.omega : rationalQuadraticAlgebra (-a))‖ =
      Real.sqrt |(a : ℝ)| at h
    exact h
  rw [shiftedSquareZeta_embedding_sub_star, norm_mul, homega]
  by_cases hd : Even d
  · rw [shiftedSquareQ₂_eq_two_of_even hd]
    norm_num
  · rw [shiftedSquareQ₂_eq_one_of_not_even hd]
    norm_num

/-- Uniformly in parity, the conjugate difference has norm at most
`2 * sqrt |a|`. -/
theorem shiftedSquareZeta_embedding_sub_star_norm_le
    (a : ℤ) (d n : ℕ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ) :
    ‖sigma (shiftedSquareZeta a d n) -
        sigma (star (shiftedSquareZeta a d n))‖ ≤
      2 * Real.sqrt |(a : ℝ)| := by
  rw [shiftedSquareZeta_embedding_sub_star_norm_eq]
  have hsqrt : 0 ≤ Real.sqrt |(a : ℝ)| := Real.sqrt_nonneg _
  by_cases hd : Even d
  · rw [shiftedSquareQ₂_eq_two_of_even hd]
    norm_num
    linarith
  · rw [shiftedSquareQ₂_eq_one_of_not_even hd]
    norm_num

/-- Denominator-free form of the manuscript's relative error estimate.
It remains meaningful without introducing a signed or complex quotient. -/
theorem shiftedSquareZeta_embedding_relativeError_mul_le
    (a : ℤ) (d n : ℕ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (hn : 2 * Real.sqrt |(a : ℝ)| ≤ (n : ℝ))
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ) :
    (n : ℝ) * ‖sigma (shiftedSquareZeta a d n) -
        sigma (star (shiftedSquareZeta a d n))‖ ≤
      8 * Real.sqrt |(a : ℝ)| *
        ‖sigma (shiftedSquareZeta a d n)‖ := by
  have hnumerator :=
    shiftedSquareZeta_embedding_sub_star_norm_le a d n sigma
  have hdenominator :
      (n : ℝ) / 4 ≤ ‖sigma (shiftedSquareZeta a d n)‖ := by
    simpa using (shiftedSquareZeta_infinitePlace_bounds a d n hn
      (NumberField.InfinitePlace.mk sigma)).1
  calc
    (n : ℝ) * ‖sigma (shiftedSquareZeta a d n) -
          sigma (star (shiftedSquareZeta a d n))‖ ≤
        (n : ℝ) * (2 * Real.sqrt |(a : ℝ)|) :=
      mul_le_mul_of_nonneg_left hnumerator (by positivity)
    _ = (8 * Real.sqrt |(a : ℝ)|) * ((n : ℝ) / 4) := by ring
    _ ≤ (8 * Real.sqrt |(a : ℝ)|) *
          ‖sigma (shiftedSquareZeta a d n)‖ :=
      mul_le_mul_of_nonneg_left hdenominator (by positivity)
    _ = 8 * Real.sqrt |(a : ℝ)| *
          ‖sigma (shiftedSquareZeta a d n)‖ := by ring

/-- Literal complex-embedding version of
`star zeta / zeta = 1 + O(sqrt |a| / n)`, with an explicit constant. -/
theorem shiftedSquareZeta_embedding_star_div_sub_one_norm_le
    (a : ℤ) (d n : ℕ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (hn : 2 * Real.sqrt |(a : ℝ)| ≤ (n : ℝ))
    (sigma : rationalQuadraticAlgebra (-a) →+* ℂ) :
    ‖sigma (star (shiftedSquareZeta a d n)) /
          sigma (shiftedSquareZeta a d n) - 1‖ ≤
      (8 * Real.sqrt |(a : ℝ)|) / (n : ℝ) := by
  have hnegA : -a ≠ 0 := by
    intro hzero
    have hnoRoot :=
      Fact.out (p := rationalQuadraticAlgebraNoRationalRoot (-a)) 0
    apply hnoRoot
    simp [hzero]
  have ha : a ≠ 0 := neg_ne_zero.mp hnegA
  have haReal : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have hsqrtPos : 0 < Real.sqrt |(a : ℝ)| :=
    Real.sqrt_pos.2 (abs_pos.mpr haReal)
  have hnPos : (0 : ℝ) < n := by nlinarith
  have hdenominator :
      (n : ℝ) / 4 ≤ ‖sigma (shiftedSquareZeta a d n)‖ := by
    simpa using (shiftedSquareZeta_infinitePlace_bounds a d n hn
      (NumberField.InfinitePlace.mk sigma)).1
  have hdenominatorPos :
      0 < ‖sigma (shiftedSquareZeta a d n)‖ := by
    exact (div_pos hnPos (by norm_num)).trans_le hdenominator
  have hzeta : sigma (shiftedSquareZeta a d n) ≠ 0 :=
    (norm_pos_iff.mp hdenominatorPos)
  have hrelative :=
    shiftedSquareZeta_embedding_relativeError_mul_le a d n hn sigma
  have hquotient :
      sigma (star (shiftedSquareZeta a d n)) /
            sigma (shiftedSquareZeta a d n) - 1 =
        -(sigma (shiftedSquareZeta a d n) -
            sigma (star (shiftedSquareZeta a d n))) /
          sigma (shiftedSquareZeta a d n) := by
    field_simp [hzeta]
    ring
  rw [hquotient, norm_div, norm_neg]
  apply (div_le_div_iff₀ hdenominatorPos hnPos).2
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hrelative

end

end PellPaper
