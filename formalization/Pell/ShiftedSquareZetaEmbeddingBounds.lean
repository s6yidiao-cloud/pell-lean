import Pell.ShiftedSquareQuadraticEmbeddingLower
import Mathlib.Tactic

/-!
# Infinite-place bounds for the normalized shifted-square element

When `n` dominates `sqrt |a|`, every infinite-place value of
`zeta = (n + sqrt(-a))/q₂` is comparable to `n`.  These estimates will
transfer the source embedding box to the target coordinates through the
same-element factorization.
-/

namespace PellPaper

noncomputable section

local instance shiftedSquareZetaEmbeddingBounds_numberField (a : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

/-- Every infinite place takes `sqrt(-a)` to an element of absolute value
exactly `sqrt |a|`. -/
theorem infinitePlace_rationalQuadraticOmega_eq_sqrt_abs
    (a : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (v : NumberField.InfinitePlace (rationalQuadraticAlgebra (-a))) :
    v (QuadraticAlgebra.omega : rationalQuadraticAlgebra (-a)) =
      Real.sqrt |a| := by
  have hsquare :
      v (QuadraticAlgebra.omega : rationalQuadraticAlgebra (-a)) ^ 2 =
        (|a| : ℤ) := by
    calc
      v (QuadraticAlgebra.omega : rationalQuadraticAlgebra (-a)) ^ 2 =
          v ((QuadraticAlgebra.omega : rationalQuadraticAlgebra (-a)) ^ 2) := by
        rw [map_pow]
      _ = v ((-a : ℤ) : rationalQuadraticAlgebra (-a)) := by
        congr 1
        rw [pow_two, QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
        norm_num
      _ = (|a| : ℤ) := by
        rw [NumberField.InfinitePlace.map_intCast]
        simp [Int.norm_eq_abs]
  calc
    v (QuadraticAlgebra.omega : rationalQuadraticAlgebra (-a)) =
        Real.sqrt
          (v (QuadraticAlgebra.omega : rationalQuadraticAlgebra (-a)) ^ 2) :=
      (Real.sqrt_sq (apply_nonneg v _)).symm
    _ = Real.sqrt |a| := by
      rw [hsquare, Int.cast_abs]

/-- Before parity normalization, `n + sqrt(-a)` lies between
`n-sqrt|a|` and `n+sqrt|a|` at every infinite place. -/
theorem infinitePlace_shiftedSquareNumerator_bounds
    (a : ℤ) (n : ℕ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (v : NumberField.InfinitePlace (rationalQuadraticAlgebra (-a))) :
    (n : ℝ) - Real.sqrt |a| ≤
        v (((n : ℚ) : rationalQuadraticAlgebra (-a)) +
          QuadraticAlgebra.omega) ∧
      v (((n : ℚ) : rationalQuadraticAlgebra (-a)) +
          QuadraticAlgebra.omega) ≤
        (n : ℝ) + Real.sqrt |a| := by
  have hvn :
      v ((n : ℚ) : rationalQuadraticAlgebra (-a)) = (n : ℝ) := by
    simp
  have hvomega := infinitePlace_rationalQuadraticOmega_eq_sqrt_abs a v
  constructor
  · calc
      (n : ℝ) - Real.sqrt |a| =
          ‖v.embedding
              ((n : ℚ) : rationalQuadraticAlgebra (-a))‖ -
            ‖-(v.embedding
              (QuadraticAlgebra.omega : rationalQuadraticAlgebra (-a)))‖ := by
        rw [norm_neg, v.norm_embedding_eq, v.norm_embedding_eq, hvn, hvomega]
      _ ≤ ‖v.embedding ((n : ℚ) : rationalQuadraticAlgebra (-a)) -
          (-(v.embedding
            (QuadraticAlgebra.omega : rationalQuadraticAlgebra (-a))))‖ :=
        norm_sub_norm_le _ _
      _ = ‖v.embedding
          (((n : ℚ) : rationalQuadraticAlgebra (-a)) +
            QuadraticAlgebra.omega)‖ := by
        rw [map_add, sub_neg_eq_add]
      _ = v (((n : ℚ) : rationalQuadraticAlgebra (-a)) +
          QuadraticAlgebra.omega) := v.norm_embedding_eq _
  · calc
      v (((n : ℚ) : rationalQuadraticAlgebra (-a)) +
          QuadraticAlgebra.omega) =
          ‖v.embedding
            (((n : ℚ) : rationalQuadraticAlgebra (-a)) +
              QuadraticAlgebra.omega)‖ := (v.norm_embedding_eq _).symm
      _ = ‖v.embedding ((n : ℚ) : rationalQuadraticAlgebra (-a)) +
          v.embedding
            (QuadraticAlgebra.omega : rationalQuadraticAlgebra (-a))‖ := by
        rw [map_add]
      _ ≤ ‖v.embedding ((n : ℚ) : rationalQuadraticAlgebra (-a))‖ +
          ‖v.embedding
            (QuadraticAlgebra.omega : rationalQuadraticAlgebra (-a))‖ :=
        norm_add_le _ _
      _ = (n : ℝ) + Real.sqrt |a| := by
        rw [v.norm_embedding_eq, v.norm_embedding_eq, hvn, hvomega]

/-- If `n >= 2*sqrt|a|`, the parity-normalized element has every
infinite-place value between `n/4` and `2n`. -/
theorem shiftedSquareZeta_infinitePlace_bounds
    (a : ℤ) (d n : ℕ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (hn : 2 * Real.sqrt |a| ≤ (n : ℝ))
    (v : NumberField.InfinitePlace (rationalQuadraticAlgebra (-a))) :
    (n : ℝ) / 4 ≤ v (shiftedSquareZeta a d n) ∧
      v (shiftedSquareZeta a d n) ≤ 2 * (n : ℝ) := by
  let z : rationalQuadraticAlgebra (-a) :=
    ((n : ℚ) : rationalQuadraticAlgebra (-a)) + QuadraticAlgebra.omega
  have hz := infinitePlace_shiftedSquareNumerator_bounds a n v
  have hzLower : (n : ℝ) / 2 ≤ v z := by
    dsimp only [z]
    nlinarith
  have hzUpper : v z ≤ 2 * (n : ℝ) := by
    dsimp only [z]
    have hsqrt : 0 ≤ Real.sqrt |a| := Real.sqrt_nonneg _
    have hnNonneg : (0 : ℝ) ≤ n := by positivity
    nlinarith
  by_cases hdEven : Even d
  · have hvalue : v (shiftedSquareZeta a d n) = (1 / 2 : ℝ) * v z := by
      rw [shiftedSquareZeta_eq_inv_smul,
        shiftedSquareQ₂_eq_two_of_even hdEven]
      simp only [Algebra.smul_def]
      rw [map_mul]
      have hq : ((2 : ℕ) : ℚ) = (2 : ℚ) := by norm_num
      rw [hq, map_inv₀ (algebraMap ℚ (rationalQuadraticAlgebra (-a))) (2 : ℚ),
        map_inv₀ v]
      have hmap_two :
          (algebraMap ℚ (rationalQuadraticAlgebra (-a))) (2 : ℚ) =
            (2 : rationalQuadraticAlgebra (-a)) := by
        norm_num
      rw [hmap_two]
      calc
        (v (2 : rationalQuadraticAlgebra (-a)))⁻¹ *
              v (((n : ℚ) : rationalQuadraticAlgebra (-a)) +
                QuadraticAlgebra.omega) =
            (2 : ℝ)⁻¹ *
              v (((n : ℚ) : rationalQuadraticAlgebra (-a)) +
                QuadraticAlgebra.omega) := by
          exact congrArg
            (fun u : ℝ => u⁻¹ *
              v (((n : ℚ) : rationalQuadraticAlgebra (-a)) +
                QuadraticAlgebra.omega))
            (NumberField.InfinitePlace.map_natCast v 2)
        _ = (1 / 2 : ℝ) * v z := by norm_num [z]
    rw [hvalue]
    constructor <;> nlinarith
  · have hvalue : v (shiftedSquareZeta a d n) = v z := by
      rw [shiftedSquareZeta_eq_inv_smul,
        shiftedSquareQ₂_eq_one_of_not_even hdEven]
      simp [z]
    rw [hvalue]
    constructor <;> nlinarith

end

end PellPaper
