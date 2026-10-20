import Pell.ShiftedSquareMinkowskiElement
import Mathlib.Tactic

/-!
# A uniform field-discriminant bound for shifted-square quadratic algebras

For the quadratic field `K = ℚ(√(-a))`, the explicit integral pair
`1, √(-a)` has discriminant `-4a`.  Comparing this pair with an actual
integral basis shows that the field discriminant differs from `-4a` by the
square of a nonzero integer.  In particular,

`|NumberField.discr K| ≤ 4 * |a|`.

This comparison needs only the same no-rational-root instance as the
shifted-square route; squarefreeness is not needed for the discriminant
inequality itself.
-/

namespace PellPaper

noncomputable section

local instance shiftedSquareFieldDiscriminantBound_numberField (d : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot d)] :
    NumberField (rationalQuadraticAlgebra d) :=
  rationalQuadraticAlgebra_numberField d

private theorem shiftedSquare_rationalQuadraticAlgebra_one_re (d : ℤ) :
    (1 : rationalQuadraticAlgebra d).re = 1 := rfl

private def shiftedSquareOmegaInteger (d : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot d)] :
    NumberField.RingOfIntegers (rationalQuadraticAlgebra d) :=
  ⟨QuadraticAlgebra.omega, rationalQuadraticAlgebra_omega_isIntegral d⟩

@[simp]
private theorem coe_shiftedSquareOmegaInteger (d : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot d)] :
    ((shiftedSquareOmegaInteger d :
      NumberField.RingOfIntegers (rationalQuadraticAlgebra d)) :
        rationalQuadraticAlgebra d) = QuadraticAlgebra.omega := rfl

private theorem shiftedSquare_algebraTrace_cast_eq_coordinates (d : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot d)]
    (z : NumberField.RingOfIntegers (rationalQuadraticAlgebra d)) :
    ((Algebra.trace ℤ _ z : ℤ) : ℚ) =
      2 * (z : rationalQuadraticAlgebra d).re := by
  change (algebraMap ℤ ℚ) (Algebra.trace ℤ _ z) = _
  rw [← Algebra.intTrace_eq_trace ℤ
    (NumberField.RingOfIntegers (rationalQuadraticAlgebra d))]
  rw [Algebra.algebraMap_intTrace (A := ℤ) (K := ℚ)
    (L := rationalQuadraticAlgebra d)
    (B := NumberField.RingOfIntegers (rationalQuadraticAlgebra d))]
  exact rationalQuadraticAlgebra_trace_apply d
    (z : rationalQuadraticAlgebra d)

private theorem shiftedSquareIntegerPair_discriminant (d : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot d)] :
    Algebra.discr ℤ ![
      (1 : NumberField.RingOfIntegers (rationalQuadraticAlgebra d)),
      shiftedSquareOmegaInteger d] = 4 * d := by
  apply (Int.cast_injective (α := ℚ))
  rw [Algebra.discr_def, Matrix.det_fin_two]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply]
  simp only [Int.cast_sub, Int.cast_mul]
  repeat' rw [shiftedSquare_algebraTrace_cast_eq_coordinates]
  simp [QuadraticAlgebra.omega,
    shiftedSquare_rationalQuadraticAlgebra_one_re]
  ring

/-- Comparing the explicit integral pair `1, √(-a)` with an integral basis
produces its exact index-square relation with the field discriminant. -/
theorem exists_nonzero_sq_mul_rationalQuadraticAlgebra_neg_fieldDiscriminant_eq
    (a : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    ∃ c : ℤ, c ≠ 0 ∧
      -4 * a = c ^ 2 *
        NumberField.discr (rationalQuadraticAlgebra (-a)) := by
  let O := NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a))
  let b : Module.Basis (Fin 2) ℤ O :=
    Module.finBasisOfFinrankEq ℤ O (by
      rw [NumberField.RingOfIntegers.rank,
        QuadraticAlgebra.finrank_eq_two])
  let v : Fin 2 → O := ![(1 : O), shiftedSquareOmegaInteger (-a)]
  let M : Matrix (Fin 2) (Fin 2) ℤ := b.toMatrix v
  have hchange := Algebra.discr_of_matrix_vecMul b M
  have hvec :
      Matrix.vecMul (b : Fin 2 → O)
          (M.map (algebraMap ℤ O)) = v := by
    exact b.toMatrix_map_vecMul v
  rw [hvec, NumberField.discr_eq_discr] at hchange
  have hpair : Algebra.discr ℤ v = -4 * a := by
    dsimp only [v, O]
    rw [shiftedSquareIntegerPair_discriminant]
    ring
  rw [hpair] at hchange
  have hdet : M.det ≠ 0 := by
    intro hdet0
    rw [hdet0, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul] at hchange
    have hnegA : -a ≠ 0 := by
      intro hnegA0
      have hnoRoot :=
        Fact.out (p := rationalQuadraticAlgebraNoRationalRoot (-a)) 0
      apply hnoRoot
      simp [hnegA0]
    have ha4 : -4 * a ≠ 0 := by
      exact mul_ne_zero (by norm_num) (neg_ne_zero.mp hnegA)
    exact ha4 hchange
  exact ⟨M.det, hdet, hchange⟩

/-- The field discriminant of `ℚ(√(-a))` is bounded by the discriminant of
the explicit integral order basis `1, √(-a)`.  The hypothesis is exactly the
field-instance hypothesis already present in the shifted-square route. -/
theorem rationalQuadraticAlgebra_neg_fieldDiscriminant_abs_le_four_mul_abs
    (a : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    |NumberField.discr (rationalQuadraticAlgebra (-a))| ≤ 4 * |a| := by
  obtain ⟨c, hc0, hchange⟩ :=
    exists_nonzero_sq_mul_rationalQuadraticAlgebra_neg_fieldDiscriminant_eq a
  have hcAbs : (1 : ℤ) ≤ |c| := Int.one_le_abs hc0
  have hcSq : (1 : ℤ) ≤ |c| ^ 2 := by
    nlinarith [abs_nonneg c]
  calc
    |NumberField.discr (rationalQuadraticAlgebra (-a))| =
        1 * |NumberField.discr (rationalQuadraticAlgebra (-a))| := by ring
    _ ≤ |c| ^ 2 *
          |NumberField.discr (rationalQuadraticAlgebra (-a))| := by
      exact mul_le_mul_of_nonneg_right hcSq (abs_nonneg _)
    _ = |-4 * a| := by
      rw [← abs_pow, ← abs_mul, hchange]
    _ = 4 * |a| := by simp

/-- The corresponding real-valued square-root estimate used after the
Minkowski bound. -/
theorem sqrt_abs_rationalQuadraticAlgebra_neg_fieldDiscriminant_le
    (a : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    Real.sqrt |NumberField.discr (rationalQuadraticAlgebra (-a))| ≤
      2 * Real.sqrt |a| := by
  have hdisc :=
    rationalQuadraticAlgebra_neg_fieldDiscriminant_abs_le_four_mul_abs a
  have hdiscR :
      (|NumberField.discr (rationalQuadraticAlgebra (-a))| : ℝ) ≤
        4 * (|a| : ℝ) := by exact_mod_cast hdisc
  calc
    Real.sqrt |NumberField.discr (rationalQuadraticAlgebra (-a))| ≤
        Real.sqrt (4 * (|a| : ℝ)) := Real.sqrt_le_sqrt hdiscR
    _ = 2 * Real.sqrt |a| := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num

/-- Combining the genuine Minkowski element with the quadratic
field-discriminant comparison gives the manuscript-scale norm bound with an
explicit absolute constant. -/
theorem exists_shiftedSquareIdealDivisor_minkowskiElement_norm_le_two_mul_sqrt_abs
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (ha : Squarefree a) (hd : 0 < d)
    (heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a) :
    ∃ mu : NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a)),
      mu ∈ shiftedSquareIdealDivisor heq ∧
      mu ≠ 0 ∧
      |Algebra.norm ℚ (mu : rationalQuadraticAlgebra (-a))| ≤
        2 * (shiftedSquareD₀ d : ℝ) * Real.sqrt |a| := by
  obtain ⟨mu, hmuI, hmu0, hmu⟩ :=
    exists_shiftedSquareIdealDivisor_minkowskiElement_norm_le ha hd heq
  refine ⟨mu, hmuI, hmu0, hmu.trans ?_⟩
  have hsqrt :=
    sqrt_abs_rationalQuadraticAlgebra_neg_fieldDiscriminant_le a
  have hd0 : 0 ≤ (shiftedSquareD₀ d : ℝ) := by positivity
  calc
    (shiftedSquareD₀ d : ℝ) *
        Real.sqrt |NumberField.discr (rationalQuadraticAlgebra (-a))| ≤
      (shiftedSquareD₀ d : ℝ) * (2 * Real.sqrt |a|) := by
        exact mul_le_mul_of_nonneg_left hsqrt hd0
    _ = 2 * (shiftedSquareD₀ d : ℝ) * Real.sqrt |a| := by ring

end

end PellPaper
