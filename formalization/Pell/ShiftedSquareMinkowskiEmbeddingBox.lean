import Pell.ShiftedSquareFieldDiscriminantBound
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.Tactic

/-!
# A simultaneous Minkowski embedding box for quadratic ideals

This isolated candidate applies Mathlib's open-box form of Minkowski's
theorem.  Unlike the existing norm-only application, the conclusion retains
a bound at every infinite place simultaneously.
-/

namespace PellPaper

noncomputable section

open scoped ENNReal NNReal nonZeroDivisors
open MeasureTheory MeasureTheory.Measure

local instance shiftedSquareMinkowskiEmbeddingBox_numberField (a : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

/-- A generous explicit radius for a nonzero integral ideal in a quadratic
number field.  The constant four leaves strict slack in Minkowski's open
convex-body inequality for either quadratic signature. -/
def quadraticIdealEmbeddingBoxRadius
    (K : Type*) [Field K] [NumberField K]
    (I : Ideal (NumberField.RingOfIntegers K)) : ℝ≥0 :=
  4 * NNReal.sqrt
    ((Ideal.absNorm I : ℝ≥0) * NNReal.sqrt ‖NumberField.discr K‖₊)

theorem quadraticIdealEmbeddingBoxRadius_coe
    (K : Type*) [Field K] [NumberField K]
    (I : Ideal (NumberField.RingOfIntegers K)) :
    (quadraticIdealEmbeddingBoxRadius K I : ℝ) =
      4 * Real.sqrt
        ((Ideal.absNorm I : ℝ) * Real.sqrt |NumberField.discr K|) := by
  simp only [quadraticIdealEmbeddingBoxRadius, NNReal.coe_mul,
    NNReal.coe_ofNat, Real.coe_sqrt, NNReal.coe_natCast,
    coe_nnnorm, Int.norm_eq_abs]

theorem exists_quadraticIdeal_ne_zero_mem_embedding_lt
    (K : Type*) [Field K] [NumberField K]
    (hrank : Module.finrank ℚ K = 2)
    (I : Ideal (NumberField.RingOfIntegers K)) (hI : I ≠ ⊥) :
    ∃ mu : NumberField.RingOfIntegers K,
      mu ∈ I ∧ mu ≠ 0 ∧
      ∀ v : NumberField.InfinitePlace K,
        v mu < quadraticIdealEmbeddingBoxRadius K I := by
  let I0 : (Ideal (NumberField.RingOfIntegers K))⁰ :=
    ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩
  let J : (FractionalIdeal
      (NumberField.RingOfIntegers K)⁰ K)ˣ :=
    FractionalIdeal.mk0 K I0
  let B := quadraticIdealEmbeddingBoxRadius K I
  have hnormI : 0 < Ideal.absNorm I := by
    exact Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp hI)
  have hdisc : NumberField.discr K ≠ 0 := NumberField.discr_ne_zero K
  have hdiscNorm : 0 < ‖NumberField.discr K‖₊ := by
    exact norm_pos_iff.mpr hdisc
  have hscale : 0 <
      (Ideal.absNorm I : ℝ≥0) * NNReal.sqrt ‖NumberField.discr K‖₊ := by
    exact mul_pos (by exact_mod_cast hnormI)
      (NNReal.sqrt_pos.2 hdiscNorm)
  have hmink_le : NumberField.mixedEmbedding.minkowskiBound K J ≤
      (4 : ℝ≥0∞) *
        ((Ideal.absNorm I : ℝ≥0∞) *
          (NNReal.sqrt ‖NumberField.discr K‖₊ : ℝ≥0∞)) := by
    rw [NumberField.mixedEmbedding.minkowskiBound,
      NumberField.mixedEmbedding.volume_fundamentalDomain_fractionalIdealLatticeBasis,
      NumberField.mixedEmbedding.volume_fundamentalDomain_latticeBasis]
    simp only [J, I0, FractionalIdeal.coe_mk0,
      FractionalIdeal.coeIdeal_absNorm,
      NumberField.mixedEmbedding.finrank, hrank]
    norm_num only [Rat.cast_natCast, ENNReal.ofReal_natCast, pow_two]
    calc
      (Ideal.absNorm I : ℝ≥0∞) *
            ((2 : ℝ≥0∞)⁻¹ ^
              NumberField.InfinitePlace.nrComplexPlaces K *
            (NNReal.sqrt ‖NumberField.discr K‖₊ : ℝ≥0∞)) * 4 ≤
          (Ideal.absNorm I : ℝ≥0∞) *
            (1 * (NNReal.sqrt ‖NumberField.discr K‖₊ : ℝ≥0∞)) * 4 := by
        gcongr
        exact pow_le_one₀ (by positivity) (by norm_num)
      _ = (4 : ℝ≥0∞) *
          ((Ideal.absNorm I : ℝ≥0∞) *
            (NNReal.sqrt ‖NumberField.discr K‖₊ : ℝ≥0∞)) := by ring
  have hmink_lt_Bsq : NumberField.mixedEmbedding.minkowskiBound K J <
      (B : ℝ≥0∞) ^ 2 := by
    refine hmink_le.trans_lt ?_
    have hscaleE : (0 : ℝ≥0∞) <
        (Ideal.absNorm I : ℝ≥0∞) *
          (NNReal.sqrt ‖NumberField.discr K‖₊ : ℝ≥0∞) := by
      exact_mod_cast hscale
    have hBsqNN : B ^ 2 =
        (16 : ℝ≥0) *
          ((Ideal.absNorm I : ℝ≥0) *
            NNReal.sqrt ‖NumberField.discr K‖₊) := by
      simp only [B, quadraticIdealEmbeddingBoxRadius, mul_pow,
        NNReal.sq_sqrt]
      ring
    have hBsqE : (B : ℝ≥0∞) ^ 2 =
        (16 : ℝ≥0∞) *
          ((Ideal.absNorm I : ℝ≥0∞) *
            (NNReal.sqrt ‖NumberField.discr K‖₊ : ℝ≥0∞)) := by
      exact_mod_cast hBsqNN
    rw [hBsqE]
    gcongr
    · finiteness
    · norm_num
  obtain ⟨x, hxJ, hx0, hxplace⟩ :=
    NumberField.mixedEmbedding.exists_ne_zero_mem_ideal_lt
      (f := fun _ => B) K J (by
        rw [NumberField.mixedEmbedding.convexBodyLT_volume]
        rw [Finset.prod_pow_eq_pow_sum,
          NumberField.InfinitePlace.sum_mult_eq, hrank]
        exact hmink_lt_Bsq.trans_le (by
          calc
            (B : ℝ≥0∞) ^ 2 = 1 * (B : ℝ≥0∞) ^ 2 := by rw [one_mul]
            _ ≤ (NumberField.mixedEmbedding.convexBodyLTFactor K : ℝ≥0∞) *
                (B : ℝ≥0∞) ^ 2 := by
              gcongr
              exact_mod_cast
                NumberField.mixedEmbedding.one_le_convexBodyLTFactor K))
  have hxI : x ∈ (I : FractionalIdeal
      (NumberField.RingOfIntegers K)⁰ K) := by
    simpa only [J, I0, FractionalIdeal.coe_mk0] using hxJ
  obtain ⟨mu, hmuI, hmux⟩ :=
    (FractionalIdeal.mem_coeIdeal
      (NumberField.RingOfIntegers K)⁰).mp hxI
  have hmu0 : mu ≠ 0 := by
    intro hmu
    apply hx0
    rw [← hmux, hmu, map_zero]
  refine ⟨mu, hmuI, hmu0, ?_⟩
  intro v
  rw [← hmux] at hxplace
  exact hxplace v

/-- The simultaneous infinite-place version for the explicit shifted-square
ideal divisor. -/
theorem exists_shiftedSquareIdealDivisor_minkowskiEmbeddingBox
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (ha : Squarefree a) (hd : 0 < d)
    (heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a) :
    ∃ mu : NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a)),
      mu ∈ shiftedSquareIdealDivisor heq ∧
      mu ≠ 0 ∧
      ∀ v : NumberField.InfinitePlace (rationalQuadraticAlgebra (-a)),
        v mu <
          4 * Real.sqrt
            ((shiftedSquareD₀ d : ℝ) *
              Real.sqrt
                |NumberField.discr (rationalQuadraticAlgebra (-a))|) := by
  let K := rationalQuadraticAlgebra (-a)
  let I : Ideal (NumberField.RingOfIntegers K) :=
    shiftedSquareIdealDivisor heq
  have hrank : Module.finrank ℚ K = 2 := by
    exact QuadraticAlgebra.finrank_eq_two ((-a : ℤ) : ℚ) 0
  have hI : I ≠ ⊥ := by
    simpa only [I, K] using shiftedSquareIdealDivisor_ne_bot ha hd heq
  obtain ⟨mu, hmuI, hmu0, hmuPlace⟩ :=
    exists_quadraticIdeal_ne_zero_mem_embedding_lt K hrank I hI
  refine ⟨mu, ?_, hmu0, ?_⟩
  · simpa only [I, K] using hmuI
  · intro v
    have hv := hmuPlace v
    rw [quadraticIdealEmbeddingBoxRadius_coe,
      shiftedSquareIdealDivisor_absNorm ha heq] at hv
    exact hv

/-- A route-facing version whose radius depends only on the shifted-square
source norm and the absolute shift. -/
theorem exists_shiftedSquareIdealDivisor_minkowskiEmbeddingBox_lt_eight
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (ha : Squarefree a) (hd : 0 < d)
    (heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a) :
    ∃ mu : NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a)),
      mu ∈ shiftedSquareIdealDivisor heq ∧
      mu ≠ 0 ∧
      ∀ v : NumberField.InfinitePlace (rationalQuadraticAlgebra (-a)),
        v mu <
          8 * Real.sqrt
            ((shiftedSquareD₀ d : ℝ) * Real.sqrt |a|) := by
  obtain ⟨mu, hmuI, hmu0, hmuPlace⟩ :=
    exists_shiftedSquareIdealDivisor_minkowskiEmbeddingBox ha hd heq
  refine ⟨mu, hmuI, hmu0, ?_⟩
  intro v
  refine (hmuPlace v).trans_le ?_
  have hdisc :=
    sqrt_abs_rationalQuadraticAlgebra_neg_fieldDiscriminant_le a
  have hd0 : 0 ≤ (shiftedSquareD₀ d : ℝ) := by positivity
  let X : ℝ :=
    (shiftedSquareD₀ d : ℝ) * Real.sqrt |a|
  have hX : 0 ≤ X := by
    dsimp only [X]
    positivity
  have hinside :
      (shiftedSquareD₀ d : ℝ) *
          Real.sqrt
            |NumberField.discr (rationalQuadraticAlgebra (-a))| ≤
        4 * X := by
    calc
      (shiftedSquareD₀ d : ℝ) *
            Real.sqrt
              |NumberField.discr (rationalQuadraticAlgebra (-a))| ≤
          (shiftedSquareD₀ d : ℝ) *
            (2 * Real.sqrt |a|) :=
        mul_le_mul_of_nonneg_left hdisc hd0
      _ = 2 * X := by dsimp only [X]; ring
      _ ≤ 4 * X := by nlinarith
  calc
    4 * Real.sqrt
          ((shiftedSquareD₀ d : ℝ) *
            Real.sqrt
              |NumberField.discr (rationalQuadraticAlgebra (-a))|) ≤
        4 * Real.sqrt (4 * X) := by
      gcongr
    _ = 8 * Real.sqrt X := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num
      ring
    _ = 8 * Real.sqrt
        ((shiftedSquareD₀ d : ℝ) * Real.sqrt |a|) := by rfl

end

end PellPaper
