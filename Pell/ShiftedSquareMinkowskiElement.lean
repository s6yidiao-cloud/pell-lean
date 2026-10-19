import Pell.ShiftedSquarePrincipalIdealDivisor
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.Tactic

/-!
# A small Minkowski element in the shifted-square ideal divisor

This file applies Mathlib's genuine Minkowski ideal theorem to the explicit
ideal `shiftedSquareIdealDivisor heq`.  It converts the integral ideal to a
nonzero fractional ideal, pulls the resulting field element back to the ring
of integers, and specializes the signature factor in quadratic degree.

The final bound is

`|Norm mu| ≤ d₀ * sqrt |discr K|`

for a nonzero `mu ∈ shiftedSquareIdealDivisor heq`.  No project-specific
Minkowski or class-group assertion is introduced.
-/

namespace PellPaper

noncomputable section

open scoped nonZeroDivisors

local instance shiftedSquareMinkowskiElement_numberField (a : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

theorem rationalQuadraticAlgebra_nrComplexPlaces_le_one
    (a : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField.InfinitePlace.nrComplexPlaces
        (rationalQuadraticAlgebra (-a)) ≤ 1 := by
  have hrank : Module.finrank ℚ (rationalQuadraticAlgebra (-a)) = 2 :=
    QuadraticAlgebra.finrank_eq_two ((-a : ℤ) : ℚ) 0
  have hsignature :=
    NumberField.InfinitePlace.card_add_two_mul_card_eq_rank
      (rationalQuadraticAlgebra (-a))
  rw [hrank] at hsignature
  omega

theorem rationalQuadraticAlgebra_minkowskiFactor_le_one
    (a : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    (4 / Real.pi) ^
          NumberField.InfinitePlace.nrComplexPlaces
            (rationalQuadraticAlgebra (-a)) *
        (Module.finrank ℚ
          (rationalQuadraticAlgebra (-a))).factorial /
      (Module.finrank ℚ
        (rationalQuadraticAlgebra (-a))) ^
          (Module.finrank ℚ (rationalQuadraticAlgebra (-a))) ≤ (1 : ℝ) := by
  have hrank : Module.finrank ℚ (rationalQuadraticAlgebra (-a)) = 2 :=
    QuadraticAlgebra.finrank_eq_two ((-a : ℤ) : ℚ) 0
  have hr2 := rationalQuadraticAlgebra_nrComplexPlaces_le_one a
  have hr2cases :
      NumberField.InfinitePlace.nrComplexPlaces
          (rationalQuadraticAlgebra (-a)) = 0 ∨
        NumberField.InfinitePlace.nrComplexPlaces
          (rationalQuadraticAlgebra (-a)) = 1 := by
    omega
  rcases hr2cases with hr2zero | hr2one
  · norm_num [hrank, hr2zero]
  · rw [hrank, hr2one]
    norm_num
    calc
      4 / Real.pi * 2 / 4 = 2 / Real.pi := by ring
      _ ≤ 1 := by
        apply (div_le_iff₀ Real.pi_pos).2
        nlinarith [Real.pi_gt_three]

theorem exists_shiftedSquareIdealDivisor_minkowskiElement
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (ha : Squarefree a) (hd : 0 < d)
    (heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a) :
    ∃ mu : NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a)),
      mu ∈ shiftedSquareIdealDivisor heq ∧
      mu ≠ 0 ∧
      |Algebra.norm ℚ
          (mu : rationalQuadraticAlgebra (-a))| ≤
        (shiftedSquareD₀ d : ℝ) *
          (4 / Real.pi) ^
            NumberField.InfinitePlace.nrComplexPlaces
              (rationalQuadraticAlgebra (-a)) *
          (Module.finrank ℚ
              (rationalQuadraticAlgebra (-a))).factorial /
            (Module.finrank ℚ
              (rationalQuadraticAlgebra (-a))) ^
                (Module.finrank ℚ (rationalQuadraticAlgebra (-a))) *
          Real.sqrt |NumberField.discr (rationalQuadraticAlgebra (-a))| := by
  let K := rationalQuadraticAlgebra (-a)
  let O := NumberField.RingOfIntegers K
  let I : Ideal O := shiftedSquareIdealDivisor heq
  have hIne : I ≠ 0 := by
    simpa [I, O, K] using shiftedSquareIdealDivisor_ne_bot ha hd heq
  let I0 : (Ideal O)⁰ :=
    ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hIne⟩
  obtain ⟨x, hx, hx0, hbound⟩ :=
    NumberField.exists_ne_zero_mem_ideal_of_norm_le_mul_sqrt_discr
      K (FractionalIdeal.mk0 K I0)
  have hxI : x ∈ (I : FractionalIdeal O⁰ K) := by
    simpa only [I0, FractionalIdeal.coe_mk0] using hx
  obtain ⟨mu, hmuI, hmux⟩ :=
    (FractionalIdeal.mem_coeIdeal O⁰).mp hxI
  have hmu0 : mu ≠ 0 := by
    intro hmu
    apply hx0
    rw [← hmux, hmu, map_zero]
  refine ⟨mu, ?_, hmu0, ?_⟩
  · simpa only [I] using hmuI
  · rw [← hmux] at hbound
    have hnormI :
        ((FractionalIdeal.absNorm
          ((FractionalIdeal.mk0 K I0 :
            (FractionalIdeal O⁰ K)ˣ) : FractionalIdeal O⁰ K) : ℚ) : ℝ) =
          (shiftedSquareD₀ d : ℝ) := by
      rw [FractionalIdeal.coe_mk0, FractionalIdeal.coeIdeal_absNorm]
      norm_num [I0, I, shiftedSquareIdealDivisor_absNorm ha heq]
    rw [hnormI] at hbound
    simpa only [K, O] using hbound

theorem exists_shiftedSquareIdealDivisor_minkowskiElement_norm_le
    {a : ℤ} {d w n : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    (ha : Squarefree a) (hd : 0 < d)
    (heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a) :
    ∃ mu : NumberField.RingOfIntegers (rationalQuadraticAlgebra (-a)),
      mu ∈ shiftedSquareIdealDivisor heq ∧
      mu ≠ 0 ∧
      |Algebra.norm ℚ
          (mu : rationalQuadraticAlgebra (-a))| ≤
        (shiftedSquareD₀ d : ℝ) *
          Real.sqrt |NumberField.discr (rationalQuadraticAlgebra (-a))| := by
  obtain ⟨mu, hmuI, hmu0, hbound⟩ :=
    exists_shiftedSquareIdealDivisor_minkowskiElement ha hd heq
  refine ⟨mu, hmuI, hmu0, hbound.trans ?_⟩
  let F : ℝ :=
    (4 / Real.pi) ^
          NumberField.InfinitePlace.nrComplexPlaces
            (rationalQuadraticAlgebra (-a)) *
        (Module.finrank ℚ
          (rationalQuadraticAlgebra (-a))).factorial /
      (Module.finrank ℚ
        (rationalQuadraticAlgebra (-a))) ^
          (Module.finrank ℚ (rationalQuadraticAlgebra (-a)))
  have hF : F ≤ 1 := by
    simpa only [F] using
      rationalQuadraticAlgebra_minkowskiFactor_le_one a
  have hF0 : 0 ≤ F := by
    dsimp [F]
    positivity
  have hd0 : 0 ≤ (shiftedSquareD₀ d : ℝ) := by positivity
  have hsqrt :
      0 ≤ Real.sqrt |NumberField.discr (rationalQuadraticAlgebra (-a))| :=
    Real.sqrt_nonneg _
  calc
    (shiftedSquareD₀ d : ℝ) *
          (4 / Real.pi) ^
            NumberField.InfinitePlace.nrComplexPlaces
              (rationalQuadraticAlgebra (-a)) *
          (Module.finrank ℚ
              (rationalQuadraticAlgebra (-a))).factorial /
            (Module.finrank ℚ
              (rationalQuadraticAlgebra (-a))) ^
                (Module.finrank ℚ (rationalQuadraticAlgebra (-a))) *
          Real.sqrt |NumberField.discr (rationalQuadraticAlgebra (-a))| =
        (shiftedSquareD₀ d : ℝ) * F *
          Real.sqrt |NumberField.discr (rationalQuadraticAlgebra (-a))| := by
      dsimp [F]
      ring
    _ ≤ (shiftedSquareD₀ d : ℝ) * 1 *
          Real.sqrt |NumberField.discr (rationalQuadraticAlgebra (-a))| := by
      gcongr
    _ = (shiftedSquareD₀ d : ℝ) *
          Real.sqrt |NumberField.discr (rationalQuadraticAlgebra (-a))| := by
      ring

end

end PellPaper
