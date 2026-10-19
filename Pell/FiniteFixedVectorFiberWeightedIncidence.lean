import Pell.FiniteRadialBallWeightedIncidence
import Mathlib.Tactic

/-!
# Finite fixed-vector fibers from weighted radial incidence

This candidate isolates the finite combinatorial bridge used after assigning
one lattice vector to each cell.  A pointwise bound on every label fiber by a
constant plus a scaled reciprocal radius is summed over the literal image of
the label map.  Linear-plus-square ball growth for that image then closes the
count through the existing weighted radial-incidence theorem.

No lattice, shortest-vector, cell-geometry, or character-sum assertion occurs
in this file.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- A fixed-label fiber estimate with constant coefficient dominated by its
reciprocal-radius coefficient can be summed using radial ball growth on the
finite label image. -/
theorem card_le_coeff_mul_linear_square_radialWeightedImage_of_fiber_bound
    {ι κ : Type*} [DecidableEq κ]
    (J : Finset ι) (f : ι → κ) (r : κ → ℝ)
    (H A B C₀ C₁ : ℝ)
    (hH : 1 ≤ H) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hC₁ : 0 ≤ C₁) (hC₀C₁ : C₀ ≤ C₁)
    (hrLower : ∀ y ∈ J.image f, 1 ≤ r y)
    (hrUpper : ∀ y ∈ J.image f, r y ≤ H)
    (hball : ∀ t : ℝ, 1 ≤ t → t ≤ H →
      ((((J.image f).filter fun y => r y ≤ t).card : ℕ) : ℝ) ≤
        A * t + B * t ^ 2)
    (hfiber : ∀ y ∈ J.image f,
      (((J.filter fun i => f i = y).card : ℕ) : ℝ) ≤
        C₀ + C₁ * H / r y) :
    (J.card : ℝ) ≤
      C₁ * (A * H * (2 + Real.log H) + 3 * B * H ^ 2) := by
  classical
  have hdecomposition : (J.card : ℝ) =
      ∑ y ∈ J.image f,
        (((J.filter fun i => f i = y).card : ℕ) : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_image f J
  have hweighted :=
    sum_one_add_scaledReciprocalRadius_le_of_linear_square_ballGrowth
      (J.image f) r H A B hH hA hB hrLower hrUpper hball
  rw [hdecomposition]
  calc
    (∑ y ∈ J.image f,
        (((J.filter fun i => f i = y).card : ℕ) : ℝ)) ≤
        ∑ y ∈ J.image f, (C₀ + C₁ * H / r y) := by
      exact Finset.sum_le_sum hfiber
    _ ≤ ∑ y ∈ J.image f, C₁ * (1 + H / r y) := by
      apply Finset.sum_le_sum
      intro y hy
      calc
        C₀ + C₁ * H / r y ≤ C₁ + C₁ * H / r y :=
          add_le_add_left hC₀C₁ _
        _ = C₁ * (1 + H / r y) := by ring
    _ = C₁ * ∑ y ∈ J.image f, (1 + H / r y) := by
      rw [Finset.mul_sum]
    _ ≤ C₁ * (A * H * (2 + Real.log H) + 3 * B * H ^ 2) :=
      mul_le_mul_of_nonneg_left hweighted hC₁

/-- The numerical specialization needed by the complex Main3 short-vector
fibers.  The constants are kept expanded into the eventual reciprocal-linear
and reciprocal-square tail coefficients. -/
theorem card_le_complexFixedVectorRadialWeightedImage
    {ι κ : Type*} [DecidableEq κ]
    (J : Finset ι) (f : ι → κ) (r : κ → ℝ)
    (H Delta : ℝ)
    (hH : 1 ≤ H) (hDelta : 0 < Delta)
    (hrLower : ∀ y ∈ J.image f, 1 ≤ r y)
    (hrUpper : ∀ y ∈ J.image f, r y ≤ H)
    (hball : ∀ t : ℝ, 1 ≤ t → t ≤ H →
      ((((J.image f).filter fun y => r y ≤ t).card : ℕ) : ℝ) ≤
        12 * t + (72 / Delta) * t ^ 2)
    (hfiber : ∀ y ∈ J.image f,
      (((J.filter fun i => f i = y).card : ℕ) : ℝ) ≤
        140 + 768 * H / r y) :
    (J.card : ℝ) ≤
      9216 * H * (2 + Real.log H) + 165888 * H ^ 2 / Delta := by
  have hbound :=
    card_le_coeff_mul_linear_square_radialWeightedImage_of_fiber_bound
      J f r H 12 (72 / Delta) 140 768 hH (by norm_num)
        (by positivity) (by norm_num) (by norm_num)
        hrLower hrUpper hball hfiber
  calc
    (J.card : ℝ) ≤
        768 * (12 * H * (2 + Real.log H) +
          3 * (72 / Delta) * H ^ 2) := hbound
    _ = 9216 * H * (2 + Real.log H) +
        165888 * H ^ 2 / Delta := by ring

end

end PellPaper
