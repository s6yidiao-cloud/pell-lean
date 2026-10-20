import Pell.HomogeneousQuadraticCharFourierBound
import Pell.SquareSievePolynomialRectangle

/-!
# From projective character cancellation to binary Fourier cancellation

The Fourier transform of an odd homogeneous binary quadratic-character
sequence has already been factored into a quadratic Gauss sum and one
one-variable projective-chart character sum.  This file packages the exact
remaining analytic leaf and derives the two-dimensional `O(p)` bound used by
the higher-degree square sieve.
-/

namespace PellPaper

noncomputable section

open scoped BigOperators

/-- The one-variable projective character-sum estimate left after the exact
Gauss-sum factorization of a nonzero binary Fourier coefficient.  This is an
honest input, not a claimed Weil theorem. -/
def PrimePolynomialProjectiveCharacterSumBound
    (p : ℕ) (hp : p.Prime) (J : MvPolynomial (Fin 2) ℤ)
    (B : ℝ) : Prop :=
  letI : Fact p.Prime := ⟨hp⟩
  ∀ a b : ZMod p, (a, b) ≠ (0, 0) →
    ‖∑ r : ZMod p,
      (quadraticChar (ZMod p)
        (MvPolynomial.eval ![r, 1]
            (J.map (Int.castRingHom (ZMod p))) * (a * r + b)) : ℂ)‖ ≤
      B * Real.sqrt (p : ℝ)

/-- A projective one-variable bound with constant `B` yields the required
two-dimensional Fourier bound with constant `B+1`.  The extra one is exactly
the projective point at infinity; `sqrt p ≤ p` absorbs it after multiplying
by the quadratic Gauss factor. -/
theorem primePolynomialFourierBound_of_projectiveCharacterSumBound
    (p j : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (J : MvPolynomial (Fin 2) ℤ) (hJ : J.IsHomogeneous j) (hj : Odd j)
    (B : ℝ)
    (hprojective : PrimePolynomialProjectiveCharacterSumBound p hp J B) :
    PrimePolynomialFourierBound p hp J (B + 1) := by
  let _ : Fact p.Prime := ⟨hp⟩
  intro a b hab
  have hreduce := zmodFourier2_quadraticChar_eval_binary_norm_le
    p j hp2 (J.map (Int.castRingHom (ZMod p)))
      (hJ.map (Int.castRingHom (ZMod p))) hj a b
  have hsum := hprojective a b hab
  have hpnonneg : (0 : ℝ) ≤ p := by positivity
  have hpone : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hsqrt : Real.sqrt (p : ℝ) ≤ (p : ℝ) :=
    Real.sqrt_le_self_iff.mpr (Or.inr hpone)
  calc
    ‖zmodFourier2 (fun x y =>
        (quadraticChar (ZMod p)
          (MvPolynomial.eval ![x, y]
            (J.map (Int.castRingHom (ZMod p)))) : ℂ)) a b‖ ≤
        Real.sqrt (p : ℝ) *
          (‖∑ r : ZMod p,
            (quadraticChar (ZMod p)
              (MvPolynomial.eval ![r, 1]
                (J.map (Int.castRingHom (ZMod p))) * (a * r + b)) : ℂ)‖ + 1) :=
      hreduce
    _ ≤ Real.sqrt (p : ℝ) *
        (B * Real.sqrt (p : ℝ) + 1) := by
      exact mul_le_mul_of_nonneg_left (add_le_add hsum le_rfl)
        (Real.sqrt_nonneg _)
    _ = B * Real.sqrt (p : ℝ) ^ 2 + Real.sqrt (p : ℝ) := by ring
    _ = B * (p : ℝ) + Real.sqrt (p : ℝ) := by
      rw [Real.sq_sqrt hpnonneg]
    _ ≤ B * (p : ℝ) + (p : ℝ) := add_le_add le_rfl hsqrt
    _ = (B + 1) * (p : ℝ) := by ring

end

end PellPaper
