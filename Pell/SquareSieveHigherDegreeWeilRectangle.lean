import Pell.OneVariableQuadraticWeilDegreeBound
import Pell.SquareSievePolynomialRectangle

/-!
# Higher-degree square sieving from the one-variable Weil input

This file composes the named one-variable quadratic-character Weil interface
with the canonical polynomial-rectangle square sieve.  A projective derivative
resultant dividing the bad-prime certificate ensures that every prime in the
good annulus is a good reduction for the higher-degree Fourier theorem.
-/

namespace PellPaper

open Filter

noncomputable section

/-- Uniform square sieving on every integer-shifted rectangle for a homogeneous
odd-degree binary polynomial of degree at least three, conditional only on the
named one-variable quadratic Weil input.

The eventual threshold is chosen after `hWeil` but before the bad-prime
certificate, polynomial, degree, rectangle, functions, and height bounds.  The
conclusion retains the canonical rectangle theorem's exact constants and uses
the Fourier constant `j + 1` supplied by the projective adapter.  Zero side
lengths are allowed. -/
theorem eventually_squareSieve_higherDegree_polynomial_rectangle_le_of_oneVariableQuadraticWeil
    (hWeil : OneVariableQuadraticWeilDegreeBound) :
    ∀ᶠ N : ℕ in atTop, ∀ Delta c : ℤ, ∀ W : ℝ,
      ∀ J : MvPolynomial (Fin 2) ℤ, ∀ j : ℕ,
      ∀ x0 y0 : ℤ, ∀ L₁ L₂ : ℕ, ∀ f r : ℕ × ℕ → ℤ,
      Delta ≠ 0 → c ∣ Delta →
      binaryProjectiveDerivativeResultant J j ∣ Delta →
      Real.log (Delta.natAbs : ℝ) ≤ (Real.log 2 / 8) * (N : ℝ) →
      Real.log W ≤ (Real.log 2 / 16) * (N : ℝ) →
      J.IsHomogeneous j → Odd j → 3 ≤ j →
      (∀ xy ∈ (Finset.range L₁).product (Finset.range L₂),
        f xy = c * (r xy) ^ 2 *
          MvPolynomial.eval
            ![x0 + (xy.1 : ℤ), y0 + (xy.2 : ℤ)] J) →
      (∀ xy ∈ (Finset.range L₁).product (Finset.range L₂),
        ((f xy).natAbs : ℝ) ≤ W) →
      ((((Finset.range L₁).product (Finset.range L₂)).filter
        (fun xy ↦ f xy ≠ 0 ∧ IsSquare (f xy))).card : ℝ) ≤
        (32 / Real.log 2) * (L₁ : ℝ) * (L₂ : ℝ) *
            Real.log (N : ℝ) / (N : ℝ) +
          4 * ((j : ℝ) + 1) ^ 2 *
            ((16 * (N : ℝ) ^ 2) *
                (1 + Real.log (16 * (N : ℝ) ^ 2)) ^ 2 +
              ((L₁ : ℝ) + (L₂ : ℝ)) *
                (1 + Real.log (16 * (N : ℝ) ^ 2))) := by
  filter_upwards
    [eventually_squareSieve_polynomial_rectangle_le_of_local_fourier2_bounds,
      eventually_ge_atTop 2]
      with N hrectangle hN
  intro Delta c W J j x0 y0 L₁ L₂ f r hDelta hcDelta
    hresultantDelta hDeltaBudget hW hJ hj hj3 hfactor hsize
  have hlocal : ∀ p ∈ goodPrimeAnnulus N Delta, ∀ hp : p.Prime,
      PrimePolynomialFourierBound p hp J ((j : ℝ) + 1) := by
    intro p hpMem _hp
    have hpPrime : p.Prime :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hpMem).1).2
    have hpLower : N < p :=
      (Finset.mem_Ioc.mp
        (Finset.mem_filter.mp (Finset.mem_filter.mp hpMem).1).1).1
    have hpDelta : ¬ (p : ℤ) ∣ Delta := (Finset.mem_filter.mp hpMem).2
    have hp2 : p ≠ 2 := by omega
    have hpResultant :
        ¬ (p : ℤ) ∣ binaryProjectiveDerivativeResultant J j := by
      intro hpDivides
      exact hpDelta (hpDivides.trans hresultantDelta)
    exact primePolynomialFourierBound_of_oneVariableQuadraticWeil
      hWeil p j hpPrime hp2 J hJ hj hj3 hpResultant
  exact hrectangle Delta c W ((j : ℝ) + 1) J j x0 y0 L₁ L₂ f r
    hDelta hcDelta hDeltaBudget hW hJ hj (by positivity) hlocal hfactor hsize

end

end PellPaper
