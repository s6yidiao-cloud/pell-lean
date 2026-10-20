import Pell.JacobiPolynomialRectangle
import Pell.SquareSieveCorrelationAggregation

/-!
# Square sieving literal polynomial rectangles from local Fourier bounds

The actual good-prime annulus, integer Jacobi correlations, rectangle
completion and ordered-pair aggregation are joined with an explicit bound
uniform over the prime products. Only local nonzero Fourier cancellation
and the displayed logarithmic height budgets remain inputs.
-/

namespace PellPaper

noncomputable section

open Filter
open scoped BigOperators

/-- A fully quantified local Fourier input for one reduced integer binary
polynomial. The prime proof only supplies the finite-field instance. -/
def PrimePolynomialFourierBound (p : ℕ) (hp : p.Prime)
    (J : MvPolynomial (Fin 2) ℤ) (C : ℝ) : Prop :=
  letI : Fact p.Prime := ⟨hp⟩
  ∀ a b : ZMod p, (a, b) ≠ (0, 0) →
    ‖zmodFourier2 (fun u v => (quadraticChar (ZMod p)
      (MvPolynomial.eval ![u, v] (J.map (Int.castRingHom (ZMod p)))) : ℂ)) a b‖ ≤
        C * (p : ℝ)

private theorem rectangle_correlation_bound
    (N : ℕ) (hN : 4 ≤ N) (Delta : ℤ)
    (J : MvPolynomial (Fin 2) ℤ) (j : ℕ) (hJ : J.IsHomogeneous j) (hj : Odd j)
    (C : ℝ) (hC : 0 ≤ C)
    (hlocal : ∀ p ∈ goodPrimeAnnulus N Delta, ∀ hp : p.Prime,
      PrimePolynomialFourierBound p hp J C)
    (x0 y0 : ℤ) (L₁ L₂ : ℕ)
    (p : ℕ) (hp : p ∈ goodPrimeAnnulus N Delta)
    (q : ℕ) (hq : q ∈ goodPrimeAnnulus N Delta) (hpq : p ≠ q) :
    |∑ xy ∈ (Finset.range L₁).product (Finset.range L₂),
      (jacobiSym (MvPolynomial.eval ![x0 + (xy.1 : ℤ), y0 + (xy.2 : ℤ)] J) p : ℝ) *
      (jacobiSym (MvPolynomial.eval ![x0 + (xy.1 : ℤ), y0 + (xy.2 : ℤ)] J) q : ℝ)| ≤
      C ^ 2 * ((16 * (N : ℝ) ^ 2) * (1 + Real.log (16 * (N : ℝ) ^ 2)) ^ 2 +
        ((L₁ : ℝ) + (L₂ : ℝ)) * (1 + Real.log (16 * (N : ℝ) ^ 2))) := by
  have hpprime : p.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
  have hqprime : q.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2
  have hpI := Finset.mem_Ioc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
  have hqI := Finset.mem_Ioc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
  let _ : Fact p.Prime := ⟨hpprime⟩
  let _ : Fact q.Prime := ⟨hqprime⟩
  have hp2 : p ≠ 2 := by omega
  have hq2 : q ≠ 2 := by omega
  have h := abs_sum_jacobiSym_polynomial_shifted_rectangle_le_of_local_fourier2_bounds
    p q j hp2 hq2 hpq J hJ hj C C hC hC (hlocal p hp hpprime) (hlocal q hq hqprime)
    x0 y0 L₁ L₂
  have hsum :
      (∑ xy ∈ (Finset.range L₁).product (Finset.range L₂),
        (jacobiSym (MvPolynomial.eval ![x0 + (xy.1 : ℤ), y0 + (xy.2 : ℤ)] J) p : ℝ) *
        (jacobiSym (MvPolynomial.eval ![x0 + (xy.1 : ℤ), y0 + (xy.2 : ℤ)] J) q : ℝ)) =
      ∑ x ∈ Finset.range L₁, ∑ y ∈ Finset.range L₂,
        (jacobiSym (MvPolynomial.eval ![x0 + (x : ℤ), y0 + (y : ℤ)] J) (p * q) : ℝ) := by
    rw [Finset.product_eq_sprod, Finset.sum_product]
    simp_rw [jacobiSym.mul_right, Int.cast_mul]
  rw [hsum]
  apply h.trans
  rw [pow_two C]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC hC)
  have hpR : (p : ℝ) ≤ 4 * (N : ℝ) := by exact_mod_cast hpI.2
  have hqR : (q : ℝ) ≤ 4 * (N : ℝ) := by exact_mod_cast hqI.2
  have hm : ((p * q : ℕ) : ℝ) ≤ 16 * (N : ℝ) ^ 2 := by
    push_cast
    calc
      (p : ℝ) * (q : ℝ) ≤ (4 * (N : ℝ)) * (4 * (N : ℝ)) :=
        mul_le_mul hpR hqR (by positivity) (by positivity)
      _ = _ := by ring
  have hmpos : (0 : ℝ) < (p * q : ℕ) := by exact_mod_cast Nat.mul_pos hpprime.pos hqprime.pos
  have hmone : (1 : ℝ) ≤ (p * q : ℕ) := by exact_mod_cast Nat.mul_pos hpprime.pos hqprime.pos
  have hlog := Real.log_le_log hmpos hm
  have hlognonneg := Real.log_nonneg hmone
  gcongr

/-- The literal finite set of nonzero square values on an integer-shifted
rectangle has an explicit good-prime square-sieve bound. The single eventual
threshold precedes the polynomial, its degree, content, factor, offsets,
side lengths and local Fourier constant. No global correlation or
prime-density hypothesis remains. -/
theorem eventually_squareSieve_polynomial_rectangle_le_of_local_fourier2_bounds :
    ∀ᶠ N : ℕ in atTop, ∀ Delta c : ℤ, ∀ W C : ℝ,
      ∀ J : MvPolynomial (Fin 2) ℤ, ∀ j : ℕ,
      ∀ x0 y0 : ℤ, ∀ L₁ L₂ : ℕ, ∀ f r : ℕ × ℕ → ℤ,
      Delta ≠ 0 → c ∣ Delta →
      Real.log (Delta.natAbs : ℝ) ≤ (Real.log 2 / 8) * (N : ℝ) →
      Real.log W ≤ (Real.log 2 / 16) * (N : ℝ) →
      J.IsHomogeneous j → Odd j → 0 ≤ C →
      (∀ p ∈ goodPrimeAnnulus N Delta, ∀ hp : p.Prime,
        PrimePolynomialFourierBound p hp J C) →
      (∀ xy ∈ (Finset.range L₁).product (Finset.range L₂),
        f xy = c * (r xy) ^ 2 *
          MvPolynomial.eval ![x0 + (xy.1 : ℤ), y0 + (xy.2 : ℤ)] J) →
      (∀ xy ∈ (Finset.range L₁).product (Finset.range L₂), ((f xy).natAbs : ℝ) ≤ W) →
      ((((Finset.range L₁).product (Finset.range L₂)).filter
        (fun xy => f xy ≠ 0 ∧ IsSquare (f xy))).card : ℝ) ≤
        (32 / Real.log 2) * (L₁ : ℝ) * (L₂ : ℝ) * Real.log (N : ℝ) / (N : ℝ) +
          4 * C ^ 2 *
            ((16 * (N : ℝ) ^ 2) * (1 + Real.log (16 * (N : ℝ) ^ 2)) ^ 2 +
              ((L₁ : ℝ) + (L₂ : ℝ)) * (1 + Real.log (16 * (N : ℝ) ^ 2))) := by
  filter_upwards [eventually_squareSieve_squareFactor_le_of_goodPrime_correlation_bound
    (α := ℕ × ℕ), eventually_ge_atTop 4] with N hdet hN
  intro Delta c W C J j x0 y0 L₁ L₂ f r hDelta hcDelta hDeltaSize hW hJ hj hC
    hlocal hfactor hsize
  let B : ℝ := C ^ 2 *
    ((16 * (N : ℝ) ^ 2) * (1 + Real.log (16 * (N : ℝ) ^ 2)) ^ 2 +
      ((L₁ : ℝ) + (L₂ : ℝ)) * (1 + Real.log (16 * (N : ℝ) ^ 2)))
  have hlog : 0 ≤ Real.log (16 * (N : ℝ) ^ 2) := by
    apply Real.log_nonneg
    have hNR : (4 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hcorr : ∀ p ∈ goodPrimeAnnulus N Delta, ∀ q ∈ goodPrimeAnnulus N Delta,
      p ≠ q → |∑ xy ∈ (Finset.range L₁).product (Finset.range L₂),
        (jacobiSym (MvPolynomial.eval ![x0 + (xy.1 : ℤ), y0 + (xy.2 : ℤ)] J) p : ℝ) *
        (jacobiSym (MvPolynomial.eval ![x0 + (xy.1 : ℤ), y0 + (xy.2 : ℤ)] J) q : ℝ)| ≤ B := by
    intro p hp q hq hpq
    exact rectangle_correlation_bound N hN Delta J j hJ hj C hC hlocal x0 y0 L₁ L₂ p hp q hq hpq
  have h := hdet Delta c W B ((Finset.range L₁).product (Finset.range L₂)) f r
    (fun xy => MvPolynomial.eval ![x0 + (xy.1 : ℤ), y0 + (xy.2 : ℤ)] J)
    hDelta hcDelta hDeltaSize hW hfactor hsize hB hcorr
  simpa only [Finset.product_eq_sprod, Finset.card_product, Finset.card_range,
    Nat.cast_mul, B, mul_assoc] using h

end
end PellPaper
