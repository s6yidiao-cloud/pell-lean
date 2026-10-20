import Pell.ProjectiveCharacterSumFourierBound
import Pell.SquareSievePolynomialRectangle
import Mathlib.Tactic

/-!
# Elementary replacement for the higher-degree Weil-dependent rectangle input

The already-proved projective Gauss factorization reduces a binary Fourier
coefficient to a one-variable quadratic-character sum. Bounding that sum term
by term gives a local Fourier constant `3 * sqrt N` throughout the prime
annulus `N < p <= 4N`.

After insertion into the generic polynomial rectangle square sieve, the
former `O(N^2)` higher-degree error becomes an explicit `O(N^3)` error. No
squarefreeness, resultant, or Weil input is used in the local estimate.
-/

namespace PellPaper

open Filter
open scoped BigOperators

noncomputable section

/-- Every complex-valued quadratic-character value has norm at most one. -/
theorem norm_complex_quadraticChar_le_one_elementary
    (p : ℕ) [Fact p.Prime] (x : ZMod p) :
    ‖(quadraticChar (ZMod p) x : ℂ)‖ ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx]
  · rcases quadraticChar_dichotomy hx with h | h
    · rw [h]
      norm_num
    · rw [h]
      norm_num

/-- The termwise bound for an arbitrary one-variable quadratic-character
sum over a prime field. -/
theorem norm_sum_complex_quadraticChar_comp_le_card
    (p : ℕ) [Fact p.Prime] (g : ZMod p → ZMod p) :
    ‖∑ r : ZMod p, (quadraticChar (ZMod p) (g r) : ℂ)‖ ≤ (p : ℝ) := by
  calc
    ‖∑ r : ZMod p, (quadraticChar (ZMod p) (g r) : ℂ)‖ ≤
        ∑ r : ZMod p, ‖(quadraticChar (ZMod p) (g r) : ℂ)‖ := by
      simpa using
        norm_sum_le (Finset.univ : Finset (ZMod p))
          (fun r ↦ (quadraticChar (ZMod p) (g r) : ℂ))
    _ ≤ ∑ _r : ZMod p, (1 : ℝ) := by
      exact Finset.sum_le_sum fun r _ ↦
        norm_complex_quadraticChar_le_one_elementary p (g r)
    _ = (p : ℝ) := by simp

/-- An unconditional projective character-sum bound with the trivial
constant `sqrt p`. Its right side is `sqrt p * sqrt p = p`. -/
theorem primePolynomialProjectiveCharacterSumBound_trivial
    (p : ℕ) (hp : p.Prime) (J : MvPolynomial (Fin 2) ℤ) :
    PrimePolynomialProjectiveCharacterSumBound p hp J
      (Real.sqrt (p : ℝ)) := by
  let _ : Fact p.Prime := ⟨hp⟩
  intro a b _hab
  have hsum :
      ‖∑ r : ZMod p,
        (quadraticChar (ZMod p)
          (MvPolynomial.eval ![r, 1]
            (J.map (Int.castRingHom (ZMod p))) * (a * r + b)) : ℂ)‖ ≤
        (p : ℝ) :=
    norm_sum_complex_quadraticChar_comp_le_card p _
  calc
    ‖∑ r : ZMod p,
        (quadraticChar (ZMod p)
          (MvPolynomial.eval ![r, 1]
            (J.map (Int.castRingHom (ZMod p))) * (a * r + b)) : ℂ)‖ ≤
        (p : ℝ) := hsum
    _ = Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ) := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ p by positivity)]

/-- On the standard good-prime annulus, the elementary projective bound and
the exact Gauss factorization give a uniform binary Fourier constant
`3 * sqrt N`. -/
theorem primePolynomialFourierBound_three_sqrt_of_mem_goodPrimeAnnulus
    (N p j : ℕ) (Delta : ℤ) (hN : 4 ≤ N)
    (hpMem : p ∈ goodPrimeAnnulus N Delta) (hp : p.Prime)
    (J : MvPolynomial (Fin 2) ℤ) (hJ : J.IsHomogeneous j) (hj : Odd j) :
    PrimePolynomialFourierBound p hp J
      (3 * Real.sqrt (N : ℝ)) := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hpI : p ∈ Finset.Ioc N (4 * N) :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hpMem).1).1
  have hp2 : p ≠ 2 := by
    have hpLower := (Finset.mem_Ioc.mp hpI).1
    omega
  intro a b _hab
  have hreduce := zmodFourier2_quadraticChar_eval_binary_norm_le
    p j hp2 (J.map (Int.castRingHom (ZMod p)))
      (hJ.map (Int.castRingHom (ZMod p))) hj a b
  have hsum :
      ‖∑ r : ZMod p,
        (quadraticChar (ZMod p)
          (MvPolynomial.eval ![r, 1]
            (J.map (Int.castRingHom (ZMod p))) * (a * r + b)) : ℂ)‖ ≤
        (p : ℝ) :=
    norm_sum_complex_quadraticChar_comp_le_card p _
  have hpUpper : p ≤ 4 * N := (Finset.mem_Ioc.mp hpI).2
  have hpUpperReal : (p : ℝ) ≤ 4 * (N : ℝ) := by
    exact_mod_cast hpUpper
  have hsqrtUpper :
      Real.sqrt (p : ℝ) ≤ 2 * Real.sqrt (N : ℝ) := by
    calc
      Real.sqrt (p : ℝ) ≤ Real.sqrt (4 * (N : ℝ)) :=
        Real.sqrt_le_sqrt hpUpperReal
      _ = 2 * Real.sqrt (N : ℝ) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
        norm_num
  have hpPlus : (p : ℝ) + 1 ≤ (3 / 2 : ℝ) * p := by
    have hpTwo : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    nlinarith
  calc
    ‖zmodFourier2 (fun x y ↦
        (quadraticChar (ZMod p)
          (MvPolynomial.eval ![x, y]
            (J.map (Int.castRingHom (ZMod p)))) : ℂ)) a b‖ ≤
        Real.sqrt (p : ℝ) *
          (‖∑ r : ZMod p,
            (quadraticChar (ZMod p)
              (MvPolynomial.eval ![r, 1]
                (J.map (Int.castRingHom (ZMod p))) * (a * r + b)) : ℂ)‖ + 1) :=
      hreduce
    _ ≤ Real.sqrt (p : ℝ) * ((p : ℝ) + 1) := by gcongr
    _ ≤ (2 * Real.sqrt (N : ℝ)) * ((3 / 2 : ℝ) * p) := by gcongr
    _ = (3 * Real.sqrt (N : ℝ)) * (p : ℝ) := by ring

/-- An unconditional odd-homogeneous polynomial rectangle square sieve.
Compared with the Weil-based theorem, the `N^2` Fourier error is replaced by
the explicit `N^3` error resulting from `C = 3 * sqrt N`. -/
theorem eventually_squareSieve_oddHomogeneous_polynomial_rectangle_le_trivial :
    ∀ᶠ N : ℕ in atTop, ∀ Delta c : ℤ, ∀ W : ℝ,
      ∀ J : MvPolynomial (Fin 2) ℤ, ∀ j : ℕ,
      ∀ x0 y0 : ℤ, ∀ L₁ L₂ : ℕ, ∀ f r : ℕ × ℕ → ℤ,
      Delta ≠ 0 → c ∣ Delta →
      Real.log (Delta.natAbs : ℝ) ≤ (Real.log 2 / 8) * (N : ℝ) →
      Real.log W ≤ (Real.log 2 / 16) * (N : ℝ) →
      J.IsHomogeneous j → Odd j →
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
          36 * (N : ℝ) *
            ((16 * (N : ℝ) ^ 2) *
                (1 + Real.log (16 * (N : ℝ) ^ 2)) ^ 2 +
              ((L₁ : ℝ) + (L₂ : ℝ)) *
                (1 + Real.log (16 * (N : ℝ) ^ 2))) := by
  filter_upwards
    [eventually_squareSieve_polynomial_rectangle_le_of_local_fourier2_bounds,
      eventually_ge_atTop 4]
      with N hrectangle hN
  intro Delta c W J j x0 y0 L₁ L₂ f r hDelta hcDelta
    hDeltaBudget hW hJ hj hfactor hsize
  have hlocal : ∀ p ∈ goodPrimeAnnulus N Delta, ∀ hp : p.Prime,
      PrimePolynomialFourierBound p hp J
        (3 * Real.sqrt (N : ℝ)) := by
    intro p hpMem hpPrime
    exact primePolynomialFourierBound_three_sqrt_of_mem_goodPrimeAnnulus
      N p j Delta hN hpMem hpPrime J hJ hj
  have hbound := hrectangle Delta c W (3 * Real.sqrt (N : ℝ))
    J j x0 y0 L₁ L₂ f r hDelta hcDelta hDeltaBudget hW hJ hj
    (by positivity) hlocal hfactor hsize
  have hsqrtSq : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) := by
    exact Real.sq_sqrt (by positivity)
  calc
    _ ≤ (32 / Real.log 2) * (L₁ : ℝ) * (L₂ : ℝ) *
            Real.log (N : ℝ) / (N : ℝ) +
          4 * (3 * Real.sqrt (N : ℝ)) ^ 2 *
            ((16 * (N : ℝ) ^ 2) *
                (1 + Real.log (16 * (N : ℝ) ^ 2)) ^ 2 +
              ((L₁ : ℝ) + (L₂ : ℝ)) *
                (1 + Real.log (16 * (N : ℝ) ^ 2))) := hbound
    _ = _ := by
      rw [mul_pow, hsqrtSq]
      ring

end

end PellPaper
