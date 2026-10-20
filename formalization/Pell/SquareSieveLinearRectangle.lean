import Pell.JacobiLinearRectangleBound
import Pell.SquareSieveCorrelationAggregation
import Mathlib.Data.Nat.Squarefree

/-!
# Square sieving a literal linear form on a shifted rectangle

The degree-one branch does not satisfy the two-dimensional Fourier bound used
for higher odd degrees.  Instead, this file feeds the existing
Pólya--Vinogradov bound for a linear Jacobi form directly into the good-prime
square-sieve aggregator.
-/

namespace PellPaper

open Filter
open scoped BigOperators

noncomputable section

private theorem not_isSquare_mul_distinct_primes
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ¬ IsSquare (p * q) := by
  intro hsquare
  have hcoprime : p.Coprime q := (Nat.coprime_primes hp hq).mpr hpq
  have hsquarefree : Squarefree (p * q) :=
    (Nat.squarefree_mul hcoprime).mpr ⟨hp.squarefree, hq.squarefree⟩
  obtain ⟨r, hr⟩ := hsquare
  have hrunit : IsUnit r := hsquarefree r (by rw [hr])
  have hrone : r = 1 := Nat.isUnit_iff.mp hrunit
  rw [hrone] at hr
  have hp2 : 2 ≤ p := hp.two_le
  have hq2 : 2 ≤ q := hq.two_le
  norm_num at hr
  omega

private theorem linear_rectangle_correlation_bound
    (N : ℕ) (hN : 4 ≤ N) (Delta : ℤ)
    (a b x0 y0 : ℤ) (L₁ L₂ : ℕ)
    (hunit : ∀ p ∈ goodPrimeAnnulus N Delta,
      ∀ q ∈ goodPrimeAnnulus N Delta, p ≠ q →
        IsUnit (a : ZMod (p * q)) ∨ IsUnit (b : ZMod (p * q)))
    (p : ℕ) (hp : p ∈ goodPrimeAnnulus N Delta)
    (q : ℕ) (hq : q ∈ goodPrimeAnnulus N Delta) (hpq : p ≠ q) :
    |∑ xy ∈ (Finset.range L₁).product (Finset.range L₂),
      (jacobiSym
        (a * ((xy.1 : ℤ) + x0) + b * ((xy.2 : ℤ) + y0)) p : ℝ) *
      (jacobiSym
        (a * ((xy.1 : ℤ) + x0) + b * ((xy.2 : ℤ) + y0)) q : ℝ)| ≤
      16 * ((max L₁ L₂ : ℕ) : ℝ) * (N : ℝ) *
        (1 + Real.log (16 * (N : ℝ) ^ 2)) := by
  have hpprime : p.Prime :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
  have hqprime : q.Prime :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2
  have hpI := Finset.mem_Ioc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
  have hqI := Finset.mem_Ioc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
  have hpodd : Odd p := hpprime.odd_of_ne_two (by omega)
  have hqodd : Odd q := hqprime.odd_of_ne_two (by omega)
  have hpos : 0 < p * q := Nat.mul_pos hpprime.pos hqprime.pos
  let _ : NeZero p := ⟨hpprime.ne_zero⟩
  let _ : NeZero q := ⟨hqprime.ne_zero⟩
  have hlinear := abs_sum_jacobiSym_linear_shifted_rectangle_le
    (p * q) hpos (hpodd.mul hqodd)
      (not_isSquare_mul_distinct_primes hpprime hqprime hpq)
      a b x0 y0 L₁ L₂ (max L₁ L₂) (hunit p hp q hq hpq)
      (le_max_left _ _) (le_max_right _ _)
  have hsum :
      (∑ xy ∈ (Finset.range L₁).product (Finset.range L₂),
        (jacobiSym
          (a * ((xy.1 : ℤ) + x0) + b * ((xy.2 : ℤ) + y0)) p : ℝ) *
        (jacobiSym
          (a * ((xy.1 : ℤ) + x0) + b * ((xy.2 : ℤ) + y0)) q : ℝ)) =
      ∑ x ∈ Finset.range L₁, ∑ y ∈ Finset.range L₂,
        (jacobiSym
          (a * ((x : ℤ) + x0) + b * ((y : ℤ) + y0)) (p * q) : ℝ) := by
    rw [Finset.product_eq_sprod, Finset.sum_product]
    simp_rw [jacobiSym.mul_right, Int.cast_mul]
  rw [hsum]
  apply hlinear.trans
  have hNreal : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hpR : (p : ℝ) ≤ 4 * (N : ℝ) := by exact_mod_cast hpI.2
  have hqR : (q : ℝ) ≤ 4 * (N : ℝ) := by exact_mod_cast hqI.2
  have hm : ((p * q : ℕ) : ℝ) ≤ 16 * (N : ℝ) ^ 2 := by
    push_cast
    calc
      (p : ℝ) * (q : ℝ) ≤ (4 * (N : ℝ)) * (4 * (N : ℝ)) :=
        mul_le_mul hpR hqR (by positivity) (by positivity)
      _ = _ := by ring
  have hmpos : (0 : ℝ) < (p * q : ℕ) := by exact_mod_cast hpos
  have hmone : (1 : ℝ) ≤ (p * q : ℕ) := by exact_mod_cast hpos
  have hsqrt : Real.sqrt ((p * q : ℕ) : ℝ) ≤ 4 * (N : ℝ) := by
    calc
      Real.sqrt ((p * q : ℕ) : ℝ) ≤ Real.sqrt (16 * (N : ℝ) ^ 2) :=
        Real.sqrt_le_sqrt hm
      _ = 4 * (N : ℝ) := by
        rw [show (16 : ℝ) * (N : ℝ) ^ 2 = (4 * (N : ℝ)) ^ 2 by ring,
          Real.sqrt_sq_eq_abs, abs_of_nonneg]
        positivity
  have hlog : Real.log ((p * q : ℕ) : ℝ) ≤
      Real.log (16 * (N : ℝ) ^ 2) := Real.log_le_log hmpos hm
  have hlognonneg : 0 ≤ Real.log ((p * q : ℕ) : ℝ) :=
    Real.log_nonneg hmone
  calc
    4 * ((max L₁ L₂ : ℕ) : ℝ) * Real.sqrt ((p * q : ℕ) : ℝ) *
        (1 + Real.log ((p * q : ℕ) : ℝ)) ≤
      4 * ((max L₁ L₂ : ℕ) : ℝ) * (4 * (N : ℝ)) *
        (1 + Real.log (16 * (N : ℝ) ^ 2)) := by gcongr
    _ = 16 * ((max L₁ L₂ : ℕ) : ℝ) * (N : ℝ) *
        (1 + Real.log (16 * (N : ℝ) ^ 2)) := by ring

/-- The nonzero square values of a factored linear form on a shifted natural
rectangle satisfy the actual good-prime square-sieve bound.  Unit control for
one linear coefficient modulo every distinct good-prime product is explicit;
the degree-one certificate adapter supplies it downstream. -/
theorem eventually_squareSieve_linear_rectangle_le :
    ∀ᶠ N : ℕ in atTop, ∀ Delta c a b : ℤ, ∀ W : ℝ,
      ∀ x0 y0 : ℤ, ∀ L₁ L₂ : ℕ, ∀ f r : ℕ × ℕ → ℤ,
      Delta ≠ 0 → c ∣ Delta →
      Real.log (Delta.natAbs : ℝ) ≤ (Real.log 2 / 8) * (N : ℝ) →
      Real.log W ≤ (Real.log 2 / 16) * (N : ℝ) →
      (∀ p ∈ goodPrimeAnnulus N Delta,
        ∀ q ∈ goodPrimeAnnulus N Delta, p ≠ q →
          IsUnit (a : ZMod (p * q)) ∨ IsUnit (b : ZMod (p * q))) →
      (∀ xy ∈ (Finset.range L₁).product (Finset.range L₂),
        f xy = c * (r xy) ^ 2 *
          (a * ((xy.1 : ℤ) + x0) + b * ((xy.2 : ℤ) + y0))) →
      (∀ xy ∈ (Finset.range L₁).product (Finset.range L₂),
        ((f xy).natAbs : ℝ) ≤ W) →
      ((((Finset.range L₁).product (Finset.range L₂)).filter
        (fun xy => f xy ≠ 0 ∧ IsSquare (f xy))).card : ℝ) ≤
        (32 / Real.log 2) * (L₁ : ℝ) * (L₂ : ℝ) *
            Real.log (N : ℝ) / (N : ℝ) +
          64 * ((max L₁ L₂ : ℕ) : ℝ) * (N : ℝ) *
            (1 + Real.log (16 * (N : ℝ) ^ 2)) := by
  filter_upwards [eventually_squareSieve_squareFactor_le_of_goodPrime_correlation_bound
    (α := ℕ × ℕ), eventually_ge_atTop 4] with N hdet hN
  intro Delta c a b W x0 y0 L₁ L₂ f r hDelta hcDelta hDeltaSize hW
    hunit hfactor hsize
  let B : ℝ := 16 * ((max L₁ L₂ : ℕ) : ℝ) * (N : ℝ) *
    (1 + Real.log (16 * (N : ℝ) ^ 2))
  have hNreal : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log (16 * (N : ℝ) ^ 2) := by
    apply Real.log_nonneg
    nlinarith [sq_nonneg (N : ℝ)]
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hcorr : ∀ p ∈ goodPrimeAnnulus N Delta,
      ∀ q ∈ goodPrimeAnnulus N Delta, p ≠ q →
      |∑ xy ∈ (Finset.range L₁).product (Finset.range L₂),
        (jacobiSym
          (a * ((xy.1 : ℤ) + x0) + b * ((xy.2 : ℤ) + y0)) p : ℝ) *
        (jacobiSym
          (a * ((xy.1 : ℤ) + x0) + b * ((xy.2 : ℤ) + y0)) q : ℝ)| ≤ B := by
    intro p hp q hq hpq
    exact linear_rectangle_correlation_bound N hN Delta a b x0 y0 L₁ L₂
      hunit p hp q hq hpq
  have h := hdet Delta c W B
    ((Finset.range L₁).product (Finset.range L₂)) f r
    (fun xy => a * ((xy.1 : ℤ) + x0) + b * ((xy.2 : ℤ) + y0))
    hDelta hcDelta hDeltaSize hW hfactor hsize hB hcorr
  simp only [Finset.product_eq_sprod, Finset.card_product, Finset.card_range,
    Nat.cast_mul, B] at h ⊢
  ring_nf at h ⊢
  exact h

end

end PellPaper
