import Pell.AuxiliaryParabolaDivisorBridge

/-!
# Finite gates for degenerate auxiliary-curve components

The proof of `L:shear-bridge` in `main.tex` first discards two elementary
families before invoking a point-counting theorem on absolutely irreducible
components:

* a rational projective slope has positive lifts with scale factors
  `r₁, r₂`, and the Pell difference forces `r₁² r₂` to divide the fixed
  difference;
* a component `a * (t - s^2) - b` forces `e² u` to divide `a * h`.

This module records the exact finite arithmetic gates behind those two
sentences.  It deliberately does not estimate divisor functions, count
lattice points on a line, or invoke a curve-counting theorem.
-/

namespace PellPaper

noncomputable section

/-- Scaling two primitive projective slope pairs by positive integral
multipliers scales the Pell-factor difference by `r₁² r₂`.  This is the
algebraic identity used for the finitely many lifts of a rational slope in
the degenerate-factor case of `L:shear-bridge`. -/
theorem projectiveLift_factor_difference
    (r₁ r₂ dStar eStar uStar vStar : ℕ) :
    ((r₁ * eStar : ℕ) : ℤ) ^ 2 * (r₂ * vStar : ℕ) -
        ((r₁ * dStar : ℕ) : ℤ) ^ 2 * (r₂ * uStar : ℕ) =
      (r₁ : ℤ) ^ 2 * (r₂ : ℤ) *
        ((eStar : ℤ) ^ 2 * vStar - (dStar : ℤ) ^ 2 * uStar) := by
  push_cast
  ring

/-- If a positive projective lift has fixed nonzero Pell difference `h`,
then its scaling product divides `h`. -/
theorem projectiveLift_scale_dvd_difference
    {r₁ r₂ dStar eStar uStar vStar : ℕ} {h : ℤ}
    (hdiff :
      ((r₁ * eStar : ℕ) : ℤ) ^ 2 * (r₂ * vStar : ℕ) -
          ((r₁ * dStar : ℕ) : ℤ) ^ 2 * (r₂ * uStar : ℕ) = h) :
    (r₁ : ℤ) ^ 2 * (r₂ : ℤ) ∣ h := by
  refine ⟨(eStar : ℤ) ^ 2 * vStar - (dStar : ℤ) ^ 2 * uStar, ?_⟩
  rw [← projectiveLift_factor_difference]
  exact hdiff.symm

/-- The natural absolute value of the projective lift scale is exactly its
positive natural scale. -/
theorem natAbs_projectiveLift_scale (r₁ r₂ : ℕ) :
    ((r₁ : ℤ) ^ 2 * (r₂ : ℤ)).natAbs = r₁ ^ 2 * r₂ := by
  simp [Int.natAbs_mul, Int.natAbs_pow]

/-- A nonzero fixed difference bounds the scale product of every projective
lift by its absolute value. -/
theorem projectiveLift_scale_le_natAbs_difference
    {r₁ r₂ dStar eStar uStar vStar : ℕ} {h : ℤ}
    (hdiff :
      ((r₁ * eStar : ℕ) : ℤ) ^ 2 * (r₂ * vStar : ℕ) -
          ((r₁ * dStar : ℕ) : ℤ) ^ 2 * (r₂ * uStar : ℕ) = h)
    (hzero : h ≠ 0) :
    r₁ ^ 2 * r₂ ≤ h.natAbs := by
  rw [← natAbs_projectiveLift_scale]
  exact Int.natAbs_le_of_dvd_ne_zero
    (projectiveLift_scale_dvd_difference hdiff) hzero

/-- In the source application `h ∈ {±1, ±2}`.  Thus a positive projective
lift can only have the trivial first scale and second scale at most two.
This is the exact finite version of the `O_{A,B,h}(1)` lift statement for a
fixed rational projective slope. -/
theorem projectiveLift_scales_small_of_difference_natAbs_le_two
    {r₁ r₂ dStar eStar uStar vStar : ℕ} {h : ℤ}
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hdiff :
      ((r₁ * eStar : ℕ) : ℤ) ^ 2 * (r₂ * vStar : ℕ) -
          ((r₁ * dStar : ℕ) : ℤ) ^ 2 * (r₂ * uStar : ℕ) = h)
    (hzero : h ≠ 0) (hsmall : h.natAbs ≤ 2) :
    r₁ = 1 ∧ r₂ ≤ 2 := by
  have hscale : r₁ ^ 2 * r₂ ≤ 2 :=
    (projectiveLift_scale_le_natAbs_difference hdiff hzero).trans hsmall
  have hr₁sq : r₁ ^ 2 ≤ 2 := by
    calc
      r₁ ^ 2 = r₁ ^ 2 * 1 := (Nat.mul_one _).symm
      _ ≤ r₁ ^ 2 * r₂ := Nat.mul_le_mul_left _ (by omega)
      _ ≤ 2 := hscale
  have hr₁le : r₁ ≤ 2 := by
    apply le_of_pow_le_pow_left₀ (by decide : 2 ≠ 0) (by omega : 0 ≤ (2 : ℕ))
    calc
      r₁ ^ 2 ≤ 2 := hr₁sq
      _ ≤ 2 ^ 2 := by norm_num
  interval_cases r₁ <;> norm_num at hr₁ hr₁le hscale ⊢ <;> omega

/-- The four differences occurring in the Pell factorization have absolute
value at most two. -/
theorem natAbs_le_two_of_isSignedDyadicDifference {h : ℤ}
    (hh : IsSignedDyadicDifference h) : h.natAbs ≤ 2 := by
  rcases hh with rfl | rfl | rfl | rfl <;> norm_num [IsSignedDyadicDifference]

/-- Source-facing specialization of the finite projective-lift gate to the
four signed Pell differences. -/
theorem projectiveLift_scales_small_of_isSignedDyadicDifference
    {r₁ r₂ dStar eStar uStar vStar : ℕ} {h : ℤ}
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hh : IsSignedDyadicDifference h)
    (hdiff :
      ((r₁ * eStar : ℕ) : ℤ) ^ 2 * (r₂ * vStar : ℕ) -
          ((r₁ * dStar : ℕ) : ℤ) ^ 2 * (r₂ * uStar : ℕ) = h) :
    r₁ = 1 ∧ r₂ ≤ 2 := by
  exact projectiveLift_scales_small_of_difference_natAbs_le_two hr₁ hr₂ hdiff
    (isSignedDyadicDifference_ne_zero hh)
    (natAbs_le_two_of_isSignedDyadicDifference hh)

/-- The special parabola component gives an explicit absolute bound for
its positive denominator factor.  This turns the divisor relation already
proved in `AuxiliaryParabolaDivisorBridge` into a finite candidate gate. -/
theorem auxiliaryParabola_denominator_le_product_natAbs
    {a b h : ℤ} {d e u v : ℕ}
    (haux : auxiliaryParabolaHomogeneousLineEval a b d e u v = 0)
    (hdiff : (e : ℤ) ^ 2 * v - (d : ℤ) ^ 2 * u = h)
    (hprod : a * h ≠ 0) :
    e ^ 2 * u ≤ (a * h).natAbs := by
  have hle := Int.natAbs_le_of_dvd_ne_zero
    (e_sq_mul_u_dvd_auxiliaryParabolaProduct haux hdiff) hprod
  simpa [Int.natAbs_mul, Int.natAbs_pow] using hle

/-- Once the discarded parabola component has been removed, a nonzero
intercept itself forces the special-factor product to be nonzero.  This is
the exact hypothesis needed by the preceding absolute divisor bound. -/
theorem auxiliaryParabola_product_ne_zero_of_intercept_ne_zero
    {a b h : ℤ} {d e u v : ℕ}
    (he : 0 < e) (hu : 0 < u) (hb : b ≠ 0)
    (haux : auxiliaryParabolaHomogeneousLineEval a b d e u v = 0)
    (hdiff : (e : ℤ) ^ 2 * v - (d : ℤ) ^ 2 * u = h) :
    a * h ≠ 0 := by
  intro hzero
  have hid := auxiliaryParabolaHomogeneousLineEval_divisor_identity haux hdiff
  rw [hzero] at hid
  have hesq : (e : ℤ) ^ 2 ≠ 0 := by
    exact pow_ne_zero _ (by exact_mod_cast Nat.ne_of_gt he)
  have huZ : (u : ℤ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hu
  exact (mul_ne_zero hb (mul_ne_zero hesq huZ)) hid

/-- In particular, both positive denominator coordinates lie below the
finite absolute product `|a h|`.  These are the elementary bounds needed
before replacing the remaining line count by a divisor/lattice estimate. -/
theorem auxiliaryParabola_denominator_coordinates_le_product_natAbs
    {a b h : ℤ} {d e u v : ℕ}
    (he : 0 < e) (hu : 0 < u)
    (haux : auxiliaryParabolaHomogeneousLineEval a b d e u v = 0)
    (hdiff : (e : ℤ) ^ 2 * v - (d : ℤ) ^ 2 * u = h)
    (hprod : a * h ≠ 0) :
    e ≤ (a * h).natAbs ∧ u ≤ (a * h).natAbs := by
  have hbound := auxiliaryParabola_denominator_le_product_natAbs
    haux hdiff hprod
  constructor
  · calc
      e = e * 1 := (Nat.mul_one _).symm
      _ ≤ e * (e * u) := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt (Nat.mul_pos he hu))
      _ = e ^ 2 * u := by ring
      _ ≤ (a * h).natAbs := hbound
  · calc
      u = 1 * u := (Nat.one_mul _).symm
      _ ≤ e ^ 2 * u := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt (pow_pos he 2))
      _ ≤ (a * h).natAbs := hbound

/-- Source-facing finite gate for a retained special component: after the
`t - s²` component is removed, a nonzero intercept makes both denominator
coordinates lie in the explicit finite interval `[1, |a h|]`. -/
theorem auxiliaryParabola_denominator_coordinates_le_product_natAbs_of_intercept_ne_zero
    {a b h : ℤ} {d e u v : ℕ}
    (he : 0 < e) (hu : 0 < u) (hb : b ≠ 0)
    (haux : auxiliaryParabolaHomogeneousLineEval a b d e u v = 0)
    (hdiff : (e : ℤ) ^ 2 * v - (d : ℤ) ^ 2 * u = h) :
    e ≤ (a * h).natAbs ∧ u ≤ (a * h).natAbs := by
  apply auxiliaryParabola_denominator_coordinates_le_product_natAbs he hu haux hdiff
  exact auxiliaryParabola_product_ne_zero_of_intercept_ne_zero he hu hb haux hdiff

end

end PellPaper
