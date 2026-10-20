import Pell.FriedlanderIwaniecSixthMoment
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Extracting the sixth root in the Friedlander--Iwaniec estimate

This module performs the remaining real-power and logarithmic normalization
after the assembled sixth-moment inequality.  It proves the source-oriented
one-sided estimate in the range `N ≤ M`; the opposite range still requires
the quadratic-reciprocity transpose before this result can inhabit the
Main4 rectangle interface.
-/

namespace PellPaper

noncomputable section

/-- Friedlander--Iwaniec's equation (17), written as the sum of its two
sixth-root monomials. -/
def friedlanderIwaniecBilinearScale (M N : ℕ) : ℝ :=
  ((M : ℝ) * (N : ℝ) ^ (5 / 6 : ℝ) +
      (M : ℝ) ^ (5 / 6 : ℝ) * (N : ℝ)) *
    (Real.log (3 * (M : ℝ) * (N : ℝ))) ^ (7 / 6 : ℝ)

/-- The explicit one-sided FI bilinear estimate obtained by extracting a
sixth root from `abs_friedlanderIwaniecJacobiBilinear_pow_six_le`.
The factor two is a harmless explicit replacement for the source's absolute
Vinogradov constant. -/
theorem abs_friedlanderIwaniecJacobiBilinear_le_two_mul_scale_of_le
    (alpha beta : ℕ → ℝ) (M N : ℕ)
    (hN : 2 ≤ N) (hNM : N ≤ M)
    (halpha : ∀ m ∈ Finset.Icc 1 M, |alpha m| ≤ 1)
    (hbetaEven : ∀ n : ℕ, Even n → beta n = 0)
    (hbeta : ∀ n : ℕ, |beta n| ≤ 1) :
    |friedlanderIwaniecJacobiBilinear alpha beta M N| ≤
      2 * friedlanderIwaniecBilinearScale M N := by
  let x : ℝ := M
  let y : ℝ := N
  let l : ℝ := Real.log (3 * x * y)
  let u : ℝ := 1 + Real.log x
  let v : ℝ := 1 + Real.log y
  let U : ℝ := x * y ^ (5 / 6 : ℝ) * l ^ (7 / 6 : ℝ)
  let V : ℝ := x ^ (5 / 6 : ℝ) * y * l ^ (7 / 6 : ℝ)
  let W : ℝ := U + V
  have hyTwo : (2 : ℝ) ≤ y := by
    dsimp only [y]
    exact_mod_cast hN
  have hxTwo : (2 : ℝ) ≤ x := by
    dsimp only [x]
    exact_mod_cast hN.trans hNM
  have hy : 0 < y := by linarith
  have hx : 0 < x := by linarith
  have hyOne : (1 : ℝ) ≤ y := by linarith
  have hxOne : (1 : ℝ) ≤ x := by linarith
  have hyx : y ≤ x := by
    dsimp only [x, y]
    exact_mod_cast hNM
  have hthreeY : Real.exp 1 ≤ 3 * y :=
    (Real.exp_one_lt_three).le.trans
      (by nlinarith [mul_le_mul_of_nonneg_left hyOne (show (0 : ℝ) ≤ 3 by norm_num)])
  have hthreeX : Real.exp 1 ≤ 3 * x :=
    (Real.exp_one_lt_three).le.trans
      (by nlinarith [mul_le_mul_of_nonneg_left hxOne (show (0 : ℝ) ≤ 3 by norm_num)])
  have hlogThreeY : 1 ≤ Real.log (3 * y) :=
    (Real.le_log_iff_exp_le (by positivity)).2 hthreeY
  have hlogThreeX : 1 ≤ Real.log (3 * x) :=
    (Real.le_log_iff_exp_le (by positivity)).2 hthreeX
  have hlu : u ≤ l := by
    have hsplit : l = Real.log x + Real.log (3 * y) := by
      dsimp only [l]
      rw [show 3 * x * y = x * (3 * y) by ring,
        Real.log_mul hx.ne' (by positivity)]
    dsimp only [u]
    rw [hsplit]
    linarith
  have hlv : v ≤ l := by
    have hsplit : l = Real.log y + Real.log (3 * x) := by
      dsimp only [l]
      rw [show 3 * x * y = y * (3 * x) by ring,
        Real.log_mul hy.ne' (by positivity)]
    dsimp only [v]
    rw [hsplit]
    linarith
  have hu : 0 ≤ u := by
    dsimp only [u]
    have : 0 ≤ Real.log x := Real.log_nonneg hxOne
    linarith
  have hv : 0 ≤ v := by
    dsimp only [v]
    have : 0 ≤ Real.log y := Real.log_nonneg hyOne
    linarith
  have huOne : 1 ≤ u := by
    dsimp only [u]
    exact le_add_of_nonneg_right (Real.log_nonneg hxOne)
  have hlOne : 1 ≤ l := huOne.trans hlu
  have hl : 0 ≤ l := zero_le_one.trans hlOne
  have huSix : u ^ 6 ≤ l ^ 6 := pow_le_pow_left₀ hu hlu 6
  have huv : u ^ 6 * v ≤ l ^ 6 * l :=
    mul_le_mul huSix hlv hv (pow_nonneg hl 6)
  have hfirst : x ^ 6 * y ^ 5 * u ^ 6 * v ≤
      x ^ 6 * y ^ 5 * l ^ 7 := by
    calc
      x ^ 6 * y ^ 5 * u ^ 6 * v =
          (x ^ 6 * y ^ 5) * (u ^ 6 * v) := by ring
      _ ≤ (x ^ 6 * y ^ 5) * (l ^ 6 * l) :=
        mul_le_mul_of_nonneg_left huv (by positivity)
      _ = x ^ 6 * y ^ 5 * l ^ 7 := by ring
  have hySq : y ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hy.le hyx 2
  have hlSixSeven : l ^ 6 ≤ l ^ 7 := by
    calc
      l ^ 6 = l ^ 6 * 1 := by ring
      _ ≤ l ^ 6 * l := mul_le_mul_of_nonneg_left hlOne (pow_nonneg hl 6)
      _ = l ^ 7 := by ring
  have hsecond : x ^ 3 * y ^ 8 * u ^ 6 ≤
      x ^ 5 * y ^ 6 * l ^ 7 := by
    calc
      x ^ 3 * y ^ 8 * u ^ 6 ≤ x ^ 3 * y ^ 8 * l ^ 6 := by
        gcongr
      _ = (x ^ 3 * y ^ 6 * l ^ 6) * y ^ 2 := by ring
      _ ≤ (x ^ 3 * y ^ 6 * l ^ 6) * x ^ 2 :=
        mul_le_mul_of_nonneg_left hySq (by positivity)
      _ = x ^ 5 * y ^ 6 * l ^ 6 := by ring
      _ ≤ x ^ 5 * y ^ 6 * l ^ 7 :=
        mul_le_mul_of_nonneg_left hlSixSeven (by positivity)
  have hU : 0 ≤ U := by dsimp only [U]; positivity
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hUpow : U ^ 6 = x ^ 6 * y ^ 5 * l ^ 7 := by
    dsimp only [U]
    rw [mul_pow, mul_pow, ← Real.rpow_mul_natCast hy.le,
      ← Real.rpow_mul_natCast hl]
    norm_num
  have hVpow : V ^ 6 = x ^ 5 * y ^ 6 * l ^ 7 := by
    dsimp only [V]
    rw [mul_pow, mul_pow, ← Real.rpow_mul_natCast hx.le,
      ← Real.rpow_mul_natCast hl]
    norm_num
  have hraw := abs_friedlanderIwaniecJacobiBilinear_pow_six_le
    alpha beta M N (by omega) halpha hbetaEven hbeta
  change |friedlanderIwaniecJacobiBilinear alpha beta M N| ^ 6 ≤
      y ^ 4 * (x ^ 3 * u ^ 6) *
        (x ^ 3 * y * v + 6 * y ^ 4) at hraw
  have hraw' :
      |friedlanderIwaniecJacobiBilinear alpha beta M N| ^ 6 ≤
        x ^ 6 * y ^ 5 * l ^ 7 + 6 * (x ^ 5 * y ^ 6 * l ^ 7) := by
    calc
      |friedlanderIwaniecJacobiBilinear alpha beta M N| ^ 6 ≤
          y ^ 4 * (x ^ 3 * u ^ 6) *
            (x ^ 3 * y * v + 6 * y ^ 4) := hraw
      _ = x ^ 6 * y ^ 5 * u ^ 6 * v +
          6 * (x ^ 3 * y ^ 8 * u ^ 6) := by ring
      _ ≤ x ^ 6 * y ^ 5 * l ^ 7 +
          6 * (x ^ 5 * y ^ 6 * l ^ 7) :=
        add_le_add hfirst (mul_le_mul_of_nonneg_left hsecond (by norm_num))
  have hUW : U ≤ W := by dsimp only [W]; linarith
  have hVW : V ≤ W := by dsimp only [W]; linarith
  have hUpowW : U ^ 6 ≤ W ^ 6 := pow_le_pow_left₀ hU hUW 6
  have hVpowW : V ^ 6 ≤ W ^ 6 := pow_le_pow_left₀ hV hVW 6
  have htargetPow :
      |friedlanderIwaniecJacobiBilinear alpha beta M N| ^ 6 ≤
        (2 * W) ^ 6 := by
    calc
      |friedlanderIwaniecJacobiBilinear alpha beta M N| ^ 6 ≤
          x ^ 6 * y ^ 5 * l ^ 7 + 6 * (x ^ 5 * y ^ 6 * l ^ 7) := hraw'
      _ = U ^ 6 + 6 * V ^ 6 := by rw [hUpow, hVpow]
      _ ≤ W ^ 6 + 6 * W ^ 6 :=
        add_le_add hUpowW (mul_le_mul_of_nonneg_left hVpowW (by norm_num))
      _ ≤ 64 * W ^ 6 := by nlinarith [pow_nonneg hW 6]
      _ = (2 * W) ^ 6 := by ring
  have hroot :
      |friedlanderIwaniecJacobiBilinear alpha beta M N| ≤ 2 * W :=
    le_of_pow_le_pow_left₀ (by norm_num : (6 : ℕ) ≠ 0)
      (mul_nonneg (by norm_num) hW) htargetPow
  calc
    |friedlanderIwaniecJacobiBilinear alpha beta M N| ≤ 2 * W := hroot
    _ = 2 * friedlanderIwaniecBilinearScale M N := by
      dsimp only [W, U, V, x, y, l, friedlanderIwaniecBilinearScale]
      ring

end

end PellPaper
