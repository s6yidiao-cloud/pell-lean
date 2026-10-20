import Pell.Main3BalancedRangeThreshold
import Pell.UnbalancedShiftedSquareDyadicCover
import Mathlib.Tactic

/-!
# Exact parameters at the enlarged main3 unbalanced Pell exponent

At the natural main3 threshold

`R = ceil (Y^(1/(100*theta^2)))`,

a nonempty fixed `(h,v,D,N)` fibre retains the admissible squarefree shift
`a = -h*v`, exact half-open blocks for `d` and `n=e*v`, and the product
window `Y <= u*v < 2Y`.  This file turns those facts into explicit shift,
height, and scale-comparison packages.  All constants are retained; no
uniform shifted-square estimate or asymptotic absorption is asserted.
-/

namespace PellPaper

noncomputable section

/-- A nonempty main3 cover cell has an exact source witness, including the
signed equation, admissible shift, factor-height bounds, product window, and
both half-open dyadic blocks. -/
theorem nonempty_main3UnbalancedEnlargedShiftedSquareCell_witness
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (hi : (h, v, D, N) ∈ unbalancedShiftedSquareDyadicCoverIndices
      (theta + 1 / 4) Y (main3BalancedR theta Y))
    (hcell : (unbalancedShiftedSquareDyadicCoverCell
      (theta + 1 / 4) Y (main3BalancedR theta Y) (h, v, D, N)).Nonempty) :
    IsSignedDyadicDifference h ∧
      1 ≤ v ∧ v < main3BalancedR theta Y ∧
      ∃ d e u : ℕ,
        0 < d ∧ 0 < e ∧ 0 < u ∧
        d ≤ dyadicFactorHeight (theta + 1 / 4) Y ∧
        e ≤ dyadicFactorHeight (theta + 1 / 4) Y ∧
        Y ≤ u * v ∧ u * v < 2 * Y ∧
        (e : ℤ) ^ 2 * v - (d : ℤ) ^ 2 * u = h ∧
        ShiftAdmissible h v ∧
        D ≤ d ∧ d < 2 * D ∧
        N ≤ e * v ∧ e * v < 2 * N := by
  have hi' := mem_unbalancedShiftedSquareDyadicCoverIndices.mp hi
  obtain ⟨⟨d, e, u, v'⟩, hp⟩ := hcell
  change (d, e, u, v') ∈ admissibleUnbalancedShiftedSquareFibre
    (theta + 1 / 4) Y (main3BalancedR theta Y) h v D N at hp
  obtain ⟨hcond, _hvR, ⟨h', _hh', hdiff', hadmissible⟩,
      hvEq, hdiff, hDlo, hDhi, hNlo, hNhi⟩ :=
    mem_admissibleUnbalancedShiftedSquareFibre.mp hp
  subst v'
  have hhEq : h' = h := by linarith
  have hadmissible' : ShiftAdmissible h v := by
    simpa only [hhEq] using hadmissible
  obtain ⟨hd, he, hu, _hv, hdH, heH, _huH, _hvH,
      _hsu, _hsv, _hcop, hYuv, huvY, _hvu, _hvSq,
      _hsign, _hheight⟩ := hcond
  exact ⟨hi'.1, hi'.2.1, hi'.2.2.1, d, e, u,
    hd, he, hu, hdH, heH, hYuv, huvY, hdiff, hadmissible',
    hDlo, hDhi, hNlo, hNhi⟩

/-- The nonempty-cell witness supplies exactly the arithmetic hypotheses on
the fixed shift required by the future unbalanced analysis. -/
theorem nonempty_main3UnbalancedEnlargedShiftedSquareCell_shift_package
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (hi : (h, v, D, N) ∈ unbalancedShiftedSquareDyadicCoverIndices
      (theta + 1 / 4) Y (main3BalancedR theta Y))
    (hcell : (unbalancedShiftedSquareDyadicCoverCell
      (theta + 1 / 4) Y (main3BalancedR theta Y) (h, v, D, N)).Nonempty) :
    ShiftAdmissible h v ∧
      Squarefree (shiftedSquareA h v) ∧
      shiftedSquareA h v ≠ 0 ∧ shiftedSquareA h v ≠ -1 := by
  obtain ⟨_hh, _hvone, _hvR, d, e, u, _hd, _he, _hu,
      _hdH, _heH, _hYuv, _huvY, _hdiff, hadmissible,
      _hDlo, _hDhi, _hNlo, _hNhi⟩ :=
    nonempty_main3UnbalancedEnlargedShiftedSquareCell_witness hi hcell
  exact ⟨hadmissible, hadmissible.1, hadmissible.1.ne_zero,
    hadmissible.2⟩

/-- An active index has the sharp shift-size bounds furnished by the strict
inequality `v < ceil(Y^delta)`.  The final comparison explicitly uses
`main3BalancedR <= Y`. -/
theorem main3UnbalancedEnlargedShiftedSquareIndex_shift_abs_bounds
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 2 ≤ Y)
    (hi : (h, v, D, N) ∈ unbalancedShiftedSquareDyadicCoverIndices
      (theta + 1 / 4) Y (main3BalancedR theta Y)) :
    |(shiftedSquareA h v : ℝ)| <
        2 * (main3BalancedR theta Y : ℝ) ∧
      |(shiftedSquareA h v : ℝ)| <
        2 * (Y : ℝ) ^ main3BalancedRExponent theta ∧
      |(shiftedSquareA h v : ℝ)| < 2 * (Y : ℝ) := by
  have hi' := mem_unbalancedShiftedSquareDyadicCoverIndices.mp hi
  have habsInt : |shiftedSquareA h v| ≤ 2 * (v : ℤ) :=
    shiftedSquareA_abs_le_two_mul (v := v) hi'.1
  have habs : |(shiftedSquareA h v : ℝ)| ≤ 2 * (v : ℝ) := by
    exact_mod_cast habsInt
  have hvR : (v : ℝ) < (main3BalancedR theta Y : ℝ) := by
    exact_mod_cast hi'.2.2.1
  have hvPower : (v : ℝ) <
      (Y : ℝ) ^ main3BalancedRExponent theta := by
    have hvCeil := hi'.2.2.1
    rw [main3BalancedR, powerRootCeilEndpoint, Nat.lt_ceil] at hvCeil
    exact hvCeil
  have hRYnat : main3BalancedR theta Y ≤ Y :=
    (main3BalancedR_parameter_package theta Y htheta hY).2.2.2
  have hRY : (main3BalancedR theta Y : ℝ) ≤ (Y : ℝ) := by
    exact_mod_cast hRYnat
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

/-- The exact source blocks yield positive endpoints and direct height bounds.
The bound for `N` is strict because `e <= height`, `height > 0`, and `v<R`.
-/
theorem nonempty_main3UnbalancedEnlargedShiftedSquareCell_endpoint_height_package
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 2 ≤ Y)
    (hi : (h, v, D, N) ∈ unbalancedShiftedSquareDyadicCoverIndices
      (theta + 1 / 4) Y (main3BalancedR theta Y))
    (hcell : (unbalancedShiftedSquareDyadicCoverCell
      (theta + 1 / 4) Y (main3BalancedR theta Y) (h, v, D, N)).Nonempty) :
    0 < D ∧ 0 < N ∧
      D ≤ dyadicFactorHeight (theta + 1 / 4) Y ∧
      N < dyadicFactorHeight (theta + 1 / 4) Y * main3BalancedR theta Y ∧
      N < dyadicFactorHeight (theta + 1 / 4) Y * Y := by
  obtain ⟨_hh, _hvone, hvR, d, e, u, hd, he, _hu,
      hdH, heH, _hYuv, _huvY, _hdiff, _hadmissible,
      hDlo, hDhi, hNlo, hNhi⟩ :=
    nonempty_main3UnbalancedEnlargedShiftedSquareCell_witness hi hcell
  have hHeight : 0 < dyadicFactorHeight (theta + 1 / 4) Y := hd.trans_le hdH
  have hevPos : 0 < e * v := Nat.mul_pos he (by omega)
  have hDpos : 0 < D := by omega
  have hNpos : 0 < N := by omega
  have hev_le : e * v ≤ dyadicFactorHeight (theta + 1 / 4) Y * v :=
    Nat.mul_le_mul_right v heH
  have hheight_vR :
      dyadicFactorHeight (theta + 1 / 4) Y * v <
        dyadicFactorHeight (theta + 1 / 4) Y * main3BalancedR theta Y :=
    mul_lt_mul_of_pos_left hvR hHeight
  have hNheightR :
      N < dyadicFactorHeight (theta + 1 / 4) Y * main3BalancedR theta Y :=
    hNlo.trans_lt (hev_le.trans_lt hheight_vR)
  have hRY : main3BalancedR theta Y ≤ Y :=
    (main3BalancedR_parameter_package theta Y htheta hY).2.2.2
  have hheightRY :
      dyadicFactorHeight (theta + 1 / 4) Y * main3BalancedR theta Y ≤
        dyadicFactorHeight (theta + 1 / 4) Y * Y := Nat.mul_le_mul_left _ hRY
  exact ⟨hDpos, hNpos, hDlo.trans hdH, hNheightR,
    hNheightR.trans_le hheightRY⟩

/-- Every active source cell produces a nonempty exact squarefree-`w`
shifted-square block with the same `(a,D,Y,N)` parameters. -/
theorem nonempty_main3UnbalancedEnlargedShiftedSquareCell_block_nonempty
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (hcell : (unbalancedShiftedSquareDyadicCoverCell
      (theta + 1 / 4) Y (main3BalancedR theta Y) (h, v, D, N)).Nonempty) :
    (squarefreeShiftedSquareBlock (shiftedSquareA h v) D Y N).Nonempty := by
  obtain ⟨p, hp⟩ := hcell
  change p ∈ admissibleUnbalancedShiftedSquareFibre
    (theta + 1 / 4) Y (main3BalancedR theta Y) h v D N at hp
  exact ⟨shiftedSquareTupleMap p,
    shiftedSquareTupleMap_mem_squarefreeShiftedSquareBlock hp⟩

/-- Exact squared scale comparisons before any large-`N` absorption.  The
additive `2R` terms are the retained cost of `|a| <= 2v < 2R`. -/
theorem nonempty_main3UnbalancedEnlargedShiftedSquareCell_squared_scale_bounds
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (hi : (h, v, D, N) ∈ unbalancedShiftedSquareDyadicCoverIndices
      (theta + 1 / 4) Y (main3BalancedR theta Y))
    (hcell : (unbalancedShiftedSquareDyadicCoverCell
      (theta + 1 / 4) Y (main3BalancedR theta Y) (h, v, D, N)).Nonempty) :
    (D : ℝ) ^ 2 * (Y : ℝ) ≤
        4 * (N : ℝ) ^ 2 + 2 * (main3BalancedR theta Y : ℝ) ∧
      (N : ℝ) ^ 2 ≤
        8 * (D : ℝ) ^ 2 * (Y : ℝ) +
          2 * (main3BalancedR theta Y : ℝ) := by
  obtain ⟨hh, _hvone, hvR, d, e, u, _hd, _he, _hu,
      _hdH, _heH, hYuv, huvY, hdiff, _hadmissible,
      hDlo, hDhi, hNlo, hNhi⟩ :=
    nonempty_main3UnbalancedEnlargedShiftedSquareCell_witness hi hcell
  have heqInt := shifted_square_integer_identity hdiff
  have heq :
      (d : ℝ) ^ 2 * ((u * v : ℕ) : ℝ) =
        ((e * v : ℕ) : ℝ) ^ 2 + (shiftedSquareA h v : ℝ) := by
    exact_mod_cast heqInt
  have habsInt : |shiftedSquareA h v| ≤ 2 * (v : ℤ) :=
    shiftedSquareA_abs_le_two_mul (v := v) hh
  have habsV : |(shiftedSquareA h v : ℝ)| ≤ 2 * (v : ℝ) := by
    exact_mod_cast habsInt
  have hvRreal : (v : ℝ) ≤ (main3BalancedR theta Y : ℝ) := by
    exact_mod_cast (Nat.le_of_lt hvR)
  have habsR : |(shiftedSquareA h v : ℝ)| ≤
      2 * (main3BalancedR theta Y : ℝ) := by
    nlinarith
  have haUpper : (shiftedSquareA h v : ℝ) ≤
      2 * (main3BalancedR theta Y : ℝ) :=
    (le_abs_self _).trans habsR
  have haLower : -2 * (main3BalancedR theta Y : ℝ) ≤
      (shiftedSquareA h v : ℝ) := by
    nlinarith [neg_abs_le (shiftedSquareA h v : ℝ)]
  have hDloR : (D : ℝ) ≤ (d : ℝ) := by exact_mod_cast hDlo
  have hDhiR : (d : ℝ) ≤ 2 * (D : ℝ) := by
    exact_mod_cast (Nat.le_of_lt hDhi)
  have hNloR : (N : ℝ) ≤ ((e * v : ℕ) : ℝ) := by exact_mod_cast hNlo
  have hNhiR : ((e * v : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
    exact_mod_cast (Nat.le_of_lt hNhi)
  have hYuvR : (Y : ℝ) ≤ ((u * v : ℕ) : ℝ) := by exact_mod_cast hYuv
  have huvYR : ((u * v : ℕ) : ℝ) ≤ 2 * (Y : ℝ) := by
    exact_mod_cast (Nat.le_of_lt huvY)
  have hdSqLower : (D : ℝ) ^ 2 ≤ (d : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hDloR 2
  have hdSqUpper : (d : ℝ) ^ 2 ≤ (2 * (D : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hDhiR 2
  have hnSqLower : (N : ℝ) ^ 2 ≤ ((e * v : ℕ) : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hNloR 2
  have hnSqUpper : ((e * v : ℕ) : ℝ) ^ 2 ≤ (2 * (N : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hNhiR 2
  have hleftLower : (D : ℝ) ^ 2 * (Y : ℝ) ≤
      (d : ℝ) ^ 2 * ((u * v : ℕ) : ℝ) :=
    mul_le_mul hdSqLower hYuvR (by positivity) (by positivity)
  have hleftUpper : (d : ℝ) ^ 2 * ((u * v : ℕ) : ℝ) ≤
      8 * (D : ℝ) ^ 2 * (Y : ℝ) := by
    calc
      (d : ℝ) ^ 2 * ((u * v : ℕ) : ℝ) ≤
          (2 * (D : ℝ)) ^ 2 * (2 * (Y : ℝ)) :=
        mul_le_mul hdSqUpper huvYR (by positivity) (by positivity)
      _ = 8 * (D : ℝ) ^ 2 * (Y : ℝ) := by ring
  constructor
  · calc
      (D : ℝ) ^ 2 * (Y : ℝ) ≤
          (d : ℝ) ^ 2 * ((u * v : ℕ) : ℝ) := hleftLower
      _ ≤ 4 * (N : ℝ) ^ 2 + 2 * (main3BalancedR theta Y : ℝ) := by
        nlinarith
  · calc
      (N : ℝ) ^ 2 ≤ ((e * v : ℕ) : ℝ) ^ 2 := hnSqLower
      _ ≤ 8 * (D : ℝ) ^ 2 * (Y : ℝ) +
          2 * (main3BalancedR theta Y : ℝ) := by
        nlinarith

/-- Once `N^2 >= 4Y`, the additive shift cost can be absorbed with explicit
constants.  This is the honest squared form of `D` being comparable to
`N/sqrt(Y)`. -/
theorem nonempty_main3UnbalancedEnlargedShiftedSquareCell_largeN_squared_comparability
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 2 ≤ Y)
    (hi : (h, v, D, N) ∈ unbalancedShiftedSquareDyadicCoverIndices
      (theta + 1 / 4) Y (main3BalancedR theta Y))
    (hcell : (unbalancedShiftedSquareDyadicCoverCell
      (theta + 1 / 4) Y (main3BalancedR theta Y) (h, v, D, N)).Nonempty)
    (hlarge : 4 * Y ≤ N ^ 2) :
    (D : ℝ) ^ 2 * (Y : ℝ) ≤ 5 * (N : ℝ) ^ 2 ∧
      (N : ℝ) ^ 2 ≤ 16 * (D : ℝ) ^ 2 * (Y : ℝ) := by
  have hscale :=
    nonempty_main3UnbalancedEnlargedShiftedSquareCell_squared_scale_bounds hi hcell
  have hRYnat : main3BalancedR theta Y ≤ Y :=
    (main3BalancedR_parameter_package theta Y htheta hY).2.2.2
  have hRY : (main3BalancedR theta Y : ℝ) ≤ (Y : ℝ) := by
    exact_mod_cast hRYnat
  have hlargeR : 4 * (Y : ℝ) ≤ (N : ℝ) ^ 2 := by
    exact_mod_cast hlarge
  constructor <;> nlinarith [hscale.1, hscale.2]

/-- Linear explicit comparability obtained from the preceding squared bounds.
No division by `sqrt(Y)` or asymptotic notation is hidden in the statement.
-/
theorem nonempty_main3UnbalancedEnlargedShiftedSquareCell_largeN_linear_comparability
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 2 ≤ Y)
    (hi : (h, v, D, N) ∈ unbalancedShiftedSquareDyadicCoverIndices
      (theta + 1 / 4) Y (main3BalancedR theta Y))
    (hcell : (unbalancedShiftedSquareDyadicCoverCell
      (theta + 1 / 4) Y (main3BalancedR theta Y) (h, v, D, N)).Nonempty)
    (hlarge : 4 * Y ≤ N ^ 2) :
    (N : ℝ) ≤ 4 * (D : ℝ) * Real.sqrt (Y : ℝ) ∧
      (D : ℝ) * Real.sqrt (Y : ℝ) ≤
        Real.sqrt 5 * (N : ℝ) := by
  have hscale :=
    nonempty_main3UnbalancedEnlargedShiftedSquareCell_largeN_squared_comparability
      htheta hY hi hcell hlarge
  have hsqrtY : Real.sqrt (Y : ℝ) ^ 2 = (Y : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hsqrtFive : Real.sqrt (5 : ℝ) ^ 2 = 5 :=
    Real.sq_sqrt (by norm_num)
  constructor
  · apply (sq_le_sq₀ (by positivity) (by positivity)).1
    calc
      (N : ℝ) ^ 2 ≤ 16 * (D : ℝ) ^ 2 * (Y : ℝ) := hscale.2
      _ = (4 * (D : ℝ) * Real.sqrt (Y : ℝ)) ^ 2 := by
        rw [mul_pow, mul_pow, hsqrtY]
        ring
  · apply (sq_le_sq₀ (by positivity) (by positivity)).1
    calc
      ((D : ℝ) * Real.sqrt (Y : ℝ)) ^ 2 =
          (D : ℝ) ^ 2 * (Y : ℝ) := by
        rw [mul_pow, hsqrtY]
      _ ≤ 5 * (N : ℝ) ^ 2 := hscale.1
      _ = (Real.sqrt 5 * (N : ℝ)) ^ 2 := by
        rw [mul_pow, hsqrtFive]

end

end PellPaper
