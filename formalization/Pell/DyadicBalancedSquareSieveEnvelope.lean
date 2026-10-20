import Pell.DyadicBalancedSquareSieveScale
import Pell.DyadicResidualFullCellEnvelopeSum

/-!
# The full-cell envelope at the balanced square-sieve scale

This module evaluates the explicit full-cell square-sieve envelope at the
positive natural ceiling of `(UV/M)^(1/4)`.  The ceiling loss, fourth-root
identities, and conversion to the manuscript's
`sqrt(UVM) + U + V` shape are all recorded explicitly.
-/

namespace PellPaper

noncomputable section

/-- The fourth power of the real balanced scale recovers its defining
quotient exactly. -/
theorem dyadicBalancedSquareSieveRealScale_pow_four
    (i : ℕ × ℕ × ℕ × ℕ) (M : ℕ) :
    dyadicBalancedSquareSieveRealScale i M ^ 4 =
      (((2 ^ i.2.2.1 : ℕ) : ℝ) * ((2 ^ i.2.2.2 : ℕ) : ℝ)) / (M : ℝ) := by
  rw [dyadicBalancedSquareSieveRealScale]
  have hx : 0 ≤
      (((2 ^ i.2.2.1 : ℕ) : ℝ) * ((2 ^ i.2.2.2 : ℕ) : ℝ)) / (M : ℝ) := by
    positivity
  convert Real.rpow_inv_natCast_pow (n := 4) hx (by norm_num) using 1
  all_goals norm_num

/-- Squaring the real fourth-root scale gives the square root of the same
quotient. -/
theorem dyadicBalancedSquareSieveRealScale_sq
    (i : ℕ × ℕ × ℕ × ℕ) (M : ℕ) :
    dyadicBalancedSquareSieveRealScale i M ^ 2 =
      Real.sqrt
        ((((2 ^ i.2.2.1 : ℕ) : ℝ) * ((2 ^ i.2.2.2 : ℕ) : ℝ)) /
          (M : ℝ)) := by
  rw [dyadicBalancedSquareSieveRealScale, Real.sqrt_eq_rpow,
    ← Real.rpow_two]
  have hx : 0 ≤
      (((2 ^ i.2.2.1 : ℕ) : ℝ) * ((2 ^ i.2.2.2 : ℕ) : ℝ)) / (M : ℝ) := by
    positivity
  rw [← Real.rpow_mul hx]
  congr 1
  norm_num

/-- Multiplying the squared real scale by `M` gives the geometric square
root occurring in the summed reciprocal-minimum bound. -/
theorem natCast_mul_dyadicBalancedSquareSieveRealScale_sq
    (i : ℕ × ℕ × ℕ × ℕ) (M : ℕ) (hM : 0 < M) :
    (M : ℝ) * dyadicBalancedSquareSieveRealScale i M ^ 2 =
      Real.sqrt
        (((2 ^ i.2.2.1 : ℕ) : ℝ) * ((2 ^ i.2.2.2 : ℕ) : ℝ) * (M : ℝ)) := by
  let U : ℝ := ((2 ^ i.2.2.1 : ℕ) : ℝ)
  let V : ℝ := ((2 ^ i.2.2.2 : ℕ) : ℝ)
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hidentity : U * V * (M : ℝ) =
      (M : ℝ) ^ 2 * (U * V / (M : ℝ)) := by
    field_simp [hMr.ne']
  rw [dyadicBalancedSquareSieveRealScale_sq]
  change (M : ℝ) * Real.sqrt (U * V / (M : ℝ)) =
    Real.sqrt (U * V * (M : ℝ))
  rw [hidentity, Real.sqrt_mul (sq_nonneg (M : ℝ)),
    Real.sqrt_sq hMr.le]

/-- Once the real scale is at least two, the positive ceiling is bounded by
the square of the real scale.  This form absorbs both the ceiling and one
power of the fourth root. -/
theorem dyadicBalancedSquareSieveScale_le_realScale_sq
    (i : ℕ × ℕ × ℕ × ℕ) (M : ℕ)
    (hscale : 2 ≤ dyadicBalancedSquareSieveRealScale i M) :
    (dyadicBalancedSquareSieveScale i M : ℝ) ≤
      dyadicBalancedSquareSieveRealScale i M ^ 2 := by
  have hceil := dyadicBalancedSquareSieveScale_le_realScale_add_one i M
  have hprod : 0 ≤
      (dyadicBalancedSquareSieveRealScale i M - 2) *
        (dyadicBalancedSquareSieveRealScale i M + 1) := by
    positivity
  nlinarith

/-- The ceiling scale absorbs one factor of `M` into the geometric
square-root term once the real fourth-root scale is at least two. -/
theorem natCast_mul_dyadicBalancedSquareSieveScale_le_sqrt
    (i : ℕ × ℕ × ℕ × ℕ) (M : ℕ) (hM : 0 < M)
    (hscale : 2 ≤ dyadicBalancedSquareSieveRealScale i M) :
    (M : ℝ) * (dyadicBalancedSquareSieveScale i M : ℝ) ≤
      Real.sqrt
        (((2 ^ i.2.2.1 : ℕ) : ℝ) * ((2 ^ i.2.2.2 : ℕ) : ℝ) * (M : ℝ)) := by
  calc
    (M : ℝ) * (dyadicBalancedSquareSieveScale i M : ℝ) ≤
        (M : ℝ) * dyadicBalancedSquareSieveRealScale i M ^ 2 :=
      mul_le_mul_of_nonneg_left
        (dyadicBalancedSquareSieveScale_le_realScale_sq i M hscale)
        (by positivity)
    _ = Real.sqrt
        (((2 ^ i.2.2.1 : ℕ) : ℝ) * ((2 ^ i.2.2.2 : ℕ) : ℝ) * (M : ℝ)) :=
      natCast_mul_dyadicBalancedSquareSieveRealScale_sq i M hM

/-- Two natural-scale factors times the geometric square root dominate the
endpoint product.  This is the exact fourth-root identity behind the
prime-density part of the balanced envelope. -/
theorem dyadicEndpointProduct_le_balancedSquareSieveScale_sq_mul_sqrt
    (i : ℕ × ℕ × ℕ × ℕ) (M : ℕ) (hM : 0 < M) :
    ((2 ^ i.2.2.1 : ℕ) : ℝ) * ((2 ^ i.2.2.2 : ℕ) : ℝ) ≤
      (dyadicBalancedSquareSieveScale i M : ℝ) ^ 2 *
        Real.sqrt
          (((2 ^ i.2.2.1 : ℕ) : ℝ) * ((2 ^ i.2.2.2 : ℕ) : ℝ) * (M : ℝ)) := by
  let U : ℝ := ((2 ^ i.2.2.1 : ℕ) : ℝ)
  let V : ℝ := ((2 ^ i.2.2.2 : ℕ) : ℝ)
  let R : ℝ := dyadicBalancedSquareSieveRealScale i M
  let N : ℕ := dyadicBalancedSquareSieveScale i M
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hR0 : 0 ≤ R := by
    dsimp [R, dyadicBalancedSquareSieveRealScale]
    positivity
  have hN0 : 0 ≤ (N : ℝ) := by positivity
  have hRleN : R ≤ (N : ℝ) := by
    simpa only [R, N] using dyadicBalancedSquareSieveRealScale_le_natScale i M
  have hR2N2 : R ^ 2 ≤ (N : ℝ) ^ 2 := by
    have hprod : 0 ≤ ((N : ℝ) - R) * ((N : ℝ) + R) :=
      mul_nonneg (sub_nonneg.mpr hRleN) (add_nonneg hN0 hR0)
    nlinarith
  have hR4 : R ^ 4 = U * V / (M : ℝ) := by
    simpa only [R, U, V] using dyadicBalancedSquareSieveRealScale_pow_four i M
  have hR4M : R ^ 4 * (M : ℝ) = U * V :=
    (eq_div_iff hMr.ne').mp hR4
  have hMR2 : (M : ℝ) * R ^ 2 = Real.sqrt (U * V * (M : ℝ)) := by
    simpa only [R, U, V] using
      natCast_mul_dyadicBalancedSquareSieveRealScale_sq i M hM
  have hidentity : U * V = R ^ 2 * Real.sqrt (U * V * (M : ℝ)) := by
    calc
      U * V = R ^ 4 * (M : ℝ) := hR4M.symm
      _ = R ^ 2 * ((M : ℝ) * R ^ 2) := by ring
      _ = R ^ 2 * Real.sqrt (U * V * (M : ℝ)) := by rw [hMR2]
  calc
    U * V = R ^ 2 * Real.sqrt (U * V * (M : ℝ)) := hidentity
    _ ≤ (N : ℝ) ^ 2 * Real.sqrt (U * V * (M : ℝ)) :=
      mul_le_mul_of_nonneg_right hR2N2 (Real.sqrt_nonneg _)

private theorem balancedEnvelope_linearPiece_le
    (U V M N T : ℝ)
    (hM : 0 < M) (hN : 0 < N)
    (hcoefficient : (4608 : ℝ) / Real.log 2 ≤ 9216)
    (hpiece0 : 0 ≤ U * V * Real.log N / N)
    (hpiece : U * V * Real.log N / N ≤ T)
    (hT0 : 0 ≤ T) :
    (1348 * M) *
        ((4608 / Real.log 2) * (U * V / M) * Real.log N / N) ≤
      13000000 * T := by
  calc
    (1348 * M) *
        ((4608 / Real.log 2) * (U * V / M) * Real.log N / N) =
        (1348 * (4608 / Real.log 2)) *
          (U * V * Real.log N / N) := by
      field_simp [hM.ne', hN.ne']
    _ ≤ (1348 * 9216) * (U * V * Real.log N / N) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcoefficient (by norm_num)) hpiece0
    _ ≤ (1348 * 9216) * T :=
      mul_le_mul_of_nonneg_left hpiece (by norm_num)
    _ ≤ 13000000 * T :=
      mul_le_mul_of_nonneg_right (by norm_num) hT0

private theorem balancedEnvelope_degreePiece_le
    (M N d L G S : ℝ)
    (hN0 : 0 ≤ N)
    (hG0 : 0 ≤ G) (hS0 : 0 ≤ S)
    (hMN : M * N ≤ S) (hSleGS : S ≤ G * S) :
    (1348 * M) * (64 * d ^ 2 * N ^ 2 * L ^ 2) ≤
      100000 * (d ^ 2 * L ^ 2 * G * N * S) := by
  let C : ℝ := 86272 * d ^ 2 * L ^ 2 * N
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hcore0 : 0 ≤ d ^ 2 * L ^ 2 * G * N * S := by positivity
  calc
    (1348 * M) * (64 * d ^ 2 * N ^ 2 * L ^ 2) = C * (M * N) := by
      dsimp [C]
      ring
    _ ≤ C * S := mul_le_mul_of_nonneg_left hMN hC0
    _ ≤ C * (G * S) := mul_le_mul_of_nonneg_left hSleGS hC0
    _ = 86272 * (d ^ 2 * L ^ 2 * G * N * S) := by
      dsimp [C]
      ring
    _ ≤ 100000 * (d ^ 2 * L ^ 2 * G * N * S) :=
      mul_le_mul_of_nonneg_right (by norm_num) hcore0

private theorem balancedEnvelope_reciprocalPiece_le
    (N d L G S : ℝ)
    (hN0 : 0 ≤ N) (hNone : 1 ≤ N)
    (hdSqOne : 1 ≤ d ^ 2) (hLsq : L ≤ L ^ 2)
    (hG0 : 0 ≤ G) (hS0 : 0 ≤ S) :
    (768 * N * L + 96 * d ^ 2 * L) * (21568 * S * G) ≤
      22000000 * (d ^ 2 * L ^ 2 * G * N * S) := by
  have hLleL2N : L ≤ L ^ 2 * N := by
    calc
      L ≤ L ^ 2 := hLsq
      _ = L ^ 2 * 1 := by ring
      _ ≤ L ^ 2 * N := mul_le_mul_of_nonneg_left hNone (sq_nonneg L)
  have hLdegree : L ≤ d ^ 2 * L ^ 2 := by
    calc
      L ≤ L ^ 2 := hLsq
      _ = 1 * L ^ 2 := by ring
      _ ≤ d ^ 2 * L ^ 2 :=
        mul_le_mul_of_nonneg_right hdSqOne (sq_nonneg L)
  have hfirst : 768 * N * L ≤ 768 * d ^ 2 * L ^ 2 * N := by
    calc
      768 * N * L ≤ 768 * N * (d ^ 2 * L ^ 2) :=
        mul_le_mul_of_nonneg_left hLdegree
          (mul_nonneg (by norm_num) hN0)
      _ = 768 * d ^ 2 * L ^ 2 * N := by ring
  have hsecond : 96 * d ^ 2 * L ≤ 96 * d ^ 2 * L ^ 2 * N := by
    calc
      96 * d ^ 2 * L ≤ (96 * d ^ 2) * (L ^ 2 * N) :=
        mul_le_mul_of_nonneg_left hLleL2N
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 96) (sq_nonneg d))
      _ = 96 * d ^ 2 * L ^ 2 * N := by ring
  have hcore0 : 0 ≤ d ^ 2 * L ^ 2 * N := by positivity
  have hcoefficient : 768 * N * L + 96 * d ^ 2 * L ≤
      1000 * d ^ 2 * L ^ 2 * N := by
    calc
      768 * N * L + 96 * d ^ 2 * L ≤
          768 * d ^ 2 * L ^ 2 * N + 96 * d ^ 2 * L ^ 2 * N :=
        add_le_add hfirst hsecond
      _ = 864 * (d ^ 2 * L ^ 2 * N) := by ring
      _ ≤ 1000 * (d ^ 2 * L ^ 2 * N) :=
        mul_le_mul_of_nonneg_right (by norm_num) hcore0
      _ = 1000 * d ^ 2 * L ^ 2 * N := by ring_nf
  have hSG0 : 0 ≤ 21568 * S * G := by positivity
  have htotal0 : 0 ≤ d ^ 2 * L ^ 2 * G * N * S := by positivity
  calc
    (768 * N * L + 96 * d ^ 2 * L) * (21568 * S * G) ≤
        (1000 * d ^ 2 * L ^ 2 * N) * (21568 * S * G) :=
      mul_le_mul_of_nonneg_right hcoefficient hSG0
    _ = 21568000 * (d ^ 2 * L ^ 2 * G * N * S) := by ring
    _ ≤ 22000000 * (d ^ 2 * L ^ 2 * G * N * S) :=
      mul_le_mul_of_nonneg_right (by norm_num) htotal0

/-- At the balanced fourth-root sieve scale, the complete summed full-cell
envelope has the manuscript's square-root shape.  The constant is absolute
and intentionally coarse; all degree and logarithmic dependence remains
visible. -/
theorem fullCellOddDegreeSieveAggregateEnvelope_balancedScale_le
    (D : ℕ) (i : ℕ × ℕ × ℕ × ℕ) (M : ℕ)
    (hM : 0 < M)
    (hproduct : (M : ℝ) ≤
      ((2 ^ i.2.2.1 : ℕ) : ℝ) * ((2 ^ i.2.2.2 : ℕ) : ℝ))
    (hscale : 2 ≤ dyadicBalancedSquareSieveRealScale i M) :
    let U : ℝ := ((2 ^ i.2.2.1 : ℕ) : ℝ)
    let V : ℝ := ((2 ^ i.2.2.2 : ℕ) : ℝ)
    let N : ℕ := dyadicBalancedSquareSieveScale i M
    let L : ℝ := 1 + Real.log (16 * (N : ℝ) ^ 2)
    let G : ℝ := 1 + Real.log
      (1 + U / Real.sqrt (U * V / (M : ℝ)))
    fullCellOddDegreeSieveAggregateEnvelope N D U V (M : ℝ) ≤
      40000000 * ((D : ℝ) + 1) ^ 2 * L ^ 2 * G * (N : ℝ) *
        (Real.sqrt (U * V * (M : ℝ)) + U + V) := by
  dsimp only
  let U : ℝ := ((2 ^ i.2.2.1 : ℕ) : ℝ)
  let V : ℝ := ((2 ^ i.2.2.2 : ℕ) : ℝ)
  let N : ℕ := dyadicBalancedSquareSieveScale i M
  let L : ℝ := 1 + Real.log (16 * (N : ℝ) ^ 2)
  let G : ℝ := 1 + Real.log
    (1 + U / Real.sqrt (U * V / (M : ℝ)))
  let S : ℝ := Real.sqrt (U * V * (M : ℝ)) + U + V
  let d : ℝ := (D : ℝ) + 1
  let T : ℝ := d ^ 2 * L ^ 2 * G * (N : ℝ) * S
  change fullCellOddDegreeSieveAggregateEnvelope N D U V (M : ℝ) ≤
    40000000 * d ^ 2 * L ^ 2 * G * (N : ℝ) * S
  have hU : 0 < U := by dsimp [U]; positivity
  have hV : 0 < V := by dsimp [V]; positivity
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hUV : 0 < U * V := mul_pos hU hV
  have hx : 0 < U * V / (M : ℝ) := div_pos hUV hMr
  have hxone : 1 ≤ U * V / (M : ℝ) := by
    apply (le_div_iff₀ hMr).2
    simpa only [one_mul, U, V] using hproduct
  have hNnat : 0 < N := by
    dsimp [N]
    exact positiveNatCeil_pos _
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hNnat
  have hNone : (1 : ℝ) ≤ N := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hNnat.ne')
  have hS0 : 0 ≤ S := by dsimp [S]; positivity
  have hsqrtS : Real.sqrt (U * V * (M : ℝ)) ≤ S := by
    dsimp [S]
    linarith [hU.le, hV.le]
  have hUVNS : U * V ≤ (N : ℝ) ^ 2 * S := by
    calc
      U * V ≤ (N : ℝ) ^ 2 * Real.sqrt (U * V * (M : ℝ)) := by
        simpa only [U, V, N] using
          dyadicEndpointProduct_le_balancedSquareSieveScale_sq_mul_sqrt i M hM
      _ ≤ (N : ℝ) ^ 2 * S :=
        mul_le_mul_of_nonneg_left hsqrtS (sq_nonneg (N : ℝ))
  have hMN : (M : ℝ) * (N : ℝ) ≤ S := by
    calc
      (M : ℝ) * (N : ℝ) ≤ Real.sqrt (U * V * (M : ℝ)) := by
        simpa only [U, V, N] using
          natCast_mul_dyadicBalancedSquareSieveScale_le_sqrt i M hM hscale
      _ ≤ S := hsqrtS
  have hargOne : (1 : ℝ) ≤ 16 * (N : ℝ) ^ 2 := by
    nlinarith [mul_nonneg hNpos.le (sub_nonneg.mpr hNone)]
  have hLone : 1 ≤ L := by
    dsimp [L]
    exact le_add_of_nonneg_right (Real.log_nonneg hargOne)
  have hL0 : 0 ≤ L := zero_le_one.trans hLone
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hNone
  have hNarg : (N : ℝ) ≤ 16 * (N : ℝ) ^ 2 := by
    nlinarith [mul_nonneg hNpos.le (sub_nonneg.mpr hNone)]
  have hlogNarg : Real.log (N : ℝ) ≤
      Real.log (16 * (N : ℝ) ^ 2) := Real.log_le_log hNpos hNarg
  have hlogNL : Real.log (N : ℝ) ≤ L := by
    dsimp [L]
    linarith
  have hsqrtxOne : 1 ≤ Real.sqrt (U * V / (M : ℝ)) :=
    Real.one_le_sqrt.mpr hxone
  have hsqrtx : 0 < Real.sqrt (U * V / (M : ℝ)) :=
    lt_of_lt_of_le zero_lt_one hsqrtxOne
  have hratio0 : 0 ≤ U / Real.sqrt (U * V / (M : ℝ)) := by positivity
  have hGone : 1 ≤ G := by
    dsimp [G]
    exact le_add_of_nonneg_right
      (Real.log_nonneg (show 1 ≤ 1 + U / Real.sqrt (U * V / (M : ℝ)) by
        linarith))
  have hG0 : 0 ≤ G := zero_le_one.trans hGone
  have hD0 : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
  have hdOne : 1 ≤ d := by
    dsimp [d]
    linarith
  have hd0 : 0 ≤ d := (by norm_num : (0 : ℝ) ≤ 1).trans hdOne
  have hdSqOne : 1 ≤ d ^ 2 := by
    have hprodD : 0 ≤ (d - 1) * (d + 1) := by positivity
    nlinarith
  have hLsq : L ≤ L ^ 2 := by
    have hprodL : 0 ≤ L * (L - 1) :=
      mul_nonneg hL0 (sub_nonneg.mpr hLone)
    nlinarith
  have hSleGS : S ≤ G * S := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hGone) hS0]
  have hLfactor : L ≤ d ^ 2 * L ^ 2 * G := by
    calc
      L ≤ L ^ 2 := hLsq
      _ = 1 * L ^ 2 * 1 := by ring
      _ ≤ d ^ 2 * L ^ 2 * G := by gcongr
  have hT0 : 0 ≤ T := by dsimp [T]; positivity
  have hbaseLinear :
      U * V * Real.log (N : ℝ) / (N : ℝ) ≤ T := by
    have hproductLog : U * V * Real.log (N : ℝ) ≤
        ((N : ℝ) ^ 2 * S) * L :=
      mul_le_mul hUVNS hlogNL hlogN
        (mul_nonneg (sq_nonneg (N : ℝ)) hS0)
    have hfirst : U * V * Real.log (N : ℝ) / (N : ℝ) ≤
        (N : ℝ) * S * L := by
      apply (div_le_iff₀ hNpos).2
      calc
        U * V * Real.log (N : ℝ) ≤ ((N : ℝ) ^ 2 * S) * L := hproductLog
        _ = ((N : ℝ) * S * L) * (N : ℝ) := by ring
    calc
      U * V * Real.log (N : ℝ) / (N : ℝ) ≤
          (N : ℝ) * S * L := hfirst
      _ ≤ (N : ℝ) * S * (d ^ 2 * L ^ 2 * G) :=
        mul_le_mul_of_nonneg_left hLfactor (mul_nonneg hNpos.le hS0)
      _ = T := by dsimp [T]; ring
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogTwoHalf : (1 : ℝ) / 2 ≤ Real.log 2 := by
    exact (by norm_num : (1 : ℝ) / 2 ≤ 0.6931471803).trans
      Real.log_two_gt_d9.le
  have hcoefficient : (4608 : ℝ) / Real.log 2 ≤ 9216 := by
    apply (div_le_iff₀ hlogTwo).2
    linarith
  have hbaseLinear0 :
      0 ≤ U * V * Real.log (N : ℝ) / (N : ℝ) := by positivity
  have hlinearTerm :
      (1348 * (M : ℝ)) *
          ((4608 / Real.log 2) * (U * V / (M : ℝ)) *
            Real.log (N : ℝ) / (N : ℝ)) ≤
        13000000 * T := by
    exact balancedEnvelope_linearPiece_le U V (M : ℝ) (N : ℝ) T
      hMr hNpos hcoefficient hbaseLinear0 hbaseLinear hT0
  have hdegreeTerm :
      (1348 * (M : ℝ)) *
          (64 * d ^ 2 * (N : ℝ) ^ 2 * L ^ 2) ≤
        100000 * T := by
    simpa only [T] using balancedEnvelope_degreePiece_le
      (M : ℝ) (N : ℝ) d L G S hNpos.le hG0 hS0 hMN hSleGS
  have hreciprocalTerm :
      (768 * (N : ℝ) * L + 96 * d ^ 2 * L) *
          (21568 * S * G) ≤
        22000000 * T := by
    simpa only [T] using balancedEnvelope_reciprocalPiece_le
      (N : ℝ) d L G S hNpos.le hNone hdSqOne hLsq hG0 hS0
  rw [fullCellOddDegreeSieveAggregateEnvelope]
  change
    (1348 * (M : ℝ)) *
        ((4608 / Real.log 2) * (U * V / (M : ℝ)) *
            Real.log (N : ℝ) / (N : ℝ) +
          64 * d ^ 2 * (N : ℝ) ^ 2 * L ^ 2) +
      (768 * (N : ℝ) * L + 96 * d ^ 2 * L) *
        (21568 * S * G) ≤
      40000000 * d ^ 2 * L ^ 2 * G * (N : ℝ) * S
  calc
    (1348 * (M : ℝ)) *
          ((4608 / Real.log 2) * (U * V / (M : ℝ)) *
              Real.log (N : ℝ) / (N : ℝ) +
            64 * d ^ 2 * (N : ℝ) ^ 2 * L ^ 2) +
        (768 * (N : ℝ) * L + 96 * d ^ 2 * L) *
          (21568 * S * G) =
        (1348 * (M : ℝ)) *
            ((4608 / Real.log 2) * (U * V / (M : ℝ)) *
              Real.log (N : ℝ) / (N : ℝ)) +
          (1348 * (M : ℝ)) *
            (64 * d ^ 2 * (N : ℝ) ^ 2 * L ^ 2) +
          (768 * (N : ℝ) * L + 96 * d ^ 2 * L) *
            (21568 * S * G) := by ring
    _ ≤ 13000000 * T + 100000 * T + 22000000 * T :=
      add_le_add (add_le_add hlinearTerm hdegreeTerm) hreciprocalTerm
    _ = 35100000 * T := by ring
    _ ≤ 40000000 * T :=
      mul_le_mul_of_nonneg_right (by norm_num) hT0
    _ = 40000000 * d ^ 2 * L ^ 2 * G * (N : ℝ) * S := by
      dsimp [T]
      ring

end

end PellPaper
