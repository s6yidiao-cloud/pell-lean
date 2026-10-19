import Pell.DyadicBalancedSquareSieveEnvelope
import Pell.DyadicResidualFullCellEnvelopeSumElementary

/-!
# The elementary full-cell envelope at the balanced square-sieve scale
-/

namespace PellPaper

noncomputable section

private theorem balancedElementaryEnvelope_linearPiece_le
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


theorem fullCellElementarySieveAggregateEnvelope_balancedScale_le
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
    fullCellElementarySieveAggregateEnvelope N D U V (M : ℝ) ≤
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
  change fullCellElementarySieveAggregateEnvelope N D U V (M : ℝ) ≤
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
  let R : ℝ := dyadicBalancedSquareSieveRealScale i M
  have hRpos : 0 < R := by
    dsimp [R]
    linarith
  have hNleTwoR : (N : ℝ) ≤ 2 * R := by
    calc
      (N : ℝ) ≤ R + 1 := by
        simpa only [N, R] using
          dyadicBalancedSquareSieveScale_le_realScale_add_one i M
      _ ≤ 2 * R := by linarith
  have hNtwoSq : (N : ℝ) ^ 2 ≤ (2 * R) ^ 2 := by
    have hprod : 0 ≤ (2 * R - (N : ℝ)) * (2 * R + (N : ℝ)) := by
      positivity
    nlinarith
  have hMRsq : (M : ℝ) * R ^ 2 =
      Real.sqrt (U * V * (M : ℝ)) := by
    simpa only [R, U, V] using
      natCast_mul_dyadicBalancedSquareSieveRealScale_sq i M hM
  have hMNtwo : (M : ℝ) * (N : ℝ) ^ 2 ≤ 4 * S := by
    calc
      (M : ℝ) * (N : ℝ) ^ 2 ≤ (M : ℝ) * (2 * R) ^ 2 :=
        mul_le_mul_of_nonneg_left hNtwoSq hMr.le
      _ = 4 * ((M : ℝ) * R ^ 2) := by ring
      _ = 4 * Real.sqrt (U * V * (M : ℝ)) := by rw [hMRsq]
      _ ≤ 4 * S := mul_le_mul_of_nonneg_left hsqrtS (by norm_num)
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
  have hLsqfactor : L ^ 2 ≤ d ^ 2 * L ^ 2 * G := by
    calc
      L ^ 2 = 1 * L ^ 2 * 1 := by ring
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
    exact balancedElementaryEnvelope_linearPiece_le U V (M : ℝ) (N : ℝ) T
      hMr hNpos hcoefficient hbaseLinear0 hbaseLinear hT0
  have hdegreeGrowth : L ^ 2 * (N : ℝ) * ((M : ℝ) * (N : ℝ) ^ 2) ≤
      4 * (d ^ 2 * L ^ 2 * G * (N : ℝ) * S) := by
    calc
      L ^ 2 * (N : ℝ) * ((M : ℝ) * (N : ℝ) ^ 2) ≤
          L ^ 2 * (N : ℝ) * (4 * S) :=
        mul_le_mul_of_nonneg_left hMNtwo (by positivity)
      _ = 4 * (L ^ 2 * (N : ℝ) * S) := by ring
      _ ≤ 4 * (d ^ 2 * L ^ 2 * G * (N : ℝ) * S) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        calc
          L ^ 2 * (N : ℝ) * S ≤
              (d ^ 2 * L ^ 2 * G) * (N : ℝ) * S := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hLsqfactor hNpos.le) hS0
          _ = d ^ 2 * L ^ 2 * G * (N : ℝ) * S := by ring
  have hcubeTerm :
      (1348 * (M : ℝ)) *
          (576 * (N : ℝ) ^ 3 * L ^ 2) ≤
        3105792 * T := by
    calc
      (1348 * (M : ℝ)) * (576 * (N : ℝ) ^ 3 * L ^ 2) =
          776448 *
            (L ^ 2 * (N : ℝ) * ((M : ℝ) * (N : ℝ) ^ 2)) := by ring
      _ ≤ 776448 *
          (4 * (d ^ 2 * L ^ 2 * G * (N : ℝ) * S)) :=
        mul_le_mul_of_nonneg_left hdegreeGrowth (by norm_num)
      _ = 3105792 * T := by
        dsimp [T]
        ring
  have hLdegree : L ≤ d ^ 2 * L ^ 2 := by
    calc
      L ≤ L ^ 2 := hLsq
      _ = 1 * L ^ 2 := by ring
      _ ≤ d ^ 2 * L ^ 2 :=
        mul_le_mul_of_nonneg_right hdSqOne (sq_nonneg L)
  have hreciprocalGrowth : L * G * (N : ℝ) * S ≤
      d ^ 2 * L ^ 2 * G * (N : ℝ) * S := by
    calc
      L * G * (N : ℝ) * S ≤
          (d ^ 2 * L ^ 2) * G * (N : ℝ) * S := by
        gcongr
      _ = d ^ 2 * L ^ 2 * G * (N : ℝ) * S := by ring
  have hreciprocalTerm :
      (864 * (N : ℝ) * L) *
          (21568 * S * G) ≤
        18634752 * T := by
    calc
      (864 * (N : ℝ) * L) * (21568 * S * G) =
          18634752 * (L * G * (N : ℝ) * S) := by ring
      _ ≤ 18634752 * (d ^ 2 * L ^ 2 * G * (N : ℝ) * S) :=
        mul_le_mul_of_nonneg_left hreciprocalGrowth (by norm_num)
      _ = 18634752 * T := by
        dsimp [T]
  rw [fullCellElementarySieveAggregateEnvelope]
  change
    (1348 * (M : ℝ)) *
          ((4608 / Real.log 2) * (U * V / (M : ℝ)) *
            Real.log (N : ℝ) / (N : ℝ) +
          576 * (N : ℝ) ^ 3 * L ^ 2) +
      (864 * (N : ℝ) * L) *
        (21568 * S * G) ≤
      40000000 * d ^ 2 * L ^ 2 * G * (N : ℝ) * S
  calc
    (1348 * (M : ℝ)) *
          ((4608 / Real.log 2) * (U * V / (M : ℝ)) *
              Real.log (N : ℝ) / (N : ℝ) +
            576 * (N : ℝ) ^ 3 * L ^ 2) +
        (864 * (N : ℝ) * L) *
          (21568 * S * G) =
        (1348 * (M : ℝ)) *
            ((4608 / Real.log 2) * (U * V / (M : ℝ)) *
              Real.log (N : ℝ) / (N : ℝ)) +
          (1348 * (M : ℝ)) *
            (576 * (N : ℝ) ^ 3 * L ^ 2) +
          (864 * (N : ℝ) * L) *
            (21568 * S * G) := by ring
    _ ≤ 13000000 * T + 3105792 * T + 18634752 * T :=
      add_le_add (add_le_add hlinearTerm hcubeTerm) hreciprocalTerm
    _ = 34740544 * T := by ring
    _ ≤ 40000000 * T :=
      mul_le_mul_of_nonneg_right (by norm_num) hT0
    _ = 40000000 * d ^ 2 * L ^ 2 * G * (N : ℝ) * S := by
      dsimp [T]
      ring

end

end PellPaper
