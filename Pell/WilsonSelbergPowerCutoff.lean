import Pell.PowerRootBandEndpoints
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# A fixed power cutoff for Wilson's finite Selberg neutralizer

The half-dimensional Selberg construction is applied with
`R = floor(M^(1/100))`.  Its sieve uses primes through `R + 1` and level
`(R + 1)^2`.  This file records the three elementary scale facts needed by
the final moment estimate: positivity of `R`, logarithmic growth of `R + 2`,
and the deliberately generous `M^(3/50)` bound for the cube of the level.
-/

namespace PellPaper

noncomputable section

/-- Wilson's small power cutoff.  The exponent `1/100` leaves ample room
inside the published `M^(2/3)` error term. -/
def main4WilsonSelbergPowerCutoff (M : ℕ) : ℕ :=
  powerRootFloorEndpoint M (1 / 100 : ℝ)

/-- The power cutoff is positive as soon as `M` is. -/
theorem one_le_main4WilsonSelbergPowerCutoff
    {M : ℕ} (hM : 1 ≤ M) :
    1 ≤ main4WilsonSelbergPowerCutoff M := by
  rw [main4WilsonSelbergPowerCutoff, powerRootFloorEndpoint,
    Nat.one_le_floor_iff]
  exact Real.one_le_rpow (by exact_mod_cast hM) (by norm_num)

/-- Rounding the cutoff up once costs at most a factor two. -/
theorem main4WilsonSelbergPowerCutoff_add_one_le_two_rpow
    {M : ℕ} (hM : 1 ≤ M) :
    ((main4WilsonSelbergPowerCutoff M + 1 : ℕ) : ℝ) ≤
      2 * (M : ℝ) ^ (1 / 100 : ℝ) := by
  have hfloor := powerRootFloorEndpoint_le_rpow M (1 / 100 : ℝ)
  have hpow : 1 ≤ (M : ℝ) ^ (1 / 100 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hM) (by norm_num)
  change ((powerRootFloorEndpoint M (1 / 100 : ℝ) + 1 : ℕ) : ℝ) ≤ _
  push_cast
  linarith

/-- The cube of the squared Selberg level is a very small power of `M`.
The constant `64` is exactly the sixth power of the rounding factor two. -/
theorem main4WilsonSelbergPowerCutoff_level_cube_le
    {M : ℕ} (hM : 1 ≤ M) :
    ((((main4WilsonSelbergPowerCutoff M + 1) ^ 2 : ℕ) : ℝ) ^ 3) ≤
      64 * (M : ℝ) ^ (3 / 50 : ℝ) := by
  let x : ℝ := (M : ℝ) ^ (1 / 100 : ℝ)
  have hx : 0 ≤ x := Real.rpow_nonneg (Nat.cast_nonneg M) _
  have hcut : ((main4WilsonSelbergPowerCutoff M + 1 : ℕ) : ℝ) ≤ 2 * x := by
    simpa [x] using main4WilsonSelbergPowerCutoff_add_one_le_two_rpow hM
  have hpow6 :
      ((main4WilsonSelbergPowerCutoff M + 1 : ℕ) : ℝ) ^ 6 ≤
        (2 * x) ^ 6 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hcut 6
  rw [Nat.cast_pow]
  calc
    (((main4WilsonSelbergPowerCutoff M + 1 : ℕ) : ℝ) ^ 2) ^ 3 =
        ((main4WilsonSelbergPowerCutoff M + 1 : ℕ) : ℝ) ^ 6 := by ring
    _ ≤ (2 * x) ^ 6 := hpow6
    _ = 64 * x ^ 6 := by ring
    _ = 64 * (M : ℝ) ^ (3 / 50 : ℝ) := by
      change 64 * (((M : ℝ) ^ (1 / 100 : ℝ)) ^ 6) = _
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg M)]
      norm_num

/-- The extra `+2` in the finite Selberg mass cleanly dominates the
logarithm of the underlying real power; no asymptotic rounding argument is
needed. -/
theorem main4WilsonSelbergPowerCutoff_log_lower
    {M : ℕ} (hM : 1 ≤ M) :
    (1 / 100 : ℝ) * Real.log (M : ℝ) ≤
      Real.log (((main4WilsonSelbergPowerCutoff M + 2 : ℕ) : ℝ)) := by
  have hMpos : 0 < (M : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM)
  have hround := rpow_lt_powerRootFloorEndpoint_add_one
    M (1 / 100 : ℝ)
  have hlt :
      (M : ℝ) ^ (1 / 100 : ℝ) <
        (main4WilsonSelbergPowerCutoff M + 2 : ℕ) := by
    change (M : ℝ) ^ (1 / 100 : ℝ) <
      ((powerRootFloorEndpoint M (1 / 100 : ℝ) + 2 : ℕ) : ℝ)
    norm_num at hround ⊢
    linarith
  have hlog := Real.log_le_log
    (Real.rpow_pos_of_pos hMpos (1 / 100 : ℝ)) hlt.le
  rw [Real.log_rpow hMpos] at hlog
  exact hlog

/-- The small power `M^(3/50)` is already bounded by
`M / sqrt(log M)` throughout the range `M ≥ 2`. -/
theorem rpow_three_fiftieth_mul_sqrt_log_le_self
    {M : ℕ} (hM : 2 ≤ M) :
    (M : ℝ) ^ (3 / 50 : ℝ) * Real.sqrt (Real.log (M : ℝ)) ≤
      (M : ℝ) := by
  have hMone : (1 : ℝ) ≤ (M : ℝ) := by
    exact_mod_cast (show 1 ≤ M by omega)
  have hMpos : 0 < (M : ℝ) := zero_lt_one.trans_le hMone
  have hlogle : Real.log (M : ℝ) ≤ (M : ℝ) := by
    have h := Real.log_le_sub_one_of_pos hMpos
    linarith
  have hsqrtle :
      Real.sqrt (Real.log (M : ℝ)) ≤ Real.sqrt (M : ℝ) :=
    Real.sqrt_le_sqrt hlogle
  calc
    (M : ℝ) ^ (3 / 50 : ℝ) * Real.sqrt (Real.log (M : ℝ)) ≤
        (M : ℝ) ^ (3 / 50 : ℝ) * Real.sqrt (M : ℝ) :=
      mul_le_mul_of_nonneg_left hsqrtle
        (Real.rpow_nonneg (Nat.cast_nonneg M) _)
    _ = (M : ℝ) ^ (14 / 25 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hMpos]
      norm_num
    _ ≤ (M : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hMone (by norm_num)
    _ = (M : ℝ) := by simp

/-- Consequently the complete polynomial coefficient error can also be
absorbed into the natural half-dimensional mass scale. -/
theorem main4WilsonSelbergPowerCutoff_level_cube_le_div_sqrt_log
    {M : ℕ} (hM : 2 ≤ M) :
    ((((main4WilsonSelbergPowerCutoff M + 1) ^ 2 : ℕ) : ℝ) ^ 3) ≤
      64 * ((M : ℝ) / Real.sqrt (Real.log (M : ℝ))) := by
  have hsqrt : 0 < Real.sqrt (Real.log (M : ℝ)) := by
    apply Real.sqrt_pos.2
    apply Real.log_pos
    exact_mod_cast (show 1 < M by omega)
  rw [show 64 * ((M : ℝ) / Real.sqrt (Real.log (M : ℝ))) =
      (64 * (M : ℝ)) / Real.sqrt (Real.log (M : ℝ)) by ring]
  apply (le_div_iff₀ hsqrt).2
  calc
    ((((main4WilsonSelbergPowerCutoff M + 1) ^ 2 : ℕ) : ℝ) ^ 3) *
          Real.sqrt (Real.log (M : ℝ)) ≤
        (64 * (M : ℝ) ^ (3 / 50 : ℝ)) *
          Real.sqrt (Real.log (M : ℝ)) :=
      mul_le_mul_of_nonneg_right
        (main4WilsonSelbergPowerCutoff_level_cube_le (by omega))
        (Real.sqrt_nonneg _)
    _ = 64 * ((M : ℝ) ^ (3 / 50 : ℝ) *
          Real.sqrt (Real.log (M : ℝ))) := by ring
    _ ≤ 64 * (M : ℝ) :=
      mul_le_mul_of_nonneg_left
        (rpow_three_fiftieth_mul_sqrt_log_le_self hM) (by norm_num)

/-- A Selberg mass which dominates the square root of the cutoff logarithm
has reciprocal at most fifteen times the target logarithmic factor. -/
theorem main4WilsonSelbergPowerCutoff_div_mass_le
    {M : ℕ} (hM : 2 ≤ M) {G : ℝ}
    (hG :
      Real.sqrt
          ((1 / 2 : ℝ) *
            Real.log
              (((main4WilsonSelbergPowerCutoff M + 2 : ℕ) : ℝ))) ≤ G) :
    (M : ℝ) / G ≤
      15 * ((M : ℝ) / Real.sqrt (Real.log (M : ℝ))) := by
  let L : ℝ := Real.log (M : ℝ)
  let K : ℝ :=
    Real.log (((main4WilsonSelbergPowerCutoff M + 2 : ℕ) : ℝ))
  have hLpos : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have hLK : (1 / 100 : ℝ) * L ≤ K := by
    simpa [L, K] using
      main4WilsonSelbergPowerCutoff_log_lower (M := M) (by omega)
  have hhalf : L / 200 ≤ (1 / 2 : ℝ) * K := by
    linarith
  have hKnonneg : 0 ≤ K := by
    nlinarith
  have hsqrtKnonneg :
      0 ≤ Real.sqrt ((1 / 2 : ℝ) * K) := Real.sqrt_nonneg _
  have hGnonneg : 0 ≤ G := hsqrtKnonneg.trans hG
  have hGsq : L / 200 ≤ G ^ 2 := by
    have hhalfKnonneg : 0 ≤ (1 / 2 : ℝ) * K :=
      mul_nonneg (by norm_num) hKnonneg
    have hsqrtSq := Real.sq_sqrt hhalfKnonneg
    nlinarith [sq_nonneg (G - Real.sqrt ((1 / 2 : ℝ) * K))]
  have hsqrtLle : Real.sqrt L ≤ 15 * G := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · nlinarith
  have hsqrtLpos : 0 < Real.sqrt L := Real.sqrt_pos.2 hLpos
  have hGpos : 0 < G := by
    have hhalfPos : 0 < (1 / 2 : ℝ) * K := by
      exact lt_of_lt_of_le (by positivity : 0 < L / 200) hhalf
    exact (Real.sqrt_pos.2 hhalfPos).trans_le hG
  change (M : ℝ) / G ≤ 15 * ((M : ℝ) / Real.sqrt L)
  rw [show 15 * ((M : ℝ) / Real.sqrt L) =
      (15 * (M : ℝ)) / Real.sqrt L by ring]
  apply (div_le_div_iff₀ hGpos hsqrtLpos).2
  calc
    (M : ℝ) * Real.sqrt L ≤ (M : ℝ) * (15 * G) :=
      mul_le_mul_of_nonneg_left hsqrtLle (Nat.cast_nonneg M)
    _ = 15 * (M : ℝ) * G := by ring

/-- Combining the reciprocal Selberg main term with the rounded level error
gives a single explicit multiple of `M / sqrt(log M)`. -/
theorem main4WilsonSelbergPowerCutoff_total_le
    {M : ℕ} (hM : 2 ≤ M) {G B : ℝ}
    (hG :
      Real.sqrt
          ((1 / 2 : ℝ) *
            Real.log
              (((main4WilsonSelbergPowerCutoff M + 2 : ℕ) : ℝ))) ≤ G)
    (hB :
      B ≤ (M : ℝ) / G +
        ((((main4WilsonSelbergPowerCutoff M + 1) ^ 2 : ℕ) : ℝ) ^ 3)) :
    B ≤ 79 * ((M : ℝ) / Real.sqrt (Real.log (M : ℝ))) := by
  have hmain := main4WilsonSelbergPowerCutoff_div_mass_le hM hG
  have herr :=
    main4WilsonSelbergPowerCutoff_level_cube_le_div_sqrt_log hM
  linarith

end

end PellPaper
