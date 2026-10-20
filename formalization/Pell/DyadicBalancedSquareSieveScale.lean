import Pell.DyadicBalancedBudgetLogBound
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# The balanced square-sieve scale

This module places the explicit full-cell residual budget at the scale used in
the balanced argument.  The natural sieve parameter is the positive ceiling
of `(UV / M)^(1/4)`.  Before taking that ceiling, the complete value and
certificate ledger is bounded by a cubic polynomial in `B + 1` times one
coordinate-log budget.  Thus no hidden maximum over residual degrees and no
extra power of the sieve scale remain.

The final theorem deliberately keeps the absolute coordinate-height constant
as a parameter.  This matches the manuscript's `O(theta log Y)` reduced-basis
coordinate bounds and combines it with the displayed
`theta^7 (1 + log (2Y))` prime threshold.
-/

namespace PellPaper

open Filter

noncomputable section

/-- The common nonnegative logarithmic ledger for the source coordinates,
target coordinates, and the cell denominator. -/
def dyadicBalancedCoordinateLogBudget
    (i : ℕ × ℕ × ℕ × ℕ) (M : ℕ) : ℝ :=
  1 + Real.log (dyadicSourceCoordinateBound i : ℝ) +
    Real.log (dyadicTargetCoordinateBound i : ℝ) +
      Real.log ((M : ℝ) + 1)

/-- The real balanced square-sieve scale `(UV/M)^(1/4)`. -/
def dyadicBalancedSquareSieveRealScale
    (i : ℕ × ℕ × ℕ × ℕ) (M : ℕ) : ℝ :=
  ((((2 ^ i.2.2.1 : ℕ) : ℝ) * ((2 ^ i.2.2.2 : ℕ) : ℝ)) /
      (M : ℝ)) ^ ((1 : ℝ) / 4)

/-- A positive natural sieve parameter at the balanced fourth-root scale. -/
def dyadicBalancedSquareSieveScale
    (i : ℕ × ℕ × ℕ × ℕ) (M : ℕ) : ℕ :=
  positiveNatCeil (dyadicBalancedSquareSieveRealScale i M)

theorem dyadicBalancedCoordinateLogBudget_one_le
    (i : ℕ × ℕ × ℕ × ℕ) (M : ℕ) :
    1 ≤ dyadicBalancedCoordinateLogBudget i M := by
  have hS : (1 : ℝ) ≤ dyadicSourceCoordinateBound i := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (dyadicSourceCoordinateBound_pos i).ne'
  have hT : (1 : ℝ) ≤ dyadicTargetCoordinateBound i := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (dyadicTargetCoordinateBound_pos i).ne'
  have hM : (1 : ℝ) ≤ (M : ℝ) + 1 := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le M)
  rw [dyadicBalancedCoordinateLogBudget]
  have hlogS : 0 ≤ Real.log (dyadicSourceCoordinateBound i : ℝ) :=
    Real.log_nonneg hS
  have hlogT : 0 ≤ Real.log (dyadicTargetCoordinateBound i : ℝ) :=
    Real.log_nonneg hT
  have hlogM : 0 ≤ Real.log ((M : ℝ) + 1) := Real.log_nonneg hM
  linarith

private theorem dyadicSourceTargetCellAuxiliaryLogBound_le_coordinateBudget
    (B : ℕ) (i : ℕ × ℕ × ℕ × ℕ) :
    dyadicSourceTargetCellAuxiliaryLogBound B i ≤
      6 * ((B : ℝ) + 1) ^ 2 * dyadicBalancedCoordinateLogBudget i 0 := by
  let p : ℝ := (B : ℝ) + 1
  let Λ : ℝ := dyadicBalancedCoordinateLogBudget i 0
  have hp : 1 ≤ p := by
    have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
    dsimp [p]
    linarith
  have hΛ : 1 ≤ Λ := by
    dsimp [Λ]
    exact dyadicBalancedCoordinateLogBudget_one_le i 0
  have hS : 0 ≤ Real.log (dyadicSourceCoordinateBound i : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (dyadicSourceCoordinateBound_pos i).ne'
  have hT : 0 ≤ Real.log (dyadicTargetCoordinateBound i : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (dyadicTargetCoordinateBound_pos i).ne'
  have hSΛ : Real.log (dyadicSourceCoordinateBound i : ℝ) ≤ Λ := by
    dsimp [Λ, dyadicBalancedCoordinateLogBudget]
    norm_num
    linarith
  have hTΛ : Real.log (dyadicTargetCoordinateBound i : ℝ) ≤ Λ := by
    dsimp [Λ, dyadicBalancedCoordinateLogBudget]
    norm_num
    linarith
  have hlogC : Real.log (2 * p) ≤ 2 * p :=
    Real.log_le_self (by positivity)
  have hB : (B : ℝ) ≤ p := by dsimp [p]; linarith
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  have hΛ0 : 0 ≤ Λ := zero_le_one.trans hΛ
  have hpΛ : p ≤ p * Λ := by nlinarith [mul_nonneg hp0 (sub_nonneg.mpr hΛ)]
  have hΛpΛ : Λ ≤ p * Λ := by nlinarith [mul_nonneg hΛ0 (sub_nonneg.mpr hp)]
  have hBT : (B : ℝ) * Real.log (dyadicTargetCoordinateBound i : ℝ) ≤
      p * Λ := by
    exact mul_le_mul hB hTΛ hT hp0
  rw [dyadicSourceTargetCellAuxiliaryLogBound]
  push_cast
  change 2 * p *
      (Real.log (2 * p) / 2 +
        Real.log (dyadicSourceCoordinateBound i : ℝ) +
          (B : ℝ) * Real.log (dyadicTargetCoordinateBound i : ℝ)) ≤
    6 * p ^ 2 * Λ
  nlinarith [mul_nonneg hp0 hΛ0]

private theorem dyadicSourceTargetCellResidualLogBound_le_coordinateBudget
    (B : ℕ) (i : ℕ × ℕ × ℕ × ℕ) (M : ℕ) :
    dyadicSourceTargetCellResidualLogBound B i ≤
      12 * ((B : ℝ) + 1) ^ 2 * dyadicBalancedCoordinateLogBudget i M := by
  let p : ℝ := (B : ℝ) + 1
  let Λ : ℝ := dyadicBalancedCoordinateLogBudget i M
  have hp : 1 ≤ p := by
    have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
    dsimp [p]
    linarith
  have hΛ : 1 ≤ Λ := dyadicBalancedCoordinateLogBudget_one_le i M
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  have hΛ0 : 0 ≤ Λ := zero_le_one.trans hΛ
  have haux0 := dyadicSourceTargetCellAuxiliaryLogBound_le_coordinateBudget B i
  have hΛmono : dyadicBalancedCoordinateLogBudget i 0 ≤ Λ := by
    dsimp [Λ, dyadicBalancedCoordinateLogBudget]
    norm_num
    have hMone : (1 : ℝ) ≤ (M : ℝ) + 1 := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le M)
    exact Real.log_nonneg hMone
  have haux : dyadicSourceTargetCellAuxiliaryLogBound B i ≤ 6 * p ^ 2 * Λ := by
    exact haux0.trans
      (mul_le_mul_of_nonneg_left hΛmono
        (mul_nonneg (by norm_num) (sq_nonneg p)))
  have hlog2 : Real.log 2 ≤ 2 := Real.log_le_self (by norm_num)
  have hlogp : Real.log p ≤ p := Real.log_le_self (by positivity)
  have hB : (B : ℝ) ≤ p := by dsimp [p]; linarith
  have hp_sq_Λ : p ≤ p ^ 2 * Λ := by
    nlinarith [mul_nonneg hp0 (sub_nonneg.mpr hΛ),
      mul_nonneg hp0 (sub_nonneg.mpr hp)]
  rw [dyadicSourceTargetCellResidualLogBound]
  change Real.log 2 + (B : ℝ) * Real.log 2 + Real.log p +
      dyadicSourceTargetCellAuxiliaryLogBound B i ≤ 12 * p ^ 2 * Λ
  have hBlog : (B : ℝ) * Real.log 2 ≤ 2 * p := by
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ B)
      (sub_nonneg.mpr hlog2)]
  nlinarith

private theorem dyadicSourceTargetCellResidualRawLogBound_le_coordinateBudget
    (B : ℕ) (i : ℕ × ℕ × ℕ × ℕ) (M : ℕ) :
    dyadicSourceTargetCellResidualRawLogBound B i ≤
      40 * ((B : ℝ) + 1) ^ 2 * dyadicBalancedCoordinateLogBudget i M := by
  let p : ℝ := (B : ℝ) + 1
  let Λ : ℝ := dyadicBalancedCoordinateLogBudget i M
  have hp : 1 ≤ p := by
    have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
    dsimp [p]
    linarith
  have hΛ : 1 ≤ Λ := dyadicBalancedCoordinateLogBudget_one_le i M
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  have hΛ0 : 0 ≤ Λ := zero_le_one.trans hΛ
  have hres := dyadicSourceTargetCellResidualLogBound_le_coordinateBudget B i M
  have hlog2 : Real.log 2 ≤ 2 := Real.log_le_self (by norm_num)
  have hlog12 : Real.log 12 ≤ 12 := Real.log_le_self (by norm_num)
  have hlogp : Real.log p ≤ p := Real.log_le_self (by positivity)
  have hp_sq_Λ : p ≤ p ^ 2 * Λ := by
    nlinarith [mul_nonneg hp0 (sub_nonneg.mpr hΛ),
      mul_nonneg hp0 (sub_nonneg.mpr hp)]
  rw [dyadicSourceTargetCellResidualRawLogBound]
  change Real.log 2 + Real.log 12 + Real.log p +
      2 * dyadicSourceTargetCellResidualLogBound B i ≤ 40 * p ^ 2 * Λ
  nlinarith

private theorem dyadicSourceTargetCellSubstitutionLogBound_le_coordinateBudget
    (B : ℕ) (i : ℕ × ℕ × ℕ × ℕ) (M : ℕ) :
    dyadicSourceTargetCellSubstitutionLogBound B i M ≤
      64 * ((B : ℝ) + 1) ^ 2 * dyadicBalancedCoordinateLogBudget i M := by
  let p : ℝ := (B : ℝ) + 1
  let Λ : ℝ := dyadicBalancedCoordinateLogBudget i M
  let d : ℝ := 2 * (B : ℝ) + 1
  have hp : 1 ≤ p := by
    have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
    dsimp [p]
    linarith
  have hΛ : 1 ≤ Λ := dyadicBalancedCoordinateLogBudget_one_le i M
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  have hΛ0 : 0 ≤ Λ := zero_le_one.trans hΛ
  have hd0 : 0 ≤ d := by dsimp [d]; positivity
  have hd : d ≤ 2 * p := by dsimp [d, p]; linarith
  have hraw := dyadicSourceTargetCellResidualRawLogBound_le_coordinateBudget B i M
  have hlogDegree : Real.log (d + 1) ≤ 2 * p := by
    calc
      Real.log (d + 1) ≤ d + 1 := Real.log_le_self (by positivity)
      _ = 2 * p := by dsimp [d, p]; ring
  have hlog2 : Real.log 2 ≤ 2 := Real.log_le_self (by norm_num)
  have hlog7 : Real.log 7 ≤ 7 := Real.log_le_self (by norm_num)
  have hlogM : Real.log ((M : ℝ) + 1) ≤ Λ := by
    dsimp [Λ, dyadicBalancedCoordinateLogBudget]
    have hS : 0 ≤ Real.log (dyadicSourceCoordinateBound i : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (dyadicSourceCoordinateBound_pos i).ne'
    have hT : 0 ≤ Real.log (dyadicTargetCoordinateBound i : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (dyadicTargetCoordinateBound_pos i).ne'
    linarith
  have hlogT : Real.log (dyadicTargetCoordinateBound i : ℝ) ≤ Λ := by
    dsimp [Λ, dyadicBalancedCoordinateLogBudget]
    have hS : 0 ≤ Real.log (dyadicSourceCoordinateBound i : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (dyadicSourceCoordinateBound_pos i).ne'
    have hMone : (1 : ℝ) ≤ (M : ℝ) + 1 := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le M)
    have hM0 : 0 ≤ Real.log ((M : ℝ) + 1) :=
      Real.log_nonneg hMone
    linarith
  have hinner : Real.log 2 +
        (Real.log 7 + Real.log ((M : ℝ) + 1) +
          Real.log (dyadicTargetCoordinateBound i : ℝ)) ≤ 11 * Λ := by
    nlinarith
  have hdegreeInner : d * (Real.log 2 +
        (Real.log 7 + Real.log ((M : ℝ) + 1) +
          Real.log (dyadicTargetCoordinateBound i : ℝ))) ≤ 22 * p * Λ := by
    have hlogM0 : 0 ≤ Real.log ((M : ℝ) + 1) := by
      apply Real.log_nonneg
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le M)
    have hlogT0 : 0 ≤ Real.log (dyadicTargetCoordinateBound i : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (dyadicTargetCoordinateBound_pos i).ne'
    have hinner0 : 0 ≤ Real.log 2 +
        (Real.log 7 + Real.log ((M : ℝ) + 1) +
          Real.log (dyadicTargetCoordinateBound i : ℝ)) := by
      positivity
    calc
      d * _ ≤ (2 * p) * _ := mul_le_mul_of_nonneg_right hd hinner0
      _ ≤ (2 * p) * (11 * Λ) :=
        mul_le_mul_of_nonneg_left hinner (by positivity)
      _ = 22 * p * Λ := by ring
  have hpΛ : p ≤ p * Λ := by
    nlinarith [mul_nonneg hp0 (sub_nonneg.mpr hΛ)]
  have hpΛ_sq : p * Λ ≤ p ^ 2 * Λ := by
    nlinarith [mul_nonneg hΛ0 (sub_nonneg.mpr hp),
      mul_nonneg hp0 hΛ0]
  rw [dyadicSourceTargetCellSubstitutionLogBound]
  push_cast
  change Real.log (d + 1) +
      dyadicSourceTargetCellResidualRawLogBound B i +
        d * (Real.log 2 +
          (Real.log 7 + Real.log ((M : ℝ) + 1) +
            Real.log (dyadicTargetCoordinateBound i : ℝ))) ≤
      64 * p ^ 2 * Λ
  nlinarith

private theorem dyadicSourceTargetCellValueLogBound_le_coordinateBudget
    (B : ℕ) (i : ℕ × ℕ × ℕ × ℕ) (M : ℕ) :
    dyadicSourceTargetCellValueLogBound B i M ≤
      80 * ((B : ℝ) + 1) ^ 2 * dyadicBalancedCoordinateLogBudget i M := by
  let p : ℝ := (B : ℝ) + 1
  let Λ : ℝ := dyadicBalancedCoordinateLogBudget i M
  let d : ℝ := 2 * (B : ℝ) + 1
  have hp : 1 ≤ p := by
    have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
    dsimp [p]
    linarith
  have hΛ : 1 ≤ Λ := dyadicBalancedCoordinateLogBudget_one_le i M
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  have hΛ0 : 0 ≤ Λ := zero_le_one.trans hΛ
  have hd0 : 0 ≤ d := by dsimp [d]; positivity
  have hd : d ≤ 2 * p := by dsimp [d, p]; linarith
  have hsub := dyadicSourceTargetCellSubstitutionLogBound_le_coordinateBudget B i M
  have hlogDegree : Real.log (d + 1) ≤ 2 * p := by
    calc
      Real.log (d + 1) ≤ d + 1 := Real.log_le_self (by positivity)
      _ = 2 * p := by dsimp [d, p]; ring
  have hlog4 : Real.log 4 ≤ 4 := Real.log_le_self (by norm_num)
  have hlogT : Real.log (dyadicTargetCoordinateBound i : ℝ) ≤ Λ := by
    dsimp [Λ, dyadicBalancedCoordinateLogBudget]
    have hS : 0 ≤ Real.log (dyadicSourceCoordinateBound i : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (dyadicSourceCoordinateBound_pos i).ne'
    have hMone : (1 : ℝ) ≤ (M : ℝ) + 1 := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le M)
    have hM0 : 0 ≤ Real.log ((M : ℝ) + 1) :=
      Real.log_nonneg hMone
    linarith
  have hinner : Real.log 4 +
      Real.log (dyadicTargetCoordinateBound i : ℝ) ≤ 5 * Λ := by
    nlinarith
  have hinner0 : 0 ≤ Real.log 4 +
      Real.log (dyadicTargetCoordinateBound i : ℝ) := by positivity
  have hdegreeInner : d * (Real.log 4 +
      Real.log (dyadicTargetCoordinateBound i : ℝ)) ≤ 10 * p * Λ := by
    calc
      d * _ ≤ (2 * p) * _ := mul_le_mul_of_nonneg_right hd hinner0
      _ ≤ (2 * p) * (5 * Λ) :=
        mul_le_mul_of_nonneg_left hinner (by positivity)
      _ = 10 * p * Λ := by ring
  have hpΛ_sq : p ≤ p ^ 2 * Λ := by
    nlinarith [mul_nonneg hp0 (sub_nonneg.mpr hp),
      mul_nonneg hp0 (sub_nonneg.mpr hΛ)]
  have hpΛ_le_sq : p * Λ ≤ p ^ 2 * Λ := by
    nlinarith [mul_nonneg hΛ0 (sub_nonneg.mpr hp),
      mul_nonneg hp0 hΛ0]
  rw [dyadicSourceTargetCellValueLogBound]
  push_cast
  change Real.log (d + 1) +
      dyadicSourceTargetCellSubstitutionLogBound B i M +
        d * (Real.log 4 +
          Real.log (dyadicTargetCoordinateBound i : ℝ)) ≤
      80 * p ^ 2 * Λ
  nlinarith

private theorem log_two_mul_oddDegree_factorial_le
    (B : ℕ) :
    Real.log ((2 * (2 * B + 1)).factorial : ℝ) ≤
      16 * ((B : ℝ) + 1) ^ 2 := by
  let n : ℕ := 2 * (2 * B + 1)
  let p : ℝ := (B : ℝ) + 1
  have hnpos : 0 < n := by dsimp [n]; omega
  have hp : 1 ≤ p := by
    have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
    dsimp [p]
    linarith
  have hn : (n : ℝ) ≤ 4 * p := by
    dsimp [n, p]
    push_cast
    linarith
  have hfacNat : n.factorial ≤ n ^ n := Nat.factorial_le_pow n
  have hfacReal : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by
    exact_mod_cast hfacNat
  have hlogFacPow : Real.log (n.factorial : ℝ) ≤
      Real.log ((n : ℝ) ^ n) :=
    Real.log_le_log (by positivity) hfacReal
  have hlogn : Real.log (n : ℝ) ≤ (n : ℝ) :=
    Real.log_le_self (by positivity)
  have hlogFac : Real.log (n.factorial : ℝ) ≤ (n : ℝ) ^ 2 := by
    rw [Real.log_pow] at hlogFacPow
    have hn0 : (0 : ℝ) ≤ n := by positivity
    nlinarith
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  have hsquare : (n : ℝ) ^ 2 ≤ (4 * p) ^ 2 := by
    nlinarith
  change Real.log (n.factorial : ℝ) ≤ 16 * p ^ 2
  exact hlogFac.trans (hsquare.trans_eq (by ring))

private theorem dyadicSourceTargetCellCertificateLogBound_le_coordinateBudget
    (B : ℕ) (i : ℕ × ℕ × ℕ × ℕ) (M : ℕ) :
    dyadicSourceTargetCellCertificateLogBound B i M ≤
      520 * ((B : ℝ) + 1) ^ 3 * dyadicBalancedCoordinateLogBudget i M := by
  let p : ℝ := (B : ℝ) + 1
  let Λ : ℝ := dyadicBalancedCoordinateLogBudget i M
  let d : ℝ := 2 * (B : ℝ) + 1
  let K : ℝ := dyadicSourceTargetCellSubstitutionLogBound B i M
  have hp : 1 ≤ p := by
    have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
    dsimp [p]
    linarith
  have hΛ : 1 ≤ Λ := dyadicBalancedCoordinateLogBudget_one_le i M
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  have hΛ0 : 0 ≤ Λ := zero_le_one.trans hΛ
  have hd0 : 0 ≤ d := by dsimp [d]; positivity
  have hdpos : 0 < d := by dsimp [d]; positivity
  have hd : d ≤ 2 * p := by dsimp [d, p]; linarith
  have htwoD : 2 * d ≤ 4 * p := by linarith
  have hK : K ≤ 64 * p ^ 2 * Λ := by
    dsimp [K, p, Λ]
    exact dyadicSourceTargetCellSubstitutionLogBound_le_coordinateBudget B i M
  have hK0 : 0 ≤ K := by
    have hSone : (1 : ℝ) ≤ dyadicSourceCoordinateBound i := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (dyadicSourceCoordinateBound_pos i).ne'
    have hTone : (1 : ℝ) ≤ dyadicTargetCoordinateBound i := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (dyadicTargetCoordinateBound_pos i).ne'
    have hMone : (1 : ℝ) ≤ (M : ℝ) + 1 := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le M)
    have hlogS0 : 0 ≤ Real.log (dyadicSourceCoordinateBound i : ℝ) :=
      Real.log_nonneg hSone
    have hlogT0 : 0 ≤ Real.log (dyadicTargetCoordinateBound i : ℝ) :=
      Real.log_nonneg hTone
    have hlogM0 : 0 ≤ Real.log ((M : ℝ) + 1) := Real.log_nonneg hMone
    have hBone : (1 : ℝ) ≤ (B : ℝ) + 1 := by
      have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
      linarith
    have hlogBone0 : 0 ≤ Real.log ((B : ℝ) + 1) := Real.log_nonneg hBone
    have hdOne : (1 : ℝ) ≤ (2 * (B : ℝ) + 1) + 1 := by
      have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
      linarith
    have hlogDegree0 :
        0 ≤ Real.log ((2 * (B : ℝ) + 1) + 1) := Real.log_nonneg hdOne
    have haux0 : 0 ≤ dyadicSourceTargetCellAuxiliaryLogBound B i := by
      rw [dyadicSourceTargetCellAuxiliaryLogBound]
      positivity
    have hres0 : 0 ≤ dyadicSourceTargetCellResidualLogBound B i := by
      rw [dyadicSourceTargetCellResidualLogBound]
      positivity
    have hraw0 : 0 ≤ dyadicSourceTargetCellResidualRawLogBound B i := by
      rw [dyadicSourceTargetCellResidualRawLogBound]
      positivity
    dsimp [K, dyadicSourceTargetCellSubstitutionLogBound]
    push_cast
    exact add_nonneg (add_nonneg hlogDegree0 hraw0)
      (mul_nonneg (by positivity)
        (add_nonneg (Real.log_nonneg (by norm_num))
          (add_nonneg
            (add_nonneg (Real.log_nonneg (by norm_num)) hlogM0) hlogT0)))
  have hlog2 : Real.log 2 ≤ 2 := Real.log_le_self (by norm_num)
  have hlogd : Real.log d ≤ 2 * p :=
    (Real.log_le_self hd0).trans hd
  have hlogDegree : Real.log (d + 1) ≤ 2 * p := by
    calc
      Real.log (d + 1) ≤ d + 1 := Real.log_le_self (by positivity)
      _ = 2 * p := by dsimp [d, p]; ring
  have hfac := log_two_mul_oddDegree_factorial_le B
  have hinner :
      2 * Real.log d + d * Real.log 2 + Real.log (d + 1) + K ≤
        74 * p ^ 2 * Λ := by
    have hdlog : d * Real.log 2 ≤ 4 * p := by
      have hlog20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      calc
        d * Real.log 2 ≤ (2 * p) * Real.log 2 :=
          mul_le_mul_of_nonneg_right hd hlog20
        _ ≤ (2 * p) * 2 :=
          mul_le_mul_of_nonneg_left hlog2 (by positivity)
        _ = 4 * p := by ring
    have hp_le : p ≤ p ^ 2 * Λ := by
      nlinarith [mul_nonneg hp0 (sub_nonneg.mpr hp),
        mul_nonneg hp0 (sub_nonneg.mpr hΛ)]
    nlinarith
  have hinner0 : 0 ≤
      2 * Real.log d + d * Real.log 2 + Real.log (d + 1) + K := by
    have hlogd0 : 0 ≤ Real.log d := Real.log_nonneg (by
      have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
      dsimp [d]
      linarith)
    have hlogDegree0 : 0 ≤ Real.log (d + 1) :=
      Real.log_nonneg (by linarith)
    positivity
  have hproduct :
      (2 * d) *
          (2 * Real.log d + d * Real.log 2 + Real.log (d + 1) + K) ≤
        296 * p ^ 3 * Λ := by
    calc
      (2 * d) * _ ≤ (4 * p) * _ :=
        mul_le_mul_of_nonneg_right htwoD hinner0
      _ ≤ (4 * p) * (74 * p ^ 2 * Λ) :=
        mul_le_mul_of_nonneg_left hinner (by positivity)
      _ = 296 * p ^ 3 * Λ := by ring
  have htailInner :
      d * Real.log 2 + Real.log (d + 1) + K ≤
        70 * p ^ 2 * Λ := by
    have hlog20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hdlog : d * Real.log 2 ≤ 4 * p := by
      calc
        d * Real.log 2 ≤ (2 * p) * Real.log 2 :=
          mul_le_mul_of_nonneg_right hd hlog20
        _ ≤ (2 * p) * 2 :=
          mul_le_mul_of_nonneg_left hlog2 (by positivity)
        _ = 4 * p := by ring
    have hp_le : p ≤ p ^ 2 * Λ := by
      nlinarith [mul_nonneg hp0 (sub_nonneg.mpr hp),
        mul_nonneg hp0 (sub_nonneg.mpr hΛ)]
    nlinarith
  have hp2Λ_le_hp3Λ : p ^ 2 * Λ ≤ p ^ 3 * Λ := by
    have := mul_nonneg (mul_nonneg (sq_nonneg p) hΛ0)
      (sub_nonneg.mpr hp)
    nlinarith
  have hunit : 1 ≤ p ^ 3 * Λ := by
    have hp3 : 1 ≤ p ^ 3 := one_le_pow₀ hp
    nlinarith [mul_nonneg (by positivity : 0 ≤ p ^ 3)
      (sub_nonneg.mpr hΛ)]
  rw [dyadicSourceTargetCellCertificateLogBound,
    fullCellCertificateUniformLogMajorant]
  push_cast
  change Real.log 2 + K +
      Real.log ((2 * (2 * B + 1)).factorial : ℝ) +
        (2 * d) *
          (2 * Real.log d + d * Real.log 2 + Real.log (d + 1) + K) +
          2 * (d * Real.log 2 + Real.log (d + 1) + K) ≤
    520 * p ^ 3 * Λ
  nlinarith

/-- The complete uniform residual sieve threshold is cubic in `B + 1`,
up to the single coordinate-log budget. -/
theorem dyadicSourceTargetCellFullCellBudgetLogBound_le_cubic_coordinateBudget
    (B : ℕ) (i : ℕ × ℕ × ℕ × ℕ) (M : ℕ) :
    dyadicSourceTargetCellFullCellBudgetLogBound B i M ≤
      10000 * ((B : ℝ) + 1) ^ 3 * dyadicBalancedCoordinateLogBudget i M := by
  let p : ℝ := (B : ℝ) + 1
  let Λ : ℝ := dyadicBalancedCoordinateLogBudget i M
  let P : ℝ := p ^ 3 * Λ
  have hp : 1 ≤ p := by
    have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
    dsimp [p]
    linarith
  have hΛ : 1 ≤ Λ := dyadicBalancedCoordinateLogBudget_one_le i M
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  have hΛ0 : 0 ≤ Λ := zero_le_one.trans hΛ
  have hP0 : 0 ≤ P := by dsimp [P]; positivity
  have hp2Λ_le_P : p ^ 2 * Λ ≤ P := by
    dsimp [P]
    have := mul_nonneg (mul_nonneg (sq_nonneg p) hΛ0)
      (sub_nonneg.mpr hp)
    nlinarith
  have hvalue0 := dyadicSourceTargetCellValueLogBound_le_coordinateBudget B i M
  have hvalue : dyadicSourceTargetCellValueLogBound B i M ≤ 80 * P := by
    have hvalue0' : dyadicSourceTargetCellValueLogBound B i M ≤
        80 * (p ^ 2 * Λ) := by
      simpa only [p, Λ, mul_assoc] using hvalue0
    exact hvalue0'.trans
      (mul_le_mul_of_nonneg_left hp2Λ_le_P (by norm_num))
  have hcertificate : dyadicSourceTargetCellCertificateLogBound B i M ≤
      520 * P := by
    simpa only [P, p, Λ, mul_assoc] using
      dyadicSourceTargetCellCertificateLogBound_le_coordinateBudget B i M
  have hlog2lower : (1 : ℝ) / 2 ≤ Real.log 2 := by
    exact (by norm_num : (1 : ℝ) / 2 ≤ 0.6931471803).trans
      Real.log_two_gt_d9.le
  have hden16 : 0 < Real.log 2 / 16 := by positivity
  have hden8 : 0 < Real.log 2 / 8 := by positivity
  have hvalueDiv :
      dyadicSourceTargetCellValueLogBound B i M / (Real.log 2 / 16) ≤
        10000 * P := by
    apply (div_le_iff₀ hden16).2
    have hfactor : 80 ≤ 10000 * (Real.log 2 / 16) := by nlinarith
    exact hvalue.trans
      (by nlinarith [mul_nonneg hP0 (sub_nonneg.mpr hfactor)])
  have hcertificateDiv :
      dyadicSourceTargetCellCertificateLogBound B i M / (Real.log 2 / 8) ≤
        10000 * P := by
    apply (div_le_iff₀ hden8).2
    have hfactor : 520 ≤ 10000 * (Real.log 2 / 8) := by nlinarith
    exact hcertificate.trans
      (by nlinarith [mul_nonneg hP0 (sub_nonneg.mpr hfactor)])
  rw [dyadicSourceTargetCellFullCellBudgetLogBound]
  simpa only [P, p, Λ, mul_assoc] using max_le hvalueDiv hcertificateDiv

theorem dyadicBalancedSquareSieveRealScale_le_natScale
    (i : ℕ × ℕ × ℕ × ℕ) (M : ℕ) :
    dyadicBalancedSquareSieveRealScale i M ≤
      (dyadicBalancedSquareSieveScale i M : ℝ) := by
  exact le_positiveNatCeil _

theorem dyadicBalancedSquareSieveScale_le_realScale_add_one
    (i : ℕ × ℕ × ℕ × ℕ) (M : ℕ) :
    (dyadicBalancedSquareSieveScale i M : ℝ) ≤
      dyadicBalancedSquareSieveRealScale i M + 1 := by
  apply positiveNatCeil_le_add_one
  rw [dyadicBalancedSquareSieveRealScale]
  exact Real.rpow_nonneg
    (div_nonneg (mul_nonneg (by positivity) (by positivity)) (by positivity)) _

/-- An eventual theorem in the square-sieve parameter may be evaluated at
the parameter-dependent balanced scale after exposing its original tail
threshold.  The outer `atTop` quantifier is retained: later parameters must
prove that their fourth-root scale lies beyond that threshold. -/
theorem eventually_apply_at_dyadicBalancedSquareSieveScale
    {P : ℕ → Prop} (hP : ∀ᶠ N : ℕ in atTop, P N) :
    ∀ᶠ N0 : ℕ in atTop,
      ∀ (i : ℕ × ℕ × ℕ × ℕ) (M : ℕ),
        N0 ≤ dyadicBalancedSquareSieveScale i M →
          P (dyadicBalancedSquareSieveScale i M) := by
  obtain ⟨Ntail, htail⟩ := (eventually_atTop.1 hP)
  exact eventually_atTop.2 ⟨Ntail, by
    intro N0 hN0 i M hscale
    exact htail _ (hN0.trans hscale)⟩

/-- A fourth-root scale that dominates the cubic coordinate ledger satisfies
the exact residual budget premise required by balanced-cell aggregation. -/
theorem fullCellResidualSieveUniformBudgetThreshold_le_balancedSquareSieveScale
    (B : ℕ) (i : ℕ × ℕ × ℕ × ℕ) (M : ℕ)
    (hscale :
      10000 * ((B : ℝ) + 1) ^ 3 *
          dyadicBalancedCoordinateLogBudget i M ≤
        dyadicBalancedSquareSieveRealScale i M) :
    fullCellResidualSieveUniformBudgetThreshold i M B
        (dyadicSourceTargetCellResidualHeight B i) ≤
      (dyadicBalancedSquareSieveScale i M : ℝ) := by
  exact (fullCellResidualSieveUniformBudgetThreshold_dyadicResidual_le B i M).trans
    ((dyadicSourceTargetCellFullCellBudgetLogBound_le_cubic_coordinateBudget
      B i M).trans
        (hscale.trans (dyadicBalancedSquareSieveRealScale_le_natScale i M)))

/-- The reduced-basis coordinate bounds combine into one manuscript-shaped
`C * theta * (1 + log (2Y))` ledger. -/
theorem dyadicBalancedCoordinateLogBudget_le_of_reducedBasisBounds
    (theta C : ℝ) (Y : ℕ) (i : ℕ × ℕ × ℕ × ℕ) (M : ℕ)
    (htheta : 3 ≤ theta) (hC : 1 ≤ C) (hY : 2 ≤ Y)
    (hsource : Real.log (dyadicSourceCoordinateBound i : ℝ) ≤
      C * theta * (1 + Real.log (2 * (Y : ℝ))))
    (htarget : Real.log (dyadicTargetCoordinateBound i : ℝ) ≤
      C * (1 + Real.log (2 * (Y : ℝ))))
    (hdenominator : Real.log ((M : ℝ) + 1) ≤
      C * theta * (1 + Real.log (2 * (Y : ℝ)))) :
    dyadicBalancedCoordinateLogBudget i M ≤
      4 * C * theta * (1 + Real.log (2 * (Y : ℝ))) := by
  let A : ℝ := 1 + Real.log (2 * (Y : ℝ))
  have hYreal : (1 : ℝ) ≤ 2 * (Y : ℝ) := by
    exact_mod_cast (show 1 ≤ 2 * Y by omega)
  have hA : 1 ≤ A := by
    dsimp [A]
    exact le_add_of_nonneg_right (Real.log_nonneg hYreal)
  have htheta0 : 0 ≤ theta := by linarith
  have hC0 : 0 ≤ C := by linarith
  have hCA : C * A ≤ C * theta * A := by
    have : 1 ≤ theta := by linarith
    nlinarith [mul_nonneg hC0 (sub_nonneg.mpr this),
      mul_nonneg hC0 (zero_le_one.trans hA)]
  have hone : 1 ≤ C * theta * A := by
    nlinarith [mul_nonneg hC0 htheta0,
      mul_nonneg (mul_nonneg hC0 htheta0) (sub_nonneg.mpr hA)]
  dsimp [A] at hsource htarget hdenominator hCA hone ⊢
  rw [dyadicBalancedCoordinateLogBudget]
  nlinarith

/-- Manuscript-shaped prime availability at `(UV/M)^(1/4)` discharges the
uniform full-cell residual sieve budget.  The exponent `theta^7` comes from
the cubic degree ledger with `B` in the near-square window. -/
theorem fullCellResidualSieveUniformBudgetThreshold_le_balancedSquareSieveScale_of_primeThreshold
    (B : ℕ) (theta C : ℝ) (Y : ℕ)
    (i : ℕ × ℕ × ℕ × ℕ) (M : ℕ)
    (htheta : 3 ≤ theta) (hC : 1 ≤ C) (hY : 2 ≤ Y)
    (hBupper : (B : ℝ) < theta ^ 2 + 1)
    (hsource : Real.log (dyadicSourceCoordinateBound i : ℝ) ≤
      C * theta * (1 + Real.log (2 * (Y : ℝ))))
    (htarget : Real.log (dyadicTargetCoordinateBound i : ℝ) ≤
      C * (1 + Real.log (2 * (Y : ℝ))))
    (hdenominator : Real.log ((M : ℝ) + 1) ≤
      C * theta * (1 + Real.log (2 * (Y : ℝ))))
    (hprime :
      320000 * C * theta ^ 7 * (1 + Real.log (2 * (Y : ℝ))) ≤
        dyadicBalancedSquareSieveRealScale i M) :
    fullCellResidualSieveUniformBudgetThreshold i M B
        (dyadicSourceTargetCellResidualHeight B i) ≤
      (dyadicBalancedSquareSieveScale i M : ℝ) := by
  let p : ℝ := (B : ℝ) + 1
  let A : ℝ := 1 + Real.log (2 * (Y : ℝ))
  have ht9 : 9 ≤ theta ^ 2 := by nlinarith [sq_nonneg (theta - 3)]
  have ht0 : 0 ≤ theta := by linarith
  have hp0 : 0 ≤ p := by dsimp [p]; positivity
  have hp : p ≤ 2 * theta ^ 2 := by
    dsimp [p]
    nlinarith
  have hp3 : p ^ 3 ≤ 8 * theta ^ 6 := by
    calc
      p ^ 3 ≤ (2 * theta ^ 2) ^ 3 := pow_le_pow_left₀ hp0 hp 3
      _ = 8 * theta ^ 6 := by ring
  have hcoord := dyadicBalancedCoordinateLogBudget_le_of_reducedBasisBounds
    theta C Y i M htheta hC hY hsource htarget hdenominator
  have hC0 : 0 ≤ C := by linarith
  have hA0 : 0 ≤ A := by
    dsimp [A]
    have : 0 ≤ Real.log (2 * (Y : ℝ)) := by
      apply Real.log_nonneg
      exact_mod_cast (show 1 ≤ 2 * Y by omega)
    linarith
  have hcoord0 : 0 ≤ dyadicBalancedCoordinateLogBudget i M :=
    (dyadicBalancedCoordinateLogBudget_one_le i M).trans' (by norm_num)
  have hdegreeLedger :
      10000 * p ^ 3 * dyadicBalancedCoordinateLogBudget i M ≤
        320000 * C * theta ^ 7 * A := by
    calc
      10000 * p ^ 3 * dyadicBalancedCoordinateLogBudget i M ≤
          10000 * (8 * theta ^ 6) *
            dyadicBalancedCoordinateLogBudget i M := by
        gcongr
      _ ≤ 10000 * (8 * theta ^ 6) * (4 * C * theta * A) := by
        gcongr
      _ = 320000 * C * theta ^ 7 * A := by ring
  apply fullCellResidualSieveUniformBudgetThreshold_le_balancedSquareSieveScale
  dsimp [p, A] at hdegreeLedger hprime ⊢
  exact hdegreeLedger.trans hprime

end

end PellPaper
