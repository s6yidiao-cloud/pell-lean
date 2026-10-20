import Pell.DyadicBalancedParameterComposition

/-!
# Logarithmic bounds for balanced-cell residual heights

This numerical draft expands the full-column Hadamard height used by the
balanced parameter-composition adapter and records the single positive-ceiling
loss in its residual coefficient height.  The statements are valid at
`B = 0`; no growing-parameter choice or asymptotic absorption is made here.

The exact height formula is inherited from
`DyadicBalancedParameterCompositionCandidate`.  These lemmas remain useful
for any later two-layer determinant endpoint that supplies the same uniform
height scale, independently of whether the current generic bidegree-one
determinant adapter lies on the final asymptotic route.
-/

namespace PellPaper

noncomputable section

/-- The logarithmic ledger for the full-column Hadamard height. -/
def dyadicSourceTargetCellAuxiliaryLogBound
    (B : ℕ) (i : ℕ × ℕ × ℕ × ℕ) : ℝ :=
  ((2 * (B + 1) : ℕ) : ℝ) *
    (Real.log ((2 * (B + 1) : ℕ) : ℝ) / 2 +
      Real.log (dyadicSourceCoordinateBound i : ℝ) +
      (B : ℝ) * Real.log (dyadicTargetCoordinateBound i : ℝ))

/-- The dyadic source-coordinate bound is strictly positive by definition. -/
theorem dyadicSourceCoordinateBound_pos
    (i : ℕ × ℕ × ℕ × ℕ) :
    0 < dyadicSourceCoordinateBound i := by
  rw [dyadicSourceCoordinateBound]
  positivity

/-- The dyadic target-coordinate bound is strictly positive by definition. -/
theorem dyadicTargetCoordinateBound_pos
    (i : ℕ × ℕ × ℕ × ℕ) :
    0 < dyadicTargetCoordinateBound i := by
  rw [dyadicTargetCoordinateBound]
  positivity

/-- The logarithm of the full-column Hadamard height is exactly its explicit
degree-times-coordinate ledger.  In particular, this includes `B = 0`. -/
theorem log_dyadicSourceTargetCellAuxiliaryUniformHeight_eq
    (B : ℕ) (i : ℕ × ℕ × ℕ × ℕ) :
    Real.log (dyadicSourceTargetCellAuxiliaryUniformHeight B i) =
      dyadicSourceTargetCellAuxiliaryLogBound B i := by
  let C : ℕ := 2 * (B + 1)
  let S : ℕ := dyadicSourceCoordinateBound i
  let T : ℕ := dyadicTargetCoordinateBound i
  have hC : 0 < C := by dsimp [C]; omega
  have hS : 0 < S := by
    dsimp [S]
    exact dyadicSourceCoordinateBound_pos i
  have hT : 0 < T := by
    dsimp [T]
    exact dyadicTargetCoordinateBound_pos i
  have hCr : (0 : ℝ) < C := by exact_mod_cast hC
  have hSr : (0 : ℝ) < S := by exact_mod_cast hS
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hcast :
      ((((S : ℤ) ^ 1 * (T : ℤ) ^ B : ℤ) : ℝ)) =
        (S : ℝ) * (T : ℝ) ^ B := by
    push_cast
    simp
  dsimp [C, S, T] at hC hS hT hCr hSr hTr hcast
  rw [dyadicSourceTargetCellAuxiliaryUniformHeight]
  rw [hcast, Real.log_pow,
    Real.log_mul (Real.sqrt_pos.2 hCr).ne'
      (mul_ne_zero hSr.ne' (pow_ne_zero _ hTr.ne')),
    Real.log_sqrt hCr.le,
    Real.log_mul hSr.ne' (pow_ne_zero _ hTr.ne'), Real.log_pow]
  simp only [dyadicSourceTargetCellAuxiliaryLogBound]
  ring

/-- A convenient inequality form of the exact auxiliary-height identity. -/
theorem log_dyadicSourceTargetCellAuxiliaryUniformHeight_le
    (B : ℕ) (i : ℕ × ℕ × ℕ × ℕ) :
    Real.log (dyadicSourceTargetCellAuxiliaryUniformHeight B i) ≤
      dyadicSourceTargetCellAuxiliaryLogBound B i := by
  exact (log_dyadicSourceTargetCellAuxiliaryUniformHeight_eq B i).le

/-- The full-column Hadamard height is at least one.  This is the input that
turns the positive-ceiling additive loss into a single factor of two. -/
theorem one_le_dyadicSourceTargetCellAuxiliaryUniformHeight
    (B : ℕ) (i : ℕ × ℕ × ℕ × ℕ) :
    1 ≤ dyadicSourceTargetCellAuxiliaryUniformHeight B i := by
  let C : ℕ := 2 * (B + 1)
  let S : ℕ := dyadicSourceCoordinateBound i
  let T : ℕ := dyadicTargetCoordinateBound i
  have hC : 1 ≤ C := by dsimp [C]; omega
  have hS : 1 ≤ S := Nat.one_le_iff_ne_zero.mpr
    (dyadicSourceCoordinateBound_pos i).ne'
  have hT : 1 ≤ T := Nat.one_le_iff_ne_zero.mpr
    (dyadicTargetCoordinateBound_pos i).ne'
  have hCr : (1 : ℝ) ≤ C := by exact_mod_cast hC
  have hSr : (1 : ℝ) ≤ S := by exact_mod_cast hS
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hsqrt : (1 : ℝ) ≤ √(C : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hCr
  have hqInt : (1 : ℤ) ≤ (S : ℤ) ^ 1 * (T : ℤ) ^ B := by
    have hSz : (1 : ℤ) ≤ S := by exact_mod_cast hS
    have hTz : (1 : ℤ) ≤ T := by exact_mod_cast hT
    exact mul_le_mul (one_le_pow₀ hSz) (one_le_pow₀ hTz)
      (by norm_num) (by positivity)
  have hq :
      (1 : ℝ) ≤ ((((S : ℤ) ^ 1 * (T : ℤ) ^ B : ℤ) : ℝ)) := by
    exact_mod_cast hqInt
  have hbase :
      (1 : ℝ) ≤ √(C : ℝ) *
        ((((S : ℤ) ^ 1 * (T : ℤ) ^ B : ℤ) : ℝ)) := by
    simpa only [one_mul] using
      mul_le_mul hsqrt hq (by norm_num) (Real.sqrt_nonneg _)
  rw [dyadicSourceTargetCellAuxiliaryUniformHeight]
  change 1 ≤
    (√(C : ℝ) * ((((S : ℤ) ^ 1 * (T : ℤ) ^ B : ℤ) : ℝ))) ^ C
  exact one_le_pow₀ hbase

/-- The logarithmic residual-height ledger.  The first `log 2` is exactly the
positive-ceiling loss; the remaining terms expand the pre-ceiling product. -/
def dyadicSourceTargetCellResidualLogBound
    (B : ℕ) (i : ℕ × ℕ × ℕ × ℕ) : ℝ :=
  Real.log 2 + (B : ℝ) * Real.log 2 + Real.log ((B : ℝ) + 1) +
    dyadicSourceTargetCellAuxiliaryLogBound B i

/-- The positive natural residual coefficient height has the displayed
logarithmic upper bound, uniformly including `B = 0`. -/
theorem log_dyadicSourceTargetCellResidualHeight_le
    (B : ℕ) (i : ℕ × ℕ × ℕ × ℕ) :
    Real.log (dyadicSourceTargetCellResidualHeight B i : ℝ) ≤
      dyadicSourceTargetCellResidualLogBound B i := by
  let H : ℝ := dyadicSourceTargetCellAuxiliaryUniformHeight B i
  let x : ℝ := (2 : ℝ) ^ B * ((B : ℝ) + 1) * H
  have hHone : (1 : ℝ) ≤ H := by
    dsimp [H]
    exact one_le_dyadicSourceTargetCellAuxiliaryUniformHeight B i
  have hxone : (1 : ℝ) ≤ x := by
    dsimp [x]
    have htwo : (1 : ℝ) ≤ (2 : ℝ) ^ B :=
      one_le_pow₀ (by norm_num)
    have hBone : (1 : ℝ) ≤ (B : ℝ) + 1 := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le B)
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (2 : ℝ) ^ B * ((B : ℝ) + 1) :=
        mul_le_mul htwo hBone (by norm_num) (by positivity)
      _ = ((2 : ℝ) ^ B * ((B : ℝ) + 1)) * 1 := by ring
      _ ≤ (2 : ℝ) ^ B * ((B : ℝ) + 1) * H :=
        mul_le_mul_of_nonneg_left hHone (by positivity)
  have hxnonneg : 0 ≤ x := zero_le_one.trans hxone
  have hceil :
      (dyadicSourceTargetCellResidualHeight B i : ℝ) ≤ x + 1 := by
    dsimp [dyadicSourceTargetCellResidualHeight, x, H]
    exact positiveNatCeil_le_add_one (by positivity)
  have hceilTwo :
      (dyadicSourceTargetCellResidualHeight B i : ℝ) ≤ 2 * x :=
    hceil.trans (by linarith)
  have hrespos :
      (0 : ℝ) < dyadicSourceTargetCellResidualHeight B i := by
    have hresNat : 0 < dyadicSourceTargetCellResidualHeight B i := by
      rw [dyadicSourceTargetCellResidualHeight]
      exact positiveNatCeil_pos _
    exact_mod_cast hresNat
  have hxpos : 0 < x := zero_lt_one.trans_le hxone
  calc
    Real.log (dyadicSourceTargetCellResidualHeight B i : ℝ) ≤
        Real.log (2 * x) :=
      Real.log_le_log hrespos hceilTwo
    _ = Real.log 2 + (B : ℝ) * Real.log 2 +
          Real.log ((B : ℝ) + 1) + Real.log H := by
      dsimp [x]
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
          (mul_ne_zero
            (mul_ne_zero (pow_ne_zero _ (by norm_num)) (by positivity))
            (zero_lt_one.trans_le hHone).ne'),
        Real.log_mul
          (mul_ne_zero (pow_ne_zero _ (by norm_num)) (by positivity))
          (zero_lt_one.trans_le hHone).ne',
        Real.log_mul (pow_ne_zero _ (by norm_num)) (by positivity),
        Real.log_pow]
      ring
    _ = dyadicSourceTargetCellResidualLogBound B i := by
      rw [log_dyadicSourceTargetCellAuxiliaryUniformHeight_eq]
      rfl

/-- A direct ledger for the `log (Hraw + 1)` term appearing in the full-cell
substitution threshold after inserting the residual coefficient height. -/
def dyadicSourceTargetCellResidualRawLogBound
    (B : ℕ) (i : ℕ × ℕ × ℕ × ℕ) : ℝ :=
  Real.log 2 + Real.log 12 + Real.log ((B : ℝ) + 1) +
    2 * dyadicSourceTargetCellResidualLogBound B i

/-- The raw factor-extraction height in the full-cell threshold is controlled
by the residual logarithmic ledger. -/
theorem log_fullCellResidualRawHeight_add_one_le
    (B : ℕ) (i : ℕ × ℕ × ℕ × ℕ) :
    Real.log
        (((12 * (B + 1) *
          (dyadicSourceTargetCellResidualHeight B i) ^ 2 : ℕ) : ℝ) + 1) ≤
      dyadicSourceTargetCellResidualRawLogBound B i := by
  let HF : ℕ := dyadicSourceTargetCellResidualHeight B i
  let R : ℝ := (12 * (B + 1) * HF ^ 2 : ℕ)
  have hHF : 0 < HF := by
    dsimp [HF, dyadicSourceTargetCellResidualHeight]
    exact positiveNatCeil_pos _
  have hRone : (1 : ℝ) ≤ R := by
    dsimp [R]
    have hRnat : 0 < 12 * (B + 1) * HF ^ 2 := by positivity
    exact_mod_cast hRnat
  have hRpos : 0 < R := zero_lt_one.trans_le hRone
  have hadd : R + 1 ≤ 2 * R := by linarith
  have hlogR :
      Real.log (R + 1) ≤ Real.log 2 + Real.log 12 +
          Real.log ((B : ℝ) + 1) + 2 * Real.log (HF : ℝ) := by
    calc
      Real.log (R + 1) ≤ Real.log (2 * R) :=
        Real.log_le_log (by positivity) hadd
      _ = Real.log 2 + Real.log 12 + Real.log ((B : ℝ) + 1) +
          2 * Real.log (HF : ℝ) := by
        dsimp [R]
        push_cast
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
            (mul_ne_zero
              (mul_ne_zero (by norm_num) (by positivity))
              (pow_ne_zero _ (by exact_mod_cast hHF.ne'))),
          Real.log_mul
            (mul_ne_zero (by norm_num : (12 : ℝ) ≠ 0) (by positivity))
            (pow_ne_zero _ (by exact_mod_cast hHF.ne')),
          Real.log_mul (by norm_num : (12 : ℝ) ≠ 0) (by positivity),
          Real.log_pow]
        ring
  have hres := log_dyadicSourceTargetCellResidualHeight_le B i
  dsimp [R, HF] at hlogR
  rw [dyadicSourceTargetCellResidualRawLogBound]
  linarith

/-- The sum of the two target dyadic endpoints is bounded by the target
coordinate height `2 max(U,V)`. -/
theorem dyadicTargetEndpointSum_le_coordinateBound
    (i : ℕ × ℕ × ℕ × ℕ) :
    ((2 ^ i.2.2.1 : ℕ) : ℝ) + ((2 ^ i.2.2.2 : ℕ) : ℝ) ≤
      (dyadicTargetCoordinateBound i : ℝ) := by
  have hnat :
      (2 ^ i.2.2.1 : ℕ) + 2 ^ i.2.2.2 ≤
        2 * max (2 ^ i.2.2.1) (2 ^ i.2.2.2) := by
    calc
      (2 ^ i.2.2.1 : ℕ) + 2 ^ i.2.2.2 ≤
          max (2 ^ i.2.2.1) (2 ^ i.2.2.2) +
            max (2 ^ i.2.2.1) (2 ^ i.2.2.2) :=
        Nat.add_le_add (Nat.le_max_left _ _) (Nat.le_max_right _ _)
      _ = 2 * max (2 ^ i.2.2.1) (2 ^ i.2.2.2) := by omega
  rw [dyadicTargetCoordinateBound]
  exact_mod_cast hnat

/-- The matrix-entry scale `6 M (U+V)` in the substitution theorem has a
logarithm controlled by `log 7 + log(M+1) + log T`.  This formulation also
covers `M = 0`. -/
theorem log_six_mul_dyadicTargetEndpointSum_add_one_le
    (M : ℕ) (i : ℕ × ℕ × ℕ × ℕ) :
    Real.log
        (6 * (M : ℝ) *
            (((2 ^ i.2.2.1 : ℕ) : ℝ) + ((2 ^ i.2.2.2 : ℕ) : ℝ)) + 1) ≤
      Real.log 7 + Real.log ((M : ℝ) + 1) +
        Real.log (dyadicTargetCoordinateBound i : ℝ) := by
  let W : ℝ :=
    ((2 ^ i.2.2.1 : ℕ) : ℝ) + ((2 ^ i.2.2.2 : ℕ) : ℝ)
  let T : ℝ := dyadicTargetCoordinateBound i
  have hWT : W ≤ T := by
    dsimp [W, T]
    exact dyadicTargetEndpointSum_le_coordinateBound i
  have hTOne : (1 : ℝ) ≤ T := by
    dsimp [T]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (dyadicTargetCoordinateBound_pos i).ne'
  have hMnonneg : (0 : ℝ) ≤ M := by positivity
  have hTnonneg : 0 ≤ T := zero_le_one.trans hTOne
  have hscale : 6 * (M : ℝ) * W + 1 ≤ 7 * ((M : ℝ) + 1) * T := by
    calc
      6 * (M : ℝ) * W + 1 ≤ 6 * (M : ℝ) * T + 1 := by
        have hmul := mul_le_mul_of_nonneg_left hWT
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6) hMnonneg)
        linarith
      _ ≤ 6 * (M : ℝ) * T + T := by linarith
      _ = (6 * (M : ℝ) + 1) * T := by ring
      _ ≤ 7 * ((M : ℝ) + 1) * T := by
        exact mul_le_mul_of_nonneg_right (by linarith) hTnonneg
  have hrightPos : 0 < 7 * ((M : ℝ) + 1) * T := by positivity
  calc
    Real.log (6 * (M : ℝ) * W + 1) ≤
        Real.log (7 * ((M : ℝ) + 1) * T) :=
      Real.log_le_log (by positivity) hscale
    _ = Real.log 7 + Real.log ((M : ℝ) + 1) + Real.log T := by
      rw [Real.log_mul
          (mul_ne_zero (by norm_num : (7 : ℝ) ≠ 0) (by positivity))
          (by positivity),
        Real.log_mul (by norm_num : (7 : ℝ) ≠ 0) (by positivity)]

/-- The value-height coordinate scale `4(U+V)` costs at most
`log 4 + log T`. -/
theorem log_four_mul_dyadicTargetEndpointSum_le
    (i : ℕ × ℕ × ℕ × ℕ) :
    Real.log
        (4 * (((2 ^ i.2.2.1 : ℕ) : ℝ) +
          ((2 ^ i.2.2.2 : ℕ) : ℝ))) ≤
      Real.log 4 + Real.log (dyadicTargetCoordinateBound i : ℝ) := by
  have hsum := dyadicTargetEndpointSum_le_coordinateBound i
  have hscale :
      4 * (((2 ^ i.2.2.1 : ℕ) : ℝ) + ((2 ^ i.2.2.2 : ℕ) : ℝ)) ≤
        4 * (dyadicTargetCoordinateBound i : ℝ) :=
    mul_le_mul_of_nonneg_left hsum (by norm_num)
  calc
    Real.log
        (4 * (((2 ^ i.2.2.1 : ℕ) : ℝ) +
          ((2 ^ i.2.2.2 : ℕ) : ℝ))) ≤
        Real.log (4 * (dyadicTargetCoordinateBound i : ℝ)) :=
      Real.log_le_log (by positivity) hscale
    _ = Real.log 4 + Real.log (dyadicTargetCoordinateBound i : ℝ) := by
      rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0)
        (by exact_mod_cast (dyadicTargetCoordinateBound_pos i).ne')]

/-- The complete logarithmic upper bound for the substituted residual
coefficient height at degree `2B+1`.  It contains only the explicit residual
ledger, a degree term, `log(M+1)`, and the dyadic target-coordinate log. -/
def dyadicSourceTargetCellSubstitutionLogBound
    (B : ℕ) (i : ℕ × ℕ × ℕ × ℕ) (M : ℕ) : ℝ :=
  let d : ℕ := 2 * B + 1
  Real.log ((d : ℝ) + 1) +
    dyadicSourceTargetCellResidualRawLogBound B i +
      (d : ℝ) *
        (Real.log 2 +
          (Real.log 7 + Real.log ((M : ℝ) + 1) +
            Real.log (dyadicTargetCoordinateBound i : ℝ)))

/-- Inserting the actual residual height and dyadic matrix-entry scale into
the substitution majorant is bounded by the explicit logarithmic ledger. -/
theorem fullCellSubstitutionHeightLogMajorant_dyadicResidual_le
    (B : ℕ) (i : ℕ × ℕ × ℕ × ℕ) (M : ℕ) :
    fullCellSubstitutionHeightLogMajorant (2 * B + 1)
        ((12 * (B + 1) *
          (dyadicSourceTargetCellResidualHeight B i) ^ 2 : ℕ) : ℝ)
        (6 * (M : ℝ) *
          (((2 ^ i.2.2.1 : ℕ) : ℝ) + ((2 ^ i.2.2.2 : ℕ) : ℝ))) ≤
      dyadicSourceTargetCellSubstitutionLogBound B i M := by
  let d : ℕ := 2 * B + 1
  let Hraw : ℝ :=
    (12 * (B + 1) *
      (dyadicSourceTargetCellResidualHeight B i) ^ 2 : ℕ)
  let L : ℝ :=
    6 * (M : ℝ) *
      (((2 ^ i.2.2.1 : ℕ) : ℝ) + ((2 ^ i.2.2.2 : ℕ) : ℝ))
  let LlogBound : ℝ :=
    Real.log 7 + Real.log ((M : ℝ) + 1) +
      Real.log (dyadicTargetCoordinateBound i : ℝ)
  have hHraw : Real.log (Hraw + 1) ≤
      dyadicSourceTargetCellResidualRawLogBound B i := by
    dsimp [Hraw]
    exact log_fullCellResidualRawHeight_add_one_le B i
  have hL : Real.log (L + 1) ≤ LlogBound := by
    dsimp [L, LlogBound]
    exact log_six_mul_dyadicTargetEndpointSum_add_one_le M i
  have hdnonneg : (0 : ℝ) ≤ d := by positivity
  have hdegree :
      (d : ℝ) * (Real.log 2 + Real.log (L + 1)) ≤
        (d : ℝ) * (Real.log 2 + LlogBound) :=
    mul_le_mul_of_nonneg_left (add_le_add le_rfl hL) hdnonneg
  have hsum :
      Real.log ((d : ℝ) + 1) + Real.log (Hraw + 1) +
          (d : ℝ) * (Real.log 2 + Real.log (L + 1)) ≤
        Real.log ((d : ℝ) + 1) +
          dyadicSourceTargetCellResidualRawLogBound B i +
            (d : ℝ) * (Real.log 2 + LlogBound) :=
    add_le_add (add_le_add le_rfl hHraw) hdegree
  simpa only [fullCellSubstitutionHeightLogMajorant,
    dyadicSourceTargetCellSubstitutionLogBound, d, Hraw, L, LlogBound]
    using hsum

/-- The value-height numerator in the uniform sieve threshold after all
dyadic logarithmic replacements. -/
def dyadicSourceTargetCellValueLogBound
    (B : ℕ) (i : ℕ × ℕ × ℕ × ℕ) (M : ℕ) : ℝ :=
  let d : ℕ := 2 * B + 1
  Real.log ((d : ℝ) + 1) +
    dyadicSourceTargetCellSubstitutionLogBound B i M +
      (d : ℝ) *
        (Real.log 4 + Real.log (dyadicTargetCoordinateBound i : ℝ))

/-- The actual value-height numerator is controlled by the expanded dyadic
ledger. -/
theorem fullCellValueLog_dyadicResidual_le
    (B : ℕ) (i : ℕ × ℕ × ℕ × ℕ) (M : ℕ) :
    let d : ℕ := 2 * B + 1
    let Hraw : ℝ :=
      (12 * (B + 1) *
        (dyadicSourceTargetCellResidualHeight B i) ^ 2 : ℕ)
    let L : ℝ :=
      6 * (M : ℝ) *
        (((2 ^ i.2.2.1 : ℕ) : ℝ) + ((2 ^ i.2.2.2 : ℕ) : ℝ))
    Real.log ((d : ℝ) + 1) +
        fullCellSubstitutionHeightLogMajorant d Hraw L +
          (d : ℝ) * Real.log
            (4 * (((2 ^ i.2.2.1 : ℕ) : ℝ) +
              ((2 ^ i.2.2.2 : ℕ) : ℝ))) ≤
      dyadicSourceTargetCellValueLogBound B i M := by
  dsimp only
  let d : ℕ := 2 * B + 1
  let Hraw : ℝ :=
    (12 * (B + 1) *
      (dyadicSourceTargetCellResidualHeight B i) ^ 2 : ℕ)
  let L : ℝ :=
    6 * (M : ℝ) *
      (((2 ^ i.2.2.1 : ℕ) : ℝ) + ((2 ^ i.2.2.2 : ℕ) : ℝ))
  have hK : fullCellSubstitutionHeightLogMajorant d Hraw L ≤
      dyadicSourceTargetCellSubstitutionLogBound B i M := by
    dsimp [d, Hraw, L]
    exact fullCellSubstitutionHeightLogMajorant_dyadicResidual_le B i M
  have hC := log_four_mul_dyadicTargetEndpointSum_le i
  have hdnonneg : (0 : ℝ) ≤ d := by positivity
  have hdegree :
      (d : ℝ) * Real.log
          (4 * (((2 ^ i.2.2.1 : ℕ) : ℝ) +
            ((2 ^ i.2.2.2 : ℕ) : ℝ))) ≤
        (d : ℝ) *
          (Real.log 4 + Real.log (dyadicTargetCoordinateBound i : ℝ)) :=
    mul_le_mul_of_nonneg_left hC hdnonneg
  have hsum :
      Real.log ((d : ℝ) + 1) +
          fullCellSubstitutionHeightLogMajorant d Hraw L +
            (d : ℝ) * Real.log
              (4 * (((2 ^ i.2.2.1 : ℕ) : ℝ) +
                ((2 ^ i.2.2.2 : ℕ) : ℝ))) ≤
        Real.log ((d : ℝ) + 1) +
          dyadicSourceTargetCellSubstitutionLogBound B i M +
            (d : ℝ) *
              (Real.log 4 +
                Real.log (dyadicTargetCoordinateBound i : ℝ)) :=
    add_le_add (add_le_add le_rfl hK) hdegree
  simpa only [dyadicSourceTargetCellValueLogBound, d, Hraw, L] using hsum

/-- The certificate-height numerator in the uniform sieve threshold after
replacing its substitution-height argument by the dyadic ledger. -/
def dyadicSourceTargetCellCertificateLogBound
    (B : ℕ) (i : ℕ × ℕ × ℕ × ℕ) (M : ℕ) : ℝ :=
  fullCellCertificateUniformLogMajorant (2 * B + 1)
    (dyadicSourceTargetCellSubstitutionLogBound B i M)

/-- At fixed degree, the certificate majorant is increasing in its
substitution-height argument; hence the actual certificate numerator is
bounded by the expanded dyadic ledger. -/
theorem fullCellCertificateLog_dyadicResidual_le
    (B : ℕ) (i : ℕ × ℕ × ℕ × ℕ) (M : ℕ) :
    let d : ℕ := 2 * B + 1
    let Hraw : ℝ :=
      (12 * (B + 1) *
        (dyadicSourceTargetCellResidualHeight B i) ^ 2 : ℕ)
    let L : ℝ :=
      6 * (M : ℝ) *
        (((2 ^ i.2.2.1 : ℕ) : ℝ) + ((2 ^ i.2.2.2 : ℕ) : ℝ))
    fullCellCertificateUniformLogMajorant d
        (fullCellSubstitutionHeightLogMajorant d Hraw L) ≤
      dyadicSourceTargetCellCertificateLogBound B i M := by
  dsimp only
  let d : ℕ := 2 * B + 1
  let Hraw : ℝ :=
    (12 * (B + 1) *
      (dyadicSourceTargetCellResidualHeight B i) ^ 2 : ℕ)
  let L : ℝ :=
    6 * (M : ℝ) *
      (((2 ^ i.2.2.1 : ℕ) : ℝ) + ((2 ^ i.2.2.2 : ℕ) : ℝ))
  let Klog : ℝ := fullCellSubstitutionHeightLogMajorant d Hraw L
  let Kbound : ℝ := dyadicSourceTargetCellSubstitutionLogBound B i M
  have hK : Klog ≤ Kbound := by
    dsimp [Klog, Kbound, d, Hraw, L]
    exact fullCellSubstitutionHeightLogMajorant_dyadicResidual_le B i M
  have hcoeff : (0 : ℝ) ≤ (2 * d : ℕ) := by positivity
  have hdelta : 0 ≤ Kbound - Klog := sub_nonneg.mpr hK
  have hproduct : 0 ≤ ((2 * d : ℕ) : ℝ) * (Kbound - Klog) :=
    mul_nonneg hcoeff hdelta
  simp only [fullCellCertificateUniformLogMajorant]
  change
    Real.log 2 + Klog + Real.log ((2 * d).factorial : ℝ) +
        ((2 * d : ℕ) : ℝ) *
          (2 * Real.log (d : ℝ) + (d : ℝ) * Real.log 2 +
            Real.log ((d : ℝ) + 1) + Klog) +
      2 * ((d : ℝ) * Real.log 2 + Real.log ((d : ℝ) + 1) + Klog) ≤
    Real.log 2 + Kbound + Real.log ((2 * d).factorial : ℝ) +
        ((2 * d : ℕ) : ℝ) *
          (2 * Real.log (d : ℝ) + (d : ℝ) * Real.log 2 +
            Real.log ((d : ℝ) + 1) + Kbound) +
      2 * ((d : ℝ) * Real.log 2 + Real.log ((d : ℝ) + 1) + Kbound)
  nlinarith

/-- The explicit endpoint bound for the whole full-cell sieve threshold after
inserting the common dyadic residual height.  Its only non-coordinate terms
are elementary degree/factorial logarithms and `log(M+1)`. -/
def dyadicSourceTargetCellFullCellBudgetLogBound
    (B : ℕ) (i : ℕ × ℕ × ℕ × ℕ) (M : ℕ) : ℝ :=
  max
    (dyadicSourceTargetCellValueLogBound B i M / (Real.log 2 / 16))
    (dyadicSourceTargetCellCertificateLogBound B i M / (Real.log 2 / 8))

/-- The actual uniform residual-sieve threshold is at most the expanded
dyadic logarithmic endpoint bound. -/
theorem fullCellResidualSieveUniformBudgetThreshold_dyadicResidual_le
    (B : ℕ) (i : ℕ × ℕ × ℕ × ℕ) (M : ℕ) :
    fullCellResidualSieveUniformBudgetThreshold i M B
        (dyadicSourceTargetCellResidualHeight B i) ≤
      dyadicSourceTargetCellFullCellBudgetLogBound B i M := by
  have hvalue := fullCellValueLog_dyadicResidual_le B i M
  have hcertificate := fullCellCertificateLog_dyadicResidual_le B i M
  dsimp only at hvalue hcertificate
  rw [fullCellResidualSieveUniformBudgetThreshold,
    fullCellResidualSieveBudgetThreshold,
    dyadicSourceTargetCellFullCellBudgetLogBound]
  apply max_le_max
  · exact (div_le_div_iff_of_pos_right
      (by positivity : 0 < Real.log 2 / 16)).mpr hvalue
  · exact (div_le_div_iff_of_pos_right
      (by positivity : 0 < Real.log 2 / 8)).mpr hcertificate

/-- Consequently, a natural sieve scale above the explicit logarithmic ledger
discharges the threshold premise used by balanced-cell aggregation. -/
theorem fullCellResidualSieveUniformBudgetThreshold_dyadicResidual_le_of_logBound
    (N B : ℕ) (i : ℕ × ℕ × ℕ × ℕ) (M : ℕ)
    (hN : dyadicSourceTargetCellFullCellBudgetLogBound B i M ≤ (N : ℝ)) :
    fullCellResidualSieveUniformBudgetThreshold i M B
        (dyadicSourceTargetCellResidualHeight B i) ≤ (N : ℝ) :=
  (fullCellResidualSieveUniformBudgetThreshold_dyadicResidual_le B i M).trans hN

end

end PellPaper
