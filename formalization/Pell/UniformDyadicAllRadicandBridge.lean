import Pell.PellPowerSavingReduction
import Pell.RealQuadraticOrderClassAverageUniformExceptional
import Mathlib.Tactic

/-!
# A uniform dyadic all-radicand boundary for Theorem 1.1

This candidate isolates the last project-specific counting input below the
uniform exceptional-set theorem.  The input controls each half-open dyadic
block of arbitrary (not necessarily squarefree) radicands, with one absolute
threshold and one absolute constant valid for every admissible `theta`.

The local block saving is twice the requested global saving.  The proof below
uses this slack only to discard radicands below `sqrt X`; all remaining dyadic
blocks have scale at least `sqrt X / 2` and can be summed geometrically.  The
admissibility comparison, dyadic cover, exponent bookkeeping, and final
Theorem 1.1 composition are proved in Lean.
-/

open Filter
open scoped BigOperators

namespace PellPaper

noncomputable section

/-- **Lower-evidence counting boundary.**  Arbitrary-radicand dyadic Pell
blocks have the doubled saving needed before the routine lower-half and
geometric-summation losses.

The eventual threshold and the constants `cDyadic`, `C` are chosen before the
universal quantifier over `theta`.  Thus this premise retains the uniformity
needed by `UniformExceptionalEstimate`; it is not a collection of fixed-height
estimates whose constants may depend on `theta`. -/
def UniformDyadicAllRadicandEstimate (cSave : ℝ) : Prop :=
  0 < cSave ∧ cSave ≤ 1 ∧
    ∃ cDyadic C : ℝ, 0 < cDyadic ∧ 0 < C ∧
      ∀ᶠ Y : ℕ in atTop, ∀ theta : ℝ, 3 ≤ theta →
        UniformAdmissible cDyadic theta (Y : ℝ) →
          (dyadicSquarePartExceptionalCount theta Y : ℝ) ≤
            C * (Y : ℝ) ^
              (1 - 2 * cSave / (uniformQ theta : ℝ) ^ 2)

/-- Admissibility at `X`, with half the local constant, implies admissibility
at every scale between `sqrt X / 2` and `X`.  The fixed lower bound on `X`
only makes all iterated logarithms positive. -/
theorem uniformAdmissible_of_half_constant_and_sqrt_half_le
    {c theta X Y : ℝ}
    (hc : 0 ≤ c)
    (hX : Real.exp 12 ≤ X)
    (hYlower : Real.sqrt X / 2 ≤ Y)
    (hYupper : Y ≤ X)
    (h : UniformAdmissible (c / 2) theta X) :
    UniformAdmissible c theta Y := by
  have hexp_pos : 0 < Real.exp (12 : ℝ) := Real.exp_pos _
  have hXpos : 0 < X := hexp_pos.trans_le hX
  have hlogX : 12 ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log hexp_pos hX
  have hlogXpos : 0 < Real.log X := by linarith
  have hsqrtXpos : 0 < Real.sqrt X := Real.sqrt_pos.2 hXpos
  have hhalfpos : 0 < Real.sqrt X / 2 := div_pos hsqrtXpos (by norm_num)
  have hYpos : 0 < Y := hhalfpos.trans_le hYlower
  have hlogYlower : Real.log X / 4 ≤ Real.log Y := by
    have hlogTwo : Real.log (2 : ℝ) ≤ 1 := by
      have hlogTwo' :=
        Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at hlogTwo' ⊢
      exact hlogTwo'
    have hlog_sqrt_div :
        Real.log (Real.sqrt X / 2) = Real.log X / 2 - Real.log 2 := by
      rw [Real.log_div (Real.sqrt_ne_zero'.mpr hXpos) (by norm_num),
        Real.log_sqrt hXpos.le]
    have hquarter : Real.log X / 4 ≤ Real.log (Real.sqrt X / 2) := by
      rw [hlog_sqrt_div]
      linarith
    exact hquarter.trans (Real.log_le_log hhalfpos hYlower)
  have hlogYpos : 0 < Real.log Y := by
    have : 0 < Real.log X / 4 := div_pos hlogXpos (by norm_num)
    exact this.trans_le hlogYlower
  have hlogYle : Real.log Y ≤ Real.log X := Real.log_le_log hYpos hYupper
  have hloglogYpos : 0 < Real.log (Real.log Y) := by
    apply Real.log_pos
    have : 3 ≤ Real.log X / 4 := by linarith
    linarith
  have hloglogXpos : 0 < Real.log (Real.log X) := by
    apply Real.log_pos
    linarith
  have hloglogYle : Real.log (Real.log Y) ≤ Real.log (Real.log X) :=
    Real.log_le_log hlogYpos hlogYle
  have hratio :
      Real.log X / Real.log (Real.log X) ≤
        4 * (Real.log Y / Real.log (Real.log Y)) := by
    calc
      Real.log X / Real.log (Real.log X) ≤
          (4 * Real.log Y) / Real.log (Real.log X) := by
        apply div_le_div_of_nonneg_right
        · linarith
        · exact hloglogXpos.le
      _ ≤ (4 * Real.log Y) / Real.log (Real.log Y) := by
        apply div_le_div_of_nonneg_left
        · positivity
        · exact hloglogYpos
        · exact hloglogYle
      _ = 4 * (Real.log Y / Real.log (Real.log Y)) := by ring
  have hratioYnonneg :
      0 ≤ Real.log Y / Real.log (Real.log Y) :=
    div_nonneg hlogYpos.le hloglogYpos.le
  have hsqrtRatio :
      Real.sqrt (Real.log X / Real.log (Real.log X)) ≤
        2 * Real.sqrt (Real.log Y / Real.log (Real.log Y)) := by
    calc
      Real.sqrt (Real.log X / Real.log (Real.log X)) ≤
          Real.sqrt (4 * (Real.log Y / Real.log (Real.log Y))) :=
        Real.sqrt_le_sqrt hratio
      _ = 2 * Real.sqrt (Real.log Y / Real.log (Real.log Y)) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
        norm_num
  unfold UniformAdmissible at h ⊢
  calc
    (uniformQ theta : ℝ) ≤
        (c / 2) * Real.sqrt (Real.log X / Real.log (Real.log X)) := h
    _ ≤ (c / 2) *
        (2 * Real.sqrt (Real.log Y / Real.log (Real.log Y))) := by
      exact mul_le_mul_of_nonneg_left hsqrtRatio (div_nonneg hc (by norm_num))
    _ = c * Real.sqrt (Real.log Y / Real.log (Real.log Y)) := by ring

/-- The doubled local exponent and the final exponent stay in a compact
positive interval, uniformly in every `theta ≥ 3`. -/
theorem uniformDyadicAllRadicand_exponent_bounds
    {cSave theta : ℝ}
    (hcSave : 0 < cSave) (hcSaveOne : cSave ≤ 1)
    (htheta : 3 ≤ theta) :
    0 < 1 - 2 * cSave / (uniformQ theta : ℝ) ^ 2 ∧
      1 / 2 ≤ 1 - 2 * cSave / (uniformQ theta : ℝ) ^ 2 ∧
      1 - 2 * cSave / (uniformQ theta : ℝ) ^ 2 ≤
        1 - cSave / (uniformQ theta : ℝ) ^ 2 ∧
      1 / 2 ≤ 1 - cSave / (uniformQ theta : ℝ) ^ 2 ∧
      1 - 2 * cSave / (uniformQ theta : ℝ) ^ 2 ≤ 1 := by
  have hQ : (2 : ℝ) ≤ (uniformQ theta : ℝ) := by
    exact_mod_cast two_le_uniformQ htheta
  have hQsq : (4 : ℝ) ≤ (uniformQ theta : ℝ) ^ 2 := by nlinarith
  have hQsqPos : 0 < (uniformQ theta : ℝ) ^ 2 := by positivity
  have hfracPos : 0 < cSave / (uniformQ theta : ℝ) ^ 2 :=
    div_pos hcSave hQsqPos
  have hfracLe : cSave / (uniformQ theta : ℝ) ^ 2 ≤ 1 / 4 := by
    apply (div_le_iff₀ hQsqPos).2
    nlinarith
  have htwo :
      2 * cSave / (uniformQ theta : ℝ) ^ 2 =
        2 * (cSave / (uniformQ theta : ℝ) ^ 2) := by ring
  constructor
  · rw [htwo]
    linarith
  constructor
  · rw [htwo]
    linarith
  constructor
  · rw [htwo]
    linarith
  constructor
  · linarith
  · rw [htwo]
    linarith

/-- The total length of all dyadic starting intervals whose doubled scale is
at most `M` is at most `M`.  This is the exact finite estimate used for the
trivial lower half. -/
theorem sum_low_dyadic_scales_le (K M : ℕ) :
    (∑ k ∈ (Finset.range K).filter (fun k => 2 * 2 ^ k ≤ M),
      ((2 ^ k : ℕ) : ℝ)) ≤ M := by
  classical
  by_cases hM : M = 0
  · subst M
    simp
  have hsubset :
      (Finset.range K).filter (fun k => 2 * 2 ^ k ≤ M) ⊆
        Finset.range (Nat.log 2 M) := by
    intro k hk
    obtain ⟨_, hkM⟩ := Finset.mem_filter.mp hk
    have hpow : 2 ^ (k + 1) ≤ M := by
      simpa [pow_succ, Nat.mul_comm] using hkM
    have hklog : k + 1 ≤ Nat.log 2 M :=
      Nat.le_log_of_pow_le Nat.one_lt_two hpow
    exact Finset.mem_range.mpr (by omega)
  calc
    (∑ k ∈ (Finset.range K).filter (fun k => 2 * 2 ^ k ≤ M),
        ((2 ^ k : ℕ) : ℝ)) ≤
        ∑ k ∈ Finset.range (Nat.log 2 M), ((2 ^ k : ℕ) : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro k _ _
      positivity
    _ ≤ ((2 ^ Nat.log 2 M : ℕ) : ℝ) := by
      have hgeom :=
        sum_pow_le_geometric (r := (2 : ℝ)) (by norm_num)
          (Nat.log 2 M)
      norm_num at hgeom
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using hgeom
    _ ≤ M := by
      exact_mod_cast Nat.pow_log_le_self 2 hM

/-- The lower-evidence dyadic block estimate implies the exact uniform
exceptional-set proposition used by the class-number argument. -/
theorem uniformExceptionalEstimate_of_uniformDyadicAllRadicandEstimate
    {cSave : ℝ}
    (hdyadic : UniformDyadicAllRadicandEstimate cSave) :
    UniformExceptionalEstimate cSave := by
  classical
  obtain ⟨hcSave, hcSaveOne, cDyadic, C, hcDyadic, hC, hblocks⟩ := hdyadic
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hblocks
  let denominatorFloor : ℝ := (2 : ℝ) ^ (1 / 2 : ℝ) - 1
  have hdenominatorFloor : 0 < denominatorFloor := by
    dsimp [denominatorFloor]
    exact sub_pos.mpr (Real.one_lt_rpow (by norm_num) (by norm_num))
  let Cglobal : ℝ := 1 + 2 * C / denominatorFloor
  have hCglobal : 0 < Cglobal := by
    dsimp [Cglobal]
    positivity
  refine ⟨hcSave, cDyadic / 2, Cglobal, div_pos hcDyadic (by norm_num),
    hCglobal, ?_⟩
  let X₀ : ℝ := max (Real.exp 12) ((2 * (N₀ : ℝ)) ^ 2)
  filter_upwards [eventually_ge_atTop X₀] with X hXlarge
  dsimp [X₀] at hXlarge
  have hXexp : Real.exp 12 ≤ X := by
    exact (le_max_left (Real.exp 12) ((2 * (N₀ : ℝ)) ^ 2)).trans hXlarge
  have hXsquare : (2 * (N₀ : ℝ)) ^ 2 ≤ X := by
    exact (le_max_right (Real.exp 12) ((2 * (N₀ : ℝ)) ^ 2)).trans hXlarge
  have hexpPos : 0 < Real.exp (12 : ℝ) := Real.exp_pos _
  have hXpos : 0 < X := hexpPos.trans_le hXexp
  have hXone : (1 : ℝ) ≤ X := by
    have : (1 : ℝ) < Real.exp 12 := Real.one_lt_exp_iff.mpr (by norm_num)
    exact this.le.trans hXexp
  have hsqrtN₀ : 2 * (N₀ : ℝ) ≤ Real.sqrt X := by
    calc
      2 * (N₀ : ℝ) = Real.sqrt ((2 * (N₀ : ℝ)) ^ 2) := by
        symm
        exact Real.sqrt_sq (by positivity)
      _ ≤ Real.sqrt X := Real.sqrt_le_sqrt hXsquare
  intro theta htheta hadmissible
  let p : ℝ := 1 - 2 * cSave / (uniformQ theta : ℝ) ^ 2
  let r : ℝ := 1 - cSave / (uniformQ theta : ℝ) ^ 2
  obtain ⟨hp, hpHalf, hpr, hrHalf, hpOne⟩ :=
    uniformDyadicAllRadicand_exponent_bounds hcSave hcSaveOne htheta
  have hp' : 0 < p := by simpa only [p]
  have hpHalf' : (1 / 2 : ℝ) ≤ p := by simpa only [p]
  have hpr' : p ≤ r := by simpa only [p, r]
  have hrHalf' : (1 / 2 : ℝ) ≤ r := by simpa only [r]
  have hpOne' : p ≤ 1 := by simpa only [p]
  let N : ℕ := ⌊X⌋₊
  let K : ℕ := Nat.log 2 N + 1
  let M : ℕ := ⌊Real.sqrt X⌋₊
  have hN : 1 ≤ N := by
    dsimp [N]
    apply (Nat.le_floor_iff hXpos.le).2
    simpa using hXone
  have hNne : N ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hNlt : N < 2 ^ K := by
    dsimp [K]
    simpa [Nat.succ_eq_add_one] using
      (Nat.lt_pow_succ_log_self Nat.one_lt_two N)
  have hcutoff : N ≤ 2 ^ K - 1 := Nat.le_sub_one_of_lt hNlt
  have hcoverNat :
      EInt theta N ≤
        ∑ k ∈ Finset.range K,
          dyadicSquarePartExceptionalCount theta (2 ^ k) :=
    (EInt_le_of_cutoff_le theta hcutoff).trans
      (EInt_le_sum_dyadicSquarePartExceptionalCount theta K)
  have hcover :
      E theta X ≤
        ∑ k ∈ Finset.range K,
          (dyadicSquarePartExceptionalCount theta (2 ^ k) : ℝ) := by
    change (EInt theta N : ℝ) ≤ _
    exact_mod_cast hcoverNat
  let low : Finset ℕ :=
    (Finset.range K).filter (fun k => 2 * 2 ^ k ≤ M)
  let high : Finset ℕ :=
    (Finset.range K).filter (fun k => ¬ 2 * 2 ^ k ≤ M)
  have hpartition :
      (∑ k ∈ Finset.range K,
          (dyadicSquarePartExceptionalCount theta (2 ^ k) : ℝ)) =
        (∑ k ∈ low,
          (dyadicSquarePartExceptionalCount theta (2 ^ k) : ℝ)) +
        (∑ k ∈ high,
          (dyadicSquarePartExceptionalCount theta (2 ^ k) : ℝ)) := by
    dsimp [low, high]
    symm
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  have hlow :
      (∑ k ∈ low,
          (dyadicSquarePartExceptionalCount theta (2 ^ k) : ℝ)) ≤ M := by
    calc
      (∑ k ∈ low,
          (dyadicSquarePartExceptionalCount theta (2 ^ k) : ℝ)) ≤
          ∑ k ∈ low, ((2 ^ k : ℕ) : ℝ) := by
        apply Finset.sum_le_sum
        intro k _
        exact_mod_cast dyadicSquarePartExceptionalCount_le_scale theta (2 ^ k)
      _ ≤ M := by
        simpa only [low] using sum_low_dyadic_scales_le K M
  have hhighPoint : ∀ k ∈ high,
      (dyadicSquarePartExceptionalCount theta (2 ^ k) : ℝ) ≤
        C * ((2 ^ k : ℕ) : ℝ) ^ p := by
    intro k hk
    obtain ⟨hkK, hkHigh⟩ := Finset.mem_filter.mp (by simpa only [high] using hk)
    have hkLog : k ≤ Nat.log 2 N := by
      have : k < K := Finset.mem_range.mp hkK
      dsimp [K] at this
      omega
    have hscaleN : 2 ^ k ≤ N := Nat.pow_le_of_le_log hNne hkLog
    have hscaleX : ((2 ^ k : ℕ) : ℝ) ≤ X := by
      calc
        ((2 ^ k : ℕ) : ℝ) ≤ N := by exact_mod_cast hscaleN
        _ ≤ X := by
          dsimp [N]
          exact Nat.floor_le hXpos.le
    have hMlt : M < 2 * 2 ^ k := lt_of_not_ge hkHigh
    have hsqrtLt : Real.sqrt X < (M : ℝ) + 1 := by
      dsimp [M]
      exact Nat.lt_floor_add_one _
    have hMSucc : (M : ℝ) + 1 ≤ 2 * ((2 ^ k : ℕ) : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hMlt)
    have hscaleLower : Real.sqrt X / 2 ≤ ((2 ^ k : ℕ) : ℝ) := by
      linarith
    have hN₀scale : N₀ ≤ 2 ^ k := by
      have hN₀scaleReal : (N₀ : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by
        nlinarith
      exact_mod_cast hN₀scaleReal
    have hadmissibleScale :
        UniformAdmissible cDyadic theta ((2 ^ k : ℕ) : ℝ) :=
      uniformAdmissible_of_half_constant_and_sqrt_half_le
        hcDyadic.le hXexp hscaleLower hscaleX hadmissible
    simpa only [p] using
      hN₀ (2 ^ k) hN₀scale theta htheta hadmissibleScale
  have hhigh :
      (∑ k ∈ high,
          (dyadicSquarePartExceptionalCount theta (2 ^ k) : ℝ)) ≤
        C * ∑ k ∈ Finset.range K, ((2 ^ k : ℕ) : ℝ) ^ p := by
    calc
      (∑ k ∈ high,
          (dyadicSquarePartExceptionalCount theta (2 ^ k) : ℝ)) ≤
          ∑ k ∈ high, C * ((2 ^ k : ℕ) : ℝ) ^ p := by
        exact Finset.sum_le_sum hhighPoint
      _ ≤ ∑ k ∈ Finset.range K, C * ((2 ^ k : ℕ) : ℝ) ^ p := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          exact (Finset.mem_filter.mp (by simpa only [high] using hk)).1
        · intro k _ _
          positivity
      _ = C * ∑ k ∈ Finset.range K, ((2 ^ k : ℕ) : ℝ) ^ p := by
        rw [Finset.mul_sum]
  have hdenominator :
      denominatorFloor ≤ (2 : ℝ) ^ p - 1 := by
    dsimp [denominatorFloor]
    have := Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 2) hpHalf'
    linarith
  have hdenominatorPos : 0 < (2 : ℝ) ^ p - 1 :=
    sub_pos.mpr (Real.one_lt_rpow (by norm_num) hp')
  have htopNat : 2 ^ K ≤ 2 * N := by
    dsimp [K]
    exact two_pow_log_add_one_le_two_mul hN
  have htopX : ((2 ^ K : ℕ) : ℝ) ≤ 2 * X := by
    calc
      ((2 ^ K : ℕ) : ℝ) ≤ (2 * N : ℕ) := by exact_mod_cast htopNat
      _ ≤ 2 * X := by
        rw [Nat.cast_mul, Nat.cast_ofNat]
        gcongr
        dsimp [N]
        exact Nat.floor_le hXpos.le
  have htwoPow : (2 : ℝ) ^ p ≤ 2 := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hpOne')
  have hXpow : X ^ p ≤ X ^ r :=
    Real.rpow_le_rpow_of_exponent_le hXone hpr'
  have htopPow : ((2 ^ K : ℕ) : ℝ) ^ p ≤ 2 * X ^ r := by
    calc
      ((2 ^ K : ℕ) : ℝ) ^ p ≤ (2 * X) ^ p :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) htopX hp'.le
      _ = (2 : ℝ) ^ p * X ^ p :=
        Real.mul_rpow (by norm_num) hXpos.le
      _ ≤ 2 * X ^ p :=
        mul_le_mul_of_nonneg_right htwoPow (Real.rpow_nonneg hXpos.le _)
      _ ≤ 2 * X ^ r := mul_le_mul_of_nonneg_left hXpow (by norm_num)
  have hquotient :
      ((2 ^ K : ℕ) : ℝ) ^ p / ((2 : ℝ) ^ p - 1) ≤
        (2 * X ^ r) / denominatorFloor :=
    div_le_div₀ (by positivity) htopPow hdenominatorFloor hdenominator
  have hhighFinal :
      (∑ k ∈ high,
          (dyadicSquarePartExceptionalCount theta (2 ^ k) : ℝ)) ≤
        C * ((2 * X ^ r) / denominatorFloor) := by
    calc
      (∑ k ∈ high,
          (dyadicSquarePartExceptionalCount theta (2 ^ k) : ℝ)) ≤
          C * ∑ k ∈ Finset.range K, ((2 ^ k : ℕ) : ℝ) ^ p := hhigh
      _ ≤ C *
          (((2 ^ K : ℕ) : ℝ) ^ p / ((2 : ℝ) ^ p - 1)) := by
        exact mul_le_mul_of_nonneg_left
          (sum_cast_two_pow_rpow_le p hp' K) hC.le
      _ ≤ C * ((2 * X ^ r) / denominatorFloor) :=
        mul_le_mul_of_nonneg_left hquotient hC.le
  have hMreal : (M : ℝ) ≤ Real.sqrt X := by
    dsimp [M]
    exact Nat.floor_le (Real.sqrt_nonneg X)
  have hsqrtPower : Real.sqrt X ≤ X ^ r := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hXone hrHalf'
  calc
    E theta X ≤
        ∑ k ∈ Finset.range K,
          (dyadicSquarePartExceptionalCount theta (2 ^ k) : ℝ) := hcover
    _ = (∑ k ∈ low,
          (dyadicSquarePartExceptionalCount theta (2 ^ k) : ℝ)) +
        (∑ k ∈ high,
          (dyadicSquarePartExceptionalCount theta (2 ^ k) : ℝ)) := hpartition
    _ ≤ (M : ℝ) + C * ((2 * X ^ r) / denominatorFloor) :=
      add_le_add hlow hhighFinal
    _ ≤ X ^ r + C * ((2 * X ^ r) / denominatorFloor) := by
      gcongr
      exact hMreal.trans hsqrtPower
    _ = Cglobal * X ^ r := by
      dsimp [Cglobal]
      ring
    _ = Cglobal * X ^
        (1 - cSave / (uniformQ theta : ℝ) ^ 2) := by rfl

/-- The exact all-order class-average headline follows from the lower-evidence
dyadic all-radicand counting boundary and otherwise proved Lean bridges. -/
theorem realQuadraticOrderClassAverageAssertion_of_uniformDyadicAllRadicandEstimate
    {cSave : ℝ}
    (hdyadic : UniformDyadicAllRadicandEstimate cSave) :
    RealQuadraticOrderClassAverageAssertion :=
  realQuadraticOrderClassAverageAssertion_of_uniformExceptional cSave
    (uniformExceptionalEstimate_of_uniformDyadicAllRadicandEstimate hdyadic)

end

end PellPaper
