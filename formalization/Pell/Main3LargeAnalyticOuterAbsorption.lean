import Pell.Main3LargeAnalyticUniformCoefficientAbsorption
import Pell.Main3LargeAnalyticBlockSumLowerEvidence
import Mathlib.Tactic

/-!
# Workspace: outer absorption for the Main3 large-analytic sum

The pointwise shift-weight candidate deliberately weakens each geometric
term to the final `1/400` saving.  That weakened endpoint cannot subsequently
be multiplied by the large-analytic dyadic-index cardinality, whose genuine
radius cost is `Y^(1/(100*theta^2))`.

This workspace retains the pre-weakened `1/32` sieve saving, absorbs the
dyadic cardinality and a concrete `theta^12 log^6` local coefficient, and
only then weakens the resulting `3/400` saving to the public `1/400` target.
-/

namespace PellPaper

open Filter
open scoped BigOperators

noncomputable section

/-! ## A coefficient absorption with the final admissibility constant -/

/-- A degree-sensitive version of uniform polynomial/logarithmic absorption.
Unlike the existing existential-`c₀` candidate, the caller supplies `c`.
The exact sufficient condition is that the two spare logarithmic powers,
together with the displayed polynomial degrees, fit inside `kappa/c²`. -/
theorem eventually_uniform_fixedThetaLogPolynomial_le_rpow_of_degreeBudget_real
    (c kappa K : ℝ) (thetaDegree logDegree : ℕ)
    (hc : 0 < c) (hK : 0 < K)
    (hdegreeBudget :
      ((thetaDegree + logDegree + 2 : ℕ) : ℝ) * c ^ 2 ≤ kappa) :
    ∀ᶠ Z : ℝ in atTop, ∀ theta : ℝ,
      3 ≤ theta →
      theta ≤ c * Real.sqrt
        (Real.log Z / Real.log (Real.log Z)) →
      K * theta ^ thetaDegree *
          (1 + Real.log (2 * Z)) ^ logDegree ≤
        Z ^ (kappa / theta ^ 2) := by
  let m : ℕ := thetaDegree + logDegree + 2
  let mReal : ℝ := m
  let A : ℝ := K * c ^ thetaDegree * 3 ^ logDegree
  let Z₀ : ℝ :=
    max (Real.exp (Real.exp 1)) (Real.exp (max 1 A))
  have hm : 0 < m := by dsimp only [m]; omega
  have hmReal : 0 < mReal := by
    dsimp only [mReal]
    exact_mod_cast hm
  have hA : 0 < A := by dsimp only [A]; positivity
  filter_upwards [eventually_ge_atTop Z₀] with Z hZ
  intro theta htheta hadmissible
  have hZbase : Real.exp (Real.exp 1) ≤ Z :=
    (le_max_left _ _).trans hZ
  have hZconstant : Real.exp (max 1 A) ≤ Z :=
    (le_max_right _ _).trans hZ
  have hZpos : 0 < Z := (Real.exp_pos _).trans_le hZbase
  have hlogExp : Real.exp 1 ≤ Real.log Z := by
    exact (Real.le_log_iff_exp_le hZpos).2 hZbase
  have hlogpos : 0 < Real.log Z := (Real.exp_pos _).trans_le hlogExp
  have hlogone : 1 ≤ Real.log Z := by
    exact (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hlogExp
  have hloglogone : 1 ≤ Real.log (Real.log Z) := by
    exact (Real.le_log_iff_exp_le hlogpos).2 hlogExp
  have hloglogpos : 0 < Real.log (Real.log Z) :=
    zero_lt_one.trans_le hloglogone
  have htheta0 : 0 ≤ theta := by linarith
  have hthetaSqPos : 0 < theta ^ 2 := sq_pos_of_pos (by linarith)
  have hthetaSqLog :=
    theta_sq_mul_log_log_le_of_balanced_admissible
      c theta Z hc.le htheta0 hlogpos.le hloglogpos hadmissible
  have hmTheta :
      mReal * theta ^ 2 * Real.log (Real.log Z) ≤
        kappa * Real.log Z := by
    calc
      mReal * theta ^ 2 * Real.log (Real.log Z) =
          mReal * (theta ^ 2 * Real.log (Real.log Z)) := by ring
      _ ≤ mReal * (c ^ 2 * Real.log Z) :=
        mul_le_mul_of_nonneg_left hthetaSqLog hmReal.le
      _ = (mReal * c ^ 2) * Real.log Z := by ring
      _ ≤ kappa * Real.log Z := by
        apply mul_le_mul_of_nonneg_right _ hlogpos.le
        simpa only [mReal, m] using hdegreeBudget
  have hexponent :
      mReal * Real.log (Real.log Z) ≤
        Real.log Z * (kappa / theta ^ 2) := by
    rw [show Real.log Z * (kappa / theta ^ 2) =
      (kappa * Real.log Z) / theta ^ 2 by ring]
    apply (le_div_iff₀ hthetaSqPos).2
    nlinarith
  have hrpowLower :
      (Real.log Z) ^ m ≤ Z ^ (kappa / theta ^ 2) := by
    calc
      (Real.log Z) ^ m =
          Real.exp (mReal * Real.log (Real.log Z)) := by
        rw [show mReal * Real.log (Real.log Z) =
          Real.log (Real.log Z) * mReal by ring]
        rw [← Real.rpow_def_of_pos hlogpos]
        simp only [mReal, Real.rpow_natCast]
      _ ≤ Real.exp (Real.log Z * (kappa / theta ^ 2)) :=
        Real.exp_le_exp.mpr hexponent
      _ = Z ^ (kappa / theta ^ 2) :=
        (Real.rpow_def_of_pos hZpos _).symm
  have hlogconstant : max 1 A ≤ Real.log Z := by
    exact (Real.le_log_iff_exp_le hZpos).2 hZconstant
  have hAleLog : A ≤ Real.log Z :=
    (le_max_right (1 : ℝ) A).trans hlogconstant
  have hratioLe :
      Real.log Z / Real.log (Real.log Z) ≤ Real.log Z := by
    apply (div_le_iff₀ hloglogpos).2
    have hproduct :
        0 ≤ Real.log Z * (Real.log (Real.log Z) - 1) :=
      mul_nonneg hlogpos.le (sub_nonneg.mpr hloglogone)
    nlinarith
  have hsqrtLeLog :
      Real.sqrt (Real.log Z / Real.log (Real.log Z)) ≤ Real.log Z := by
    have hratio0 :
        0 ≤ Real.log Z / Real.log (Real.log Z) :=
      div_nonneg hlogpos.le hloglogpos.le
    have hsqrtLeSqrt :
        Real.sqrt (Real.log Z / Real.log (Real.log Z)) ≤
          Real.sqrt (Real.log Z) := Real.sqrt_le_sqrt hratioLe
    have hsqrtLogLe : Real.sqrt (Real.log Z) ≤ Real.log Z := by
      rw [Real.sqrt_le_iff]
      exact ⟨hlogpos.le, by nlinarith [hlogone]⟩
    exact hsqrtLeSqrt.trans hsqrtLogLe
  have hthetaLe : theta ≤ c * Real.log Z :=
    hadmissible.trans
      (mul_le_mul_of_nonneg_left hsqrtLeLog hc.le)
  have hthetaPow : theta ^ thetaDegree ≤
      (c * Real.log Z) ^ thetaDegree :=
    pow_le_pow_left₀ htheta0 hthetaLe thetaDegree
  have hlogProduct :
      1 + Real.log (2 * Z) ≤ 3 * Real.log Z := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hZpos.ne']
    nlinarith [Real.log_two_lt_d9.le]
  have hlogProduct0 : 0 ≤ 1 + Real.log (2 * Z) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hZpos.ne']
    have hlogtwo0 : 0 ≤ Real.log 2 :=
      Real.log_nonneg (by norm_num)
    linarith
  have hlogPow : (1 + Real.log (2 * Z)) ^ logDegree ≤
      (3 * Real.log Z) ^ logDegree :=
    pow_le_pow_left₀ hlogProduct0 hlogProduct logDegree
  have hleft :
      K * theta ^ thetaDegree *
          (1 + Real.log (2 * Z)) ^ logDegree ≤
        A * (Real.log Z) ^ (thetaDegree + logDegree) := by
    calc
      K * theta ^ thetaDegree *
          (1 + Real.log (2 * Z)) ^ logDegree ≤
        K * (c * Real.log Z) ^ thetaDegree *
          (3 * Real.log Z) ^ logDegree := by gcongr
      _ = A * (Real.log Z) ^ (thetaDegree + logDegree) := by
        dsimp only [A]
        simp only [mul_pow, pow_add]
        ring
  calc
    K * theta ^ thetaDegree *
        (1 + Real.log (2 * Z)) ^ logDegree ≤
      A * (Real.log Z) ^ (thetaDegree + logDegree) := hleft
    _ ≤ (Real.log Z) ^ 2 *
        (Real.log Z) ^ (thetaDegree + logDegree) := by
      apply mul_le_mul_of_nonneg_right _
        (pow_nonneg hlogpos.le _)
      calc
        A ≤ Real.log Z := hAleLog
        _ ≤ (Real.log Z) ^ 2 := by nlinarith
    _ = (Real.log Z) ^ m := by
      rw [← pow_add]
      congr 1
      dsimp only [m]
      omega
    _ ≤ Z ^ (kappa / theta ^ 2) := hrpowLower

/-- Natural-scale wrapper for the preceding degree-budget absorption. -/
theorem eventually_uniform_fixedThetaLogPolynomial_le_rpow_of_degreeBudget
    (c kappa K : ℝ) (thetaDegree logDegree : ℕ)
    (hc : 0 < c) (hK : 0 < K)
    (hdegreeBudget :
      ((thetaDegree + logDegree + 2 : ℕ) : ℝ) * c ^ 2 ≤ kappa) :
    ∀ᶠ Y : ℕ in atTop, ∀ theta : ℝ,
      3 ≤ theta →
      theta ≤ c * Real.sqrt
        (Real.log (Y : ℝ) / Real.log (Real.log (Y : ℝ))) →
      K * theta ^ thetaDegree *
          (1 + Real.log (2 * (Y : ℝ))) ^ logDegree ≤
        (Y : ℝ) ^ (kappa / theta ^ 2) := by
  exact tendsto_natCast_atTop_atTop.eventually
    (eventually_uniform_fixedThetaLogPolynomial_le_rpow_of_degreeBudget_real
      c kappa K thetaDegree logDegree hc hK hdegreeBudget)

/-! ## The exact dyadic-index coefficient used by the outer sum -/

/-- The complete large-analytic dyadic index cardinality, together with a
`theta^12 log^6` local coefficient, costs

`Y^((1/100 + 1/400)/theta^2)`.

The `1/100` is the genuine dyadic-radius exponent.  The `1/400` absorbs the
remaining `theta^14 log^8` after the index-count estimate contributes two
additional powers of both `theta` and the logarithm.  The degree-budget
condition is `24*c^2 <= 1/400`, which follows from the public assumption
`10*c^2 <= 1/2400`. -/
theorem eventually_main3LargeAnalytic_indexThetaTwelveLogSix_le_rpow
    (K c : ℝ) (hK : 0 < K) (hc : 0 < c)
    (hsmall : 10 * c ^ 2 ≤ (1 : ℝ) / 2400) :
    ∀ᶠ Y : ℕ in atTop, ∀ theta : ℝ,
      3 ≤ theta →
      theta ≤ c * Real.sqrt
        (Real.log (Y : ℝ) / Real.log (Real.log (Y : ℝ))) →
      ((main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices
          theta Y).card : ℝ) *
          (K * theta ^ 12 *
            (1 + Real.log (2 * (Y : ℝ))) ^ 6) ≤
        (Y : ℝ) ^
          ((((1 : ℝ) / 100 + 1 / 400) / theta ^ 2)) := by
  let K₀ : ℝ := 512 * K
  have hK₀ : 0 < K₀ := by dsimp only [K₀]; positivity
  have hdegreeBudget :
      (((14 + 8 + 2 : ℕ) : ℝ) * c ^ 2) ≤ (1 : ℝ) / 400 := by
    norm_num
    nlinarith
  have habsorb :=
    eventually_uniform_fixedThetaLogPolynomial_le_rpow_of_degreeBudget
      c ((1 : ℝ) / 400) K₀ 14 8 hc hK₀ hdegreeBudget
  filter_upwards [habsorb, eventually_ge_atTop 2] with Y habsorbY hY
  intro theta htheta hadmissible
  let y : ℝ := Y
  let delta : ℝ := main3BalancedRExponent theta
  let L : ℝ := 1 + Real.log (2 * y)
  let P : ℝ := main3UnbalancedEnlargedDyadicIndexScaleProduct theta Y
  let I : ℝ :=
    (main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y).card
  have hypos : 0 < y := by dsimp only [y]; positivity
  have hthetaOne : (1 : ℝ) ≤ theta := by linarith
  have hLone : (1 : ℝ) ≤ L := by
    dsimp only [L, y]
    have hone : (1 : ℝ) ≤ 2 * (Y : ℝ) := by
      exact_mod_cast (show 1 ≤ 2 * Y by omega)
    exact le_add_of_nonneg_right (Real.log_nonneg hone)
  have hL0 : 0 ≤ L := zero_le_one.trans hLone
  have hP : P ≤
      32 * y ^ delta * (theta + 1) * (theta + 2) * L ^ 2 := by
    simpa only [P, y, delta, L, Nat.cast_mul, Nat.cast_ofNat] using
      main3UnbalancedEnlargedDyadicIndexScaleProduct_cast_le
        theta Y htheta hY
  have hINat :=
    card_main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices_le theta Y
  have hIP : I ≤ 4 * P := by
    dsimp only [I, P]
    exact_mod_cast hINat
  have hI : I ≤
      128 * y ^ delta * (theta + 1) * (theta + 2) * L ^ 2 := by
    calc
      I ≤ 4 * P := hIP
      _ ≤ 4 *
          (32 * y ^ delta * (theta + 1) * (theta + 2) * L ^ 2) :=
        mul_le_mul_of_nonneg_left hP (by norm_num)
      _ = 128 * y ^ delta * (theta + 1) * (theta + 2) * L ^ 2 := by
        ring
  have hthetaProduct :
      (theta + 1) * (theta + 2) ≤ 4 * theta ^ 2 := by
    have h1 : theta + 1 ≤ 2 * theta := by linarith
    have h2 : theta + 2 ≤ 2 * theta := by linarith
    calc
      (theta + 1) * (theta + 2) ≤ (2 * theta) * (2 * theta) :=
        mul_le_mul h1 h2 (by linarith) (by positivity)
      _ = 4 * theta ^ 2 := by ring
  have hI' : I ≤
      128 * y ^ delta * (4 * theta ^ 2) * L ^ 2 := by
    have hprefactor :
        128 * y ^ delta * ((theta + 1) * (theta + 2)) ≤
          128 * y ^ delta * (4 * theta ^ 2) :=
      mul_le_mul_of_nonneg_left hthetaProduct (by positivity)
    calc
      I ≤ 128 * y ^ delta * (theta + 1) * (theta + 2) * L ^ 2 := hI
      _ = (128 * y ^ delta * ((theta + 1) * (theta + 2))) * L ^ 2 := by
        ring
      _ ≤ (128 * y ^ delta * (4 * theta ^ 2)) * L ^ 2 :=
        mul_le_mul_of_nonneg_right hprefactor (pow_nonneg hL0 _)
      _ = 128 * y ^ delta * (4 * theta ^ 2) * L ^ 2 := by ring
  have hpoly0 : 0 ≤ K * theta ^ 12 * L ^ 6 := by positivity
  have hcombined :
      I * (K * theta ^ 12 * L ^ 6) ≤
        y ^ delta * (K₀ * theta ^ 14 * L ^ 8) := by
    calc
      I * (K * theta ^ 12 * L ^ 6) ≤
          (128 * y ^ delta * (4 * theta ^ 2) * L ^ 2) *
            (K * theta ^ 12 * L ^ 6) :=
        mul_le_mul_of_nonneg_right hI' hpoly0
      _ = y ^ delta * (K₀ * theta ^ 14 * L ^ 8) := by
        dsimp only [K₀]
        ring
  have habsorbCoefficient :
      K₀ * theta ^ 14 * L ^ 8 ≤
        y ^ (((1 : ℝ) / 400) / theta ^ 2) := by
    simpa only [K₀, L, y] using
      habsorbY theta htheta hadmissible
  change I * (K * theta ^ 12 * L ^ 6) ≤
    y ^ (((1 / 100 + 1 / 400) / theta ^ 2))
  calc
    I * (K * theta ^ 12 * L ^ 6) ≤
        y ^ delta * (K₀ * theta ^ 14 * L ^ 8) := hcombined
    _ ≤ y ^ delta * y ^ (((1 : ℝ) / 400) / theta ^ 2) :=
      mul_le_mul_of_nonneg_left habsorbCoefficient
        (Real.rpow_nonneg hypos.le _)
    _ = y ^ (delta + ((1 : ℝ) / 400) / theta ^ 2) := by
      rw [Real.rpow_add hypos]
    _ = y ^ (((1 / 100 + 1 / 400) / theta ^ 2)) := by
      congr 1
      dsimp only [delta, main3BalancedRExponent]
      have hthetaSq : theta ^ 2 ≠ 0 := by positivity
      field_simp [hthetaSq]

/-- Exact exponent ledger after the dyadic-index cost, the `1/400`
coefficient absorption, and the `A^(9/8)` shift cost.  The result retains a
`3/400` saving. -/
theorem main3LargeAnalytic_outer_nineEighth_exponent_eq
    {theta : ℝ} (htheta : 3 ≤ theta) :
    ((1 / 100 + 1 / 400 : ℝ) / theta ^ 2) +
          main3BalancedRExponent theta * (9 / 8) +
          (1 - 1 / (32 * theta ^ 2)) =
      1 - 3 / (400 * theta ^ 2) := by
  have hthetaSq : theta ^ 2 ≠ 0 := by positivity
  dsimp only [main3BalancedRExponent]
  field_simp [hthetaSq]
  ring

/-- The retained `3/400` saving has an explicit `1/200` margin over the
public `1/400` target. -/
theorem main3LargeAnalytic_threeFourHundred_exponent_le_target
    {theta : ℝ} (htheta : 3 ≤ theta) :
    1 - 3 / (400 * theta ^ 2) ≤
      1 - 1 / (400 * theta ^ 2) := by
  have hthetaSqPos : 0 < theta ^ 2 := by positivity
  have hdenNonneg : 0 ≤ 400 * theta ^ 2 :=
    (mul_pos (by norm_num) hthetaSqPos).le
  have : 1 / (400 * theta ^ 2) ≤ 3 / (400 * theta ^ 2) := by
    exact div_le_div_of_nonneg_right (by norm_num) hdenNonneg
  linarith

/-! ## Conditional bridge from a key-summed block estimate to lower evidence -/

/-- On a genuine large-analytic index, the shifted logarithm used by the
local estimate is nonnegative. -/
theorem main3LargeAnalytic_one_add_log_shiftWeight_mul_Y_nonneg
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (hY : 2 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y) :
    0 ≤ 1 + Real.log
      (2 * main3LargeAnalyticShiftWeight h v * (Y : ℝ)) := by
  have hiLarge :=
    mem_main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices.mp hi
  have hiActive :=
    mem_main3UnbalancedEnlargedActiveDyadicCoverIndices.mp hiLarge.1
  have hiBroad :=
    mem_unbalancedShiftedSquareDyadicCoverIndices.mp hiActive.1
  have ha0 : shiftedSquareA h v ≠ 0 :=
    shiftedSquareA_ne_zero hiBroad.1 (by omega)
  have habsOne : (1 : ℝ) ≤ |(shiftedSquareA h v : ℝ)| := by
    exact_mod_cast Int.one_le_abs ha0
  have hYOne : (1 : ℝ) ≤ (Y : ℝ) := by
    exact_mod_cast (show 1 ≤ Y by omega)
  have hargOne : (1 : ℝ) ≤
      2 * main3LargeAnalyticShiftWeight h v * (Y : ℝ) := by
    unfold main3LargeAnalyticShiftWeight
    nlinarith [mul_le_mul habsOne hYOne (by norm_num : (0 : ℝ) ≤ 1)
      (abs_nonneg (shiftedSquareA h v : ℝ))]
  exact add_nonneg zero_le_one (Real.log_nonneg hargOne)

/-- The precise local interface consumed by the outer arithmetic bridge.
It is intended to be proved only after summing the real/complex active cells
and all auxiliary keys for one fixed dyadic block.  The remaining dependence
is the explicit common envelope suggested by the expanded sieve ledgers.

The constant `K` is absolute and is chosen before `c`, `Y`, `theta`, and the
block index. -/
def Main3LargeAnalyticThetaTwelveLogSixPointwiseBlockEstimate : Prop :=
  OneVariableQuadraticWeilDegreeBound →
    ∃ K : ℝ, 0 < K ∧
      ∀ c : ℝ, 0 < c →
        10 * c ^ 2 ≤ (1 : ℝ) / 2400 →
        ∀ᶠ Y : ℕ in atTop, ∀ theta : ℝ,
          3 ≤ theta →
          theta ≤ c * Real.sqrt
            (Real.log (Y : ℝ) / Real.log (Real.log (Y : ℝ))) →
          ∀ h : ℤ, ∀ v D N : ℕ,
            (h, v, D, N) ∈
                main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices
                  theta Y →
            ((squarefreeShiftedSquareBlock
              (shiftedSquareA h v) D Y N).card : ℝ) ≤
              K * theta ^ 12 *
                (1 + Real.log
                  (2 * main3LargeAnalyticShiftWeight h v * (Y : ℝ))) ^ 6 *
                (main3LargeAnalyticShiftWeight h v ^ ((9 : ℝ) / 8) *
                  (Y : ℝ) ^ (1 - 1 / (32 * theta ^ 2)))

/-- A key-summed pointwise block estimate of the preceding explicit shape
implies the exact public lower-evidence proposition.  Before the final
weakening, the proof obtains the stronger exponent
`1 - 3/(400*theta^2)`, leaving the literal margin
`1/(200*theta^2)`. -/
theorem main3LargeAnalyticBlockSumEstimateLowerEvidence_of_thetaTwelveLogSix
    (hPointwise :
      Main3LargeAnalyticThetaTwelveLogSixPointwiseBlockEstimate) :
    Main3LargeAnalyticBlockSumEstimateLowerEvidence := by
  intro hWeil
  obtain ⟨K, hK, hPointwiseAll⟩ := hPointwise hWeil
  let C : ℝ := 4 ^ ((9 : ℝ) / 8)
  have hC : 0 < C := by
    dsimp only [C]
    exact Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨C, hC, ?_⟩
  intro c hc hsmall
  have hcoefficient :=
    eventually_main3LargeAnalytic_indexThetaTwelveLogSix_le_rpow
      (K * 3 ^ 6) c (by positivity) hc hsmall
  have hlocal := hPointwiseAll c hc hsmall
  filter_upwards [hcoefficient, hlocal, eventually_ge_atTop 2] with
    Y hcoefficientY hlocalY hY
  intro theta htheta hadmissible
  let I :=
    main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y
  let y : ℝ := Y
  let L : ℝ := 1 + Real.log (2 * y)
  let delta : ℝ := main3BalancedRExponent theta
  let q : ℝ := ((1 : ℝ) / 100 + 1 / 400) / theta ^ 2
  let sourceExponent : ℝ := 1 - 1 / (32 * theta ^ 2)
  let strongExponent : ℝ := 1 - 3 / (400 * theta ^ 2)
  let targetExponent : ℝ := 1 - 1 / (400 * theta ^ 2)
  have hypos : 0 < y := by dsimp only [y]; positivity
  have hyone : 1 ≤ y := by
    dsimp only [y]
    exact_mod_cast (show 1 ≤ Y by omega)
  have hcoefficientBound :
      (I.card : ℝ) * ((K * 3 ^ 6) * theta ^ 12 * L ^ 6) ≤
        y ^ q := by
    simpa only [I, y, L, q, mul_assoc] using
      hcoefficientY theta htheta hadmissible
  have hpoint : ∀ i ∈ I,
      ((squarefreeShiftedSquareBlock
        (shiftedSquareA i.1 i.2.1) i.2.2.1 Y i.2.2.2).card : ℝ) ≤
        ((K * 3 ^ 6) * theta ^ 12 * L ^ 6) *
          (4 ^ ((9 : ℝ) / 8) *
            y ^ (delta * ((9 : ℝ) / 8)) * y ^ sourceExponent) := by
    intro i hi
    let A : ℝ := main3LargeAnalyticShiftWeight i.1 i.2.1
    let S : ℝ := 1 + Real.log (2 * A * y)
    have hlocalPoint :=
      hlocalY theta htheta hadmissible
        i.1 i.2.1 i.2.2.1 i.2.2.2 (by simpa only [I] using hi)
    have hS0 : 0 ≤ S := by
      simpa only [S, A, y] using
        main3LargeAnalytic_one_add_log_shiftWeight_mul_Y_nonneg
          hY (by simpa only [I] using hi)
    have hS : S ≤ 3 * L := by
      simpa only [S, A, L, y] using
        main3LargeAnalytic_one_add_log_shiftWeight_mul_Y_le_candidate
          htheta hY (by simpa only [I] using hi)
    have hSPow : S ^ 6 ≤ (3 * L) ^ 6 :=
      pow_le_pow_left₀ hS0 hS 6
    have hA : A ^ ((9 : ℝ) / 8) ≤
        4 ^ ((9 : ℝ) / 8) *
          y ^ (delta * ((9 : ℝ) / 8)) := by
      simpa only [A, y, delta] using
        main3LargeAnalyticShiftWeight_rpow_le_candidate
          htheta hY (by simpa only [I] using hi)
            (by norm_num : (0 : ℝ) ≤ 9 / 8)
    have hcoefficientPoint :
        K * theta ^ 12 * S ^ 6 ≤
          K * theta ^ 12 * (3 * L) ^ 6 := by
      exact mul_le_mul_of_nonneg_left hSPow (by positivity)
    have hgeometricPoint :
        A ^ ((9 : ℝ) / 8) * y ^ sourceExponent ≤
          (4 ^ ((9 : ℝ) / 8) *
            y ^ (delta * ((9 : ℝ) / 8))) * y ^ sourceExponent :=
      mul_le_mul_of_nonneg_right hA (Real.rpow_nonneg hypos.le _)
    have hAnonneg : 0 ≤ A := by
      dsimp only [A, main3LargeAnalyticShiftWeight]
      positivity
    have hgeometricPointNonneg :
        0 ≤ A ^ ((9 : ℝ) / 8) * y ^ sourceExponent :=
      mul_nonneg
        (Real.rpow_nonneg hAnonneg _)
        (Real.rpow_nonneg hypos.le _)
    have hcoefficientUpperNonneg :
        0 ≤ K * theta ^ 12 * (3 * L) ^ 6 := by positivity
    calc
      ((squarefreeShiftedSquareBlock
        (shiftedSquareA i.1 i.2.1) i.2.2.1 Y i.2.2.2).card : ℝ) ≤
          K * theta ^ 12 * S ^ 6 *
            (A ^ ((9 : ℝ) / 8) * y ^ sourceExponent) := by
        simpa only [A, S, y, sourceExponent, mul_assoc] using hlocalPoint
      _ ≤ (K * theta ^ 12 * (3 * L) ^ 6) *
          ((4 ^ ((9 : ℝ) / 8) *
            y ^ (delta * ((9 : ℝ) / 8))) * y ^ sourceExponent) := by
        exact mul_le_mul hcoefficientPoint hgeometricPoint
          hgeometricPointNonneg hcoefficientUpperNonneg
      _ = ((K * 3 ^ 6) * theta ^ 12 * L ^ 6) *
          (4 ^ ((9 : ℝ) / 8) *
            y ^ (delta * ((9 : ℝ) / 8)) * y ^ sourceExponent) := by
        rw [mul_pow]
        ring
  have hsum :
      (∑ i ∈ I,
        ((squarefreeShiftedSquareBlock
          (shiftedSquareA i.1 i.2.1) i.2.2.1 Y i.2.2.2).card : ℝ)) ≤
        (I.card : ℝ) * ((K * 3 ^ 6) * theta ^ 12 * L ^ 6) *
          (4 ^ ((9 : ℝ) / 8) *
            y ^ (delta * ((9 : ℝ) / 8)) * y ^ sourceExponent) := by
    calc
      (∑ i ∈ I,
        ((squarefreeShiftedSquareBlock
          (shiftedSquareA i.1 i.2.1) i.2.2.1 Y i.2.2.2).card : ℝ)) ≤
          ∑ _i ∈ I,
            (((K * 3 ^ 6) * theta ^ 12 * L ^ 6) *
              (4 ^ ((9 : ℝ) / 8) *
                y ^ (delta * ((9 : ℝ) / 8)) * y ^ sourceExponent)) := by
        exact Finset.sum_le_sum hpoint
      _ = (I.card : ℝ) * ((K * 3 ^ 6) * theta ^ 12 * L ^ 6) *
          (4 ^ ((9 : ℝ) / 8) *
            y ^ (delta * ((9 : ℝ) / 8)) * y ^ sourceExponent) := by
        simp
        ring
  have hfactorNonneg :
      0 ≤ 4 ^ ((9 : ℝ) / 8) *
        y ^ (delta * ((9 : ℝ) / 8)) * y ^ sourceExponent := by
    positivity
  have hexponent :
      q + delta * ((9 : ℝ) / 8) + sourceExponent =
        strongExponent := by
    simpa only [q, delta, sourceExponent, strongExponent] using
      main3LargeAnalytic_outer_nineEighth_exponent_eq htheta
  have hstrongTarget : strongExponent ≤ targetExponent := by
    simpa only [strongExponent, targetExponent] using
      main3LargeAnalytic_threeFourHundred_exponent_le_target htheta
  change
    (((∑ i ∈ I,
      (squarefreeShiftedSquareBlock
        (shiftedSquareA i.1 i.2.1) i.2.2.1 Y i.2.2.2).card : ℕ) : ℝ)) ≤
      C * y ^ targetExponent
  calc
    (((∑ i ∈ I,
        (squarefreeShiftedSquareBlock
          (shiftedSquareA i.1 i.2.1) i.2.2.1 Y i.2.2.2).card : ℕ) : ℝ)) =
        ∑ i ∈ I,
          ((squarefreeShiftedSquareBlock
            (shiftedSquareA i.1 i.2.1) i.2.2.1 Y i.2.2.2).card : ℝ) := by
      push_cast
      rfl
    _ ≤ (I.card : ℝ) * ((K * 3 ^ 6) * theta ^ 12 * L ^ 6) *
          (4 ^ ((9 : ℝ) / 8) *
            y ^ (delta * ((9 : ℝ) / 8)) * y ^ sourceExponent) := hsum
    _ ≤ y ^ q *
          (4 ^ ((9 : ℝ) / 8) *
            y ^ (delta * ((9 : ℝ) / 8)) * y ^ sourceExponent) :=
      mul_le_mul_of_nonneg_right hcoefficientBound hfactorNonneg
    _ = 4 ^ ((9 : ℝ) / 8) * y ^ strongExponent := by
      calc
        y ^ q *
            (4 ^ ((9 : ℝ) / 8) *
              y ^ (delta * ((9 : ℝ) / 8)) * y ^ sourceExponent) =
            4 ^ ((9 : ℝ) / 8) *
              ((y ^ q * y ^ (delta * ((9 : ℝ) / 8))) *
                y ^ sourceExponent) := by ring
        _ = 4 ^ ((9 : ℝ) / 8) *
              (y ^ (q + delta * ((9 : ℝ) / 8)) *
                y ^ sourceExponent) := by
          congr 1
          exact congrArg (fun t : ℝ => t * y ^ sourceExponent)
            (Real.rpow_add hypos q
              (delta * ((9 : ℝ) / 8))).symm
        _ = 4 ^ ((9 : ℝ) / 8) *
              y ^ (q + delta * ((9 : ℝ) / 8) + sourceExponent) := by
          congr 1
          exact (Real.rpow_add hypos
            (q + delta * ((9 : ℝ) / 8)) sourceExponent).symm
        _ = 4 ^ ((9 : ℝ) / 8) * y ^ strongExponent := by rw [hexponent]
    _ ≤ C * y ^ targetExponent := by
      dsimp only [C]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hyone hstrongTarget) hC.le

#check main3LargeAnalytic_shiftWeightedGeometricTerms_le_target_rpow_candidate
#check exists_pos_eventually_main3LargeAnalytic_indexPolynomialLog_le_rpow_candidate
#check Main3LargeAnalyticThetaTwelveLogSixPointwiseBlockEstimate
#check main3LargeAnalyticBlockSumEstimateLowerEvidence_of_thetaTwelveLogSix

#print axioms main3LargeAnalyticShiftWeight_le_four_mul_rpow_candidate
#print axioms main3LargeAnalyticShiftWeight_rpow_le_candidate
#print axioms main3LargeAnalytic_sevenEighthShiftTerm_le_target_rpow_candidate
#print axioms main3LargeAnalytic_nineEighthShiftTerm_le_target_rpow_candidate
#print axioms main3LargeAnalytic_shiftWeightedGeometricTerms_le_target_rpow_candidate

#print axioms exists_pos_eventually_uniform_fixedThetaLogPolynomial_le_rpow_candidate
#print axioms main3LargeAnalytic_one_add_log_shiftWeight_mul_Y_le_candidate
#print axioms exists_pos_eventually_main3LargeAnalytic_indexPolynomialLog_le_rpow_candidate

#print axioms eventually_uniform_fixedThetaLogPolynomial_le_rpow_of_degreeBudget_real
#print axioms eventually_uniform_fixedThetaLogPolynomial_le_rpow_of_degreeBudget
#print axioms eventually_main3LargeAnalytic_indexThetaTwelveLogSix_le_rpow
#print axioms main3LargeAnalytic_outer_nineEighth_exponent_eq
#print axioms main3LargeAnalytic_threeFourHundred_exponent_le_target
#print axioms main3LargeAnalytic_one_add_log_shiftWeight_mul_Y_nonneg
#print axioms main3LargeAnalyticBlockSumEstimateLowerEvidence_of_thetaTwelveLogSix

end

end PellPaper
