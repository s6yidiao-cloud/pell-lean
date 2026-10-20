import Pell.Main3BalancedHighBoxBound
import Pell.Main3BalancedDyadicBoxSummation
import Pell.Main3BalancedRangeThreshold
import Mathlib.Tactic

/-!
# Explicit high-DE envelope for the main3 balanced range

For an occupied balanced dyadic box, write `T` for the natural main3
threshold, `M` for the rounded localization mesh, `U,V` for the target
endpoints, and `Q = (UV/M)^(1/4)` for the real square-sieve scale.  The exact
endpoint and ceiling packages imply

`Q * (sqrt(UVM) + U + V) <= 24 Y / sqrt(T)`.

This file then inserts that algebraic estimate into the concrete high-box
theorem and the existing finite-union bookkeeping.  It deliberately retains
the dyadic scale-count product and all polynomial/logarithmic factors: no
logarithmic absorption is asserted here.
-/

namespace PellPaper

open Filter

noncomputable section

/-- The geometric square-sieve factor in every occupied main3 balanced box
has an explicit common envelope at the natural range threshold. -/
theorem main3BalancedOccupiedBox_squareSieveEnvelope_le
    (theta : ℝ) (Y : ℕ) (i : ℕ × ℕ × ℕ × ℕ)
    (htheta : 3 ≤ theta) (hY : 2 ≤ Y)
    (hi : i ∈ main3BalancedOccupiedBoxIndices theta Y
      (main3BalancedR theta Y)) :
    let M : ℕ := main3BalancedM theta Y
    let U : ℝ := ((2 ^ i.2.2.1 : ℕ) : ℝ)
    let V : ℝ := ((2 ^ i.2.2.2 : ℕ) : ℝ)
    let Q : ℝ := dyadicBalancedSquareSieveRealScale i M
    Q * (Real.sqrt (U * V * (M : ℝ)) + U + V) ≤
      24 * (Y : ℝ) / Real.sqrt (main3BalancedR theta Y : ℝ) := by
  let y : ℝ := Y
  let T : ℝ := main3BalancedR theta Y
  let M : ℕ := main3BalancedM theta Y
  let Mr : ℝ := M
  let U : ℝ := ((2 ^ i.2.2.1 : ℕ) : ℝ)
  let V : ℝ := ((2 ^ i.2.2.2 : ℕ) : ℝ)
  let Q : ℝ := dyadicBalancedSquareSieveRealScale i M
  let Z : ℝ := Real.sqrt (U * V * Mr)
  let s : ℝ := Real.sqrt T
  change Q * (Z + U + V) ≤ 24 * y / s
  have hyPos : 0 < y := by dsimp [y]; positivity
  have hTpackage := main3BalancedR_parameter_package theta Y htheta hY
  have hToneNat : 1 ≤ main3BalancedR theta Y := hTpackage.1
  have hTpos : 0 < T := by
    dsimp [T]
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hToneNat)
  have hMpackage := main3BalancedM_sharp_bounds theta Y htheta hY
  have hMposNat : 0 < M := by simpa only [M] using hMpackage.1
  have hMpos : 0 < Mr := by dsimp [Mr]; exact_mod_cast hMposNat
  have hUpos : 0 < U := by dsimp [U]; positivity
  have hVpos : 0 < V := by dsimp [V]; positivity
  have hiData := mem_main3BalancedOccupiedBoxIndices.mp hi
  have hTU : T < 2 * U := by
    dsimp [T, U]
    exact_mod_cast hiData.2.2.1
  have hTV : T < 2 * V := by
    dsimp [T, V]
    exact_mod_cast hiData.2.2.2
  obtain ⟨p, hp⟩ := hiData.2.1
  have hcond : DyadicFactorCondition (theta + 1 / 4) Y
      p.1 p.2.1 p.2.2.1 p.2.2.2 :=
    mem_dyadicFactorTuples.mp (Finset.mem_inter.mp hp).1
  have hbox : p ∈ dyadicBox i := (Finset.mem_inter.mp hp).2
  have hnormalization :=
    dyadicFactorCondition_dyadicBox_endpoint_normalization hcond hbox
  have hUV : U * V < 2 * y := by
    simpa only [U, V, y] using hnormalization.1
  have hTM := main3BalancedR_sq_mul_M_comparable theta Y htheta hY
  have hyTM : y ≤ T ^ 2 * Mr := by
    simpa only [y, T, Mr, M] using hTM.1
  have hTMy : T ^ 2 * Mr ≤ 8 * y := by
    simpa only [y, T, Mr, M] using hTM.2
  have hQ0 : 0 ≤ Q := by
    dsimp [Q, dyadicBalancedSquareSieveRealScale]
    positivity
  have hQfour : Q ^ 4 = U * V / Mr := by
    simpa only [Q, U, V, Mr, M] using
      dyadicBalancedSquareSieveRealScale_pow_four i M
  have hbase : U * V / Mr ≤ 2 * T ^ 2 := by
    apply (div_le_iff₀ hMpos).2
    calc
      U * V ≤ 2 * y := hUV.le
      _ ≤ (2 * T ^ 2) * Mr := by nlinarith
  have hQfourUpper : Q ^ 4 ≤ 2 * T ^ 2 := hQfour.le.trans hbase
  have hs0 : 0 ≤ s := by dsimp [s]; exact Real.sqrt_nonneg T
  have hsSq : s ^ 2 = T := by
    dsimp [s]
    exact Real.sq_sqrt hTpos.le
  have hsPos : 0 < s := by nlinarith
  have hQle : Q ≤ 2 * s := by
    by_contra hnot
    have hlt : 2 * s < Q := lt_of_not_ge hnot
    have hsqLt : (2 * s) ^ 2 < Q ^ 2 :=
      (sq_lt_sq₀ (by positivity) hQ0).2 hlt
    have hfourLt : ((2 * s) ^ 2) ^ 2 < (Q ^ 2) ^ 2 :=
      (sq_lt_sq₀ (sq_nonneg (2 * s)) (sq_nonneg Q)).2 hsqLt
    have h16 : 16 * T ^ 2 < Q ^ 4 := by
      calc
        16 * T ^ 2 = ((2 * s) ^ 2) ^ 2 := by rw [← hsSq]; ring
        _ < (Q ^ 2) ^ 2 := hfourLt
        _ = Q ^ 4 := by ring
    nlinarith [sq_pos_of_pos hTpos]
  have hUT : U * T < 4 * y := by
    have hmul := mul_lt_mul_of_pos_left hTV hUpos
    nlinarith
  have hVT : V * T < 4 * y := by
    have hmul := mul_lt_mul_of_pos_left hTU hVpos
    nlinarith
  have hZ0 : 0 ≤ Z := by dsimp [Z]; exact Real.sqrt_nonneg _
  have hZSq : Z ^ 2 = U * V * Mr := by
    dsimp [Z]
    exact Real.sq_sqrt (by positivity)
  have hUVMT : U * V * Mr * T ^ 2 ≤ 16 * y ^ 2 := by
    calc
      U * V * Mr * T ^ 2 = (U * V) * (T ^ 2 * Mr) := by ring
      _ ≤ (2 * y) * (8 * y) :=
        mul_le_mul hUV.le hTMy (by positivity) (by positivity)
      _ = 16 * y ^ 2 := by ring
  have hZTsq : (Z * T) ^ 2 ≤ (4 * y) ^ 2 := by
    calc
      (Z * T) ^ 2 = U * V * Mr * T ^ 2 := by rw [mul_pow, hZSq]
      _ ≤ 16 * y ^ 2 := hUVMT
      _ = (4 * y) ^ 2 := by ring
  have hZT : Z * T ≤ 4 * y :=
    (sq_le_sq₀ (mul_nonneg hZ0 hTpos.le) (by positivity)).1 hZTsq
  have hQZ : Q * Z ≤ 8 * y / s := by
    apply (le_div_iff₀ hsPos).2
    calc
      Q * Z * s ≤ (2 * s) * Z * s := by
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_right hQle (mul_nonneg hZ0 hs0)
      _ = 2 * (Z * T) := by rw [← hsSq]; ring
      _ ≤ 2 * (4 * y) :=
        mul_le_mul_of_nonneg_left hZT (by norm_num)
      _ = 8 * y := by ring
  have hQU : Q * U ≤ 8 * y / s := by
    apply (le_div_iff₀ hsPos).2
    calc
      Q * U * s ≤ (2 * s) * U * s := by
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_right hQle (mul_nonneg hUpos.le hs0)
      _ = 2 * (U * T) := by rw [← hsSq]; ring
      _ ≤ 2 * (4 * y) :=
        mul_le_mul_of_nonneg_left hUT.le (by norm_num)
      _ = 8 * y := by ring
  have hQV : Q * V ≤ 8 * y / s := by
    apply (le_div_iff₀ hsPos).2
    calc
      Q * V * s ≤ (2 * s) * V * s := by
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_right hQle (mul_nonneg hVpos.le hs0)
      _ = 2 * (V * T) := by rw [← hsSq]; ring
      _ ≤ 2 * (4 * y) :=
        mul_le_mul_of_nonneg_left hVT.le (by norm_num)
      _ = 8 * y := by ring
  calc
    Q * (Z + U + V) = Q * Z + Q * U + Q * V := by ring
    _ ≤ 8 * y / s + 8 * y / s + 8 * y / s :=
      add_le_add (add_le_add hQZ hQU) hQV
    _ = 24 * y / s := by ring

/-- The concrete main3 high-box theorem with its geometric factor replaced
by the common `24 Y / sqrt(T)` envelope.  No dyadic-box multiplicity has yet
been charged. -/
theorem eventually_main3BalancedHighDEBoxIndex_card_le_commonEnvelope
    (hWeil : OneVariableQuadraticWeilDegreeBound)
    (c : ℝ) (hc : 0 < c)
    (hsmall : 10 * c ^ 2 ≤ (1 : ℝ) / 400) :
    ∀ᶠ Y : ℕ in atTop,
      ∀ (theta : ℝ),
        3 ≤ theta →
        theta ≤ c * Real.sqrt
          (Real.log (Y : ℝ) / Real.log (Real.log (Y : ℝ))) →
        ∀ i ∈ main3BalancedHighDEBoxIndices theta Y
          (main3BalancedR theta Y),
          let B : ℕ := main3BalancedDegree theta
          let H0 : ℕ := 2 * (B + 1)
          let M : ℕ := main3BalancedM theta Y
          let T : ℝ := main3BalancedR theta Y
          ((dyadicFactorBoxCell (theta + 1 / 4) Y i).card : ℝ) ≤
            1348 * (M : ℝ) *
                ((H0 : ℝ) + 96 * theta * (B : ℝ) + 16) +
              7864320000000 * ((B : ℝ) + 1) ^ 2 *
                (1 + Real.log (2 * (Y : ℝ))) ^ 3 *
                  (Y : ℝ) / Real.sqrt T := by
  have hlocalEventual :=
    eventually_main3BalancedHighDE_dyadicFactorBoxCell_card_le
      hWeil c hc hsmall
  filter_upwards [hlocalEventual, eventually_ge_atTop 2] with Y hlocal hY
  intro theta htheta hadmissible i hi
  have hiHigh := mem_main3BalancedHighDEBoxIndices.mp hi
  have hiOccupied := mem_main3BalancedOccupiedBoxIndices.mp hiHigh.1
  have hlocalBound :=
    hlocal theta i htheta hadmissible hiOccupied.2.1 hiHigh.2
  have hgeometric :=
    main3BalancedOccupiedBox_squareSieveEnvelope_le
      theta Y i htheta hY hiHigh.1
  let y : ℝ := Y
  let B : ℕ := main3BalancedDegree theta
  let H0 : ℕ := 2 * (B + 1)
  let M : ℕ := main3BalancedM theta Y
  let T : ℝ := main3BalancedR theta Y
  let U : ℝ := ((2 ^ i.2.2.1 : ℕ) : ℝ)
  let V : ℝ := ((2 ^ i.2.2.2 : ℕ) : ℝ)
  let Q : ℝ := dyadicBalancedSquareSieveRealScale i M
  let S : ℝ := Real.sqrt (U * V * (M : ℝ)) + U + V
  let A : ℝ := 1348 * (M : ℝ) *
    ((H0 : ℝ) + 96 * theta * (B : ℝ) + 16)
  let C : ℝ := 327680000000 * ((B : ℝ) + 1) ^ 2 *
    (1 + Real.log (2 * y)) ^ 3
  change ((dyadicFactorBoxCell (theta + 1 / 4) Y i).card : ℝ) ≤
    A + 7864320000000 * ((B : ℝ) + 1) ^ 2 *
      (1 + Real.log (2 * y)) ^ 3 * y / Real.sqrt T
  change ((dyadicFactorBoxCell (theta + 1 / 4) Y i).card : ℝ) ≤
    A + C * Q * S at hlocalBound
  change Q * S ≤ 24 * y / Real.sqrt T at hgeometric
  have hyTwo : (2 : ℝ) ≤ y := by dsimp [y]; exact_mod_cast hY
  have hlog0 : 0 ≤ 1 + Real.log (2 * y) := by
    have hone : (1 : ℝ) ≤ 2 * y := by nlinarith
    have := Real.log_nonneg hone
    linarith
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  have hmul : C * (Q * S) ≤ C * (24 * y / Real.sqrt T) :=
    mul_le_mul_of_nonneg_left hgeometric hC0
  calc
    ((dyadicFactorBoxCell (theta + 1 / 4) Y i).card : ℝ) ≤
        A + C * (Q * S) := by
      simpa only [mul_assoc] using hlocalBound
    _ ≤ A + C * (24 * y / Real.sqrt T) := by
      simpa only [add_comm] using add_le_add_left hmul A
    _ = A + 7864320000000 * ((B : ℝ) + 1) ^ 2 *
        (1 + Real.log (2 * y)) ^ 3 * y / Real.sqrt T := by
      dsimp [C]
      ring

/-- Summing the common pointwise estimate costs only the explicit product of
the four dyadic scale counts.  This is the honest finite high-box union bound
before any eventual absorption of those scale counts or the displayed
polynomial/logarithmic factors. -/
theorem eventually_main3BalancedHighDEBoxUnion_card_le_scaleProduct_mul_envelope
    (hWeil : OneVariableQuadraticWeilDegreeBound)
    (c : ℝ) (hc : 0 < c)
    (hsmall : 10 * c ^ 2 ≤ (1 : ℝ) / 400) :
    ∀ᶠ Y : ℕ in atTop,
      ∀ (theta : ℝ),
        3 ≤ theta →
        theta ≤ c * Real.sqrt
          (Real.log (Y : ℝ) / Real.log (Real.log (Y : ℝ))) →
        let T : ℕ := main3BalancedR theta Y
        let B : ℕ := main3BalancedDegree theta
        let H0 : ℕ := 2 * (B + 1)
        let M : ℕ := main3BalancedM theta Y
        let K : ℕ :=
          dyadicScaleCount (dyadicFactorHeight (theta + 1 / 4) Y) *
            (dyadicScaleCount (dyadicFactorHeight (theta + 1 / 4) Y) *
              (dyadicScaleCount (2 * Y) * dyadicScaleCount (2 * Y)))
        let A : ℝ :=
          1348 * (M : ℝ) *
              ((H0 : ℝ) + 96 * theta * (B : ℝ) + 16) +
            7864320000000 * ((B : ℝ) + 1) ^ 2 *
              (1 + Real.log (2 * (Y : ℝ))) ^ 3 *
                (Y : ℝ) / Real.sqrt (T : ℝ)
        ((main3BalancedHighDEBoxUnion theta Y T).card : ℝ) ≤ (K : ℝ) * A := by
  have hpointEventual :=
    eventually_main3BalancedHighDEBoxIndex_card_le_commonEnvelope
      hWeil c hc hsmall
  filter_upwards [hpointEventual, eventually_ge_atTop 2] with Y hpoint hY
  intro theta htheta hadmissible
  let T : ℕ := main3BalancedR theta Y
  let B : ℕ := main3BalancedDegree theta
  let H0 : ℕ := 2 * (B + 1)
  let M : ℕ := main3BalancedM theta Y
  let K : ℕ :=
    dyadicScaleCount (dyadicFactorHeight (theta + 1 / 4) Y) *
      (dyadicScaleCount (dyadicFactorHeight (theta + 1 / 4) Y) *
        (dyadicScaleCount (2 * Y) * dyadicScaleCount (2 * Y)))
  let A : ℝ :=
    1348 * (M : ℝ) *
        ((H0 : ℝ) + 96 * theta * (B : ℝ) + 16) +
      7864320000000 * ((B : ℝ) + 1) ^ 2 *
        (1 + Real.log (2 * (Y : ℝ))) ^ 3 *
          (Y : ℝ) / Real.sqrt (T : ℝ)
  change ((main3BalancedHighDEBoxUnion theta Y T).card : ℝ) ≤ (K : ℝ) * A
  have hpointwise :
      ∀ i ∈ main3BalancedHighDEBoxIndices theta Y T,
        ((dyadicFactorBoxCell (theta + 1 / 4) Y i).card : ℝ) ≤ A := by
    intro i hi
    have hbound := hpoint theta htheta hadmissible i
    have hi' : i ∈ main3BalancedHighDEBoxIndices theta Y
        (main3BalancedR theta Y) := by simpa only [T] using hi
    simpa only [T, B, H0, M, A] using hbound hi'
  have hunion := main3BalancedHighDEBoxUnion_card_cast_le_card_mul
    theta Y T A hpointwise
  have hKnat := card_main3BalancedHighDEBoxIndices_le_scale_product
    theta Y T
  change (main3BalancedHighDEBoxIndices theta Y T).card ≤ K at hKnat
  have hKcast :
      ((main3BalancedHighDEBoxIndices theta Y T).card : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast hKnat
  have hyTwo : (2 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
  have hy0 : (0 : ℝ) ≤ (Y : ℝ) := by positivity
  have htheta0 : 0 ≤ theta := by linarith
  have hToneNat : 1 ≤ T := by
    simpa only [T] using
      (main3BalancedR_parameter_package theta Y htheta hY).1
  have hTpos : (0 : ℝ) < (T : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hToneNat)
  have hsqrtTpos : 0 < Real.sqrt (T : ℝ) := Real.sqrt_pos.2 hTpos
  have hlog0 : 0 ≤ 1 + Real.log (2 * (Y : ℝ)) := by
    have hone : (1 : ℝ) ≤ 2 * (Y : ℝ) := by nlinarith
    have := Real.log_nonneg hone
    linarith
  have hbracket0 :
      0 ≤ (H0 : ℝ) + 96 * theta * (B : ℝ) + 16 := by
    positivity
  have hfirst0 :
      0 ≤ 1348 * (M : ℝ) *
        ((H0 : ℝ) + 96 * theta * (B : ℝ) + 16) := by
    positivity
  have hsecond0 :
      0 ≤ 7864320000000 * ((B : ℝ) + 1) ^ 2 *
        (1 + Real.log (2 * (Y : ℝ))) ^ 3 *
          (Y : ℝ) / Real.sqrt (T : ℝ) := by
    positivity
  have hA0 : 0 ≤ A := by
    dsimp only [A]
    exact add_nonneg hfirst0 hsecond0
  calc
    ((main3BalancedHighDEBoxUnion theta Y T).card : ℝ) ≤
        ((main3BalancedHighDEBoxIndices theta Y T).card : ℝ) * A := hunion
    _ ≤ (K : ℝ) * A := mul_le_mul_of_nonneg_right hKcast hA0

end

end PellPaper
