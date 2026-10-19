import Pell.Main3LargeAnalyticOuterParameterBounds

/-!
# Workspace: common logarithmic bounds for the Main3 outer sieve sum

All logarithms in the real and complex active-key envelopes are bounded by
one coarse scale

`S = 1 + log (2 * main3LargeAnalyticShiftWeight h v * Y)`.

The constants are deliberately loose.  This keeps the later key summation and
power absorption independent of the archimedean sign branch.
-/

namespace PellPaper

noncomputable section

local instance main3LargeAnalyticOuterLogBounds_numberField
    (a : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

/-- On every active large-analytic block and every key in its actual gate, one
common logarithm controls both logarithmic factors in both archimedean
branches. -/
theorem main3LargeAnalytic_activeKey_outerLogBounds_workspace
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (htheta : 3 ≤ theta) (hY : 2 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    {key : ShiftedSquareAuxiliaryKey}
    (hkey : key ∈ main3LargeAnalytic_blockAuxiliaryKeyGate h v) :
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    let S := 1 + Real.log
      (2 * main3LargeAnalyticShiftWeight h v * (Y : ℝ))
    let E := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
    let Delta := Real.sqrt
      |(NumberField.discr
        (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ)|
    let Mmesh := (main3UnbalancedM theta Y : ℝ)
    let complexK := (6 * E / Mmesh) / Delta
    let complexL := complexK / 2 + 2
    let complexH₀ := 2 * Real.sqrt E
    let realK := (2 * E / Mmesh) / Delta
    let realL := realK / 2 + 5
    let realH₀ := 144 * Real.sqrt E
    1 ≤ S ∧
      2 + Real.log complexH₀ ≤ 16 * S ∧
      1 + Real.log (2 * complexL) ≤ 16 * S ∧
      2 + Real.log realH₀ ≤ 16 * S ∧
      1 + Real.log (2 * realL) ≤ 16 * S := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let a : ℤ := shiftedSquareA h v
  let A : ℝ := |(a : ℝ)|
  let W : ℝ := main3LargeAnalyticShiftWeight h v
  let y : ℝ := Y
  let T : ℝ := 2 * W * y
  let S : ℝ := 1 + Real.log T
  let E : ℝ := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
  let Delta : ℝ := Real.sqrt
    |(NumberField.discr
      (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ)|
  let Mmesh : ℝ := main3UnbalancedM theta Y
  let complexK : ℝ := (6 * E / Mmesh) / Delta
  let complexL : ℝ := complexK / 2 + 2
  let complexH₀ : ℝ := 2 * Real.sqrt E
  let realK : ℝ := (2 * E / Mmesh) / Delta
  let realL : ℝ := realK / 2 + 5
  let realH₀ : ℝ := 144 * Real.sqrt E
  have ha0 : a ≠ 0 := by
    dsimp [a]
    exact main3LargeAnalytic_shift_ne_zero_of_largeAnalyticIndex hi
  have hAone : 1 ≤ A := by
    dsimp [A]
    exact_mod_cast Int.one_le_abs ha0
  have hApos : 0 < A := zero_lt_one.trans_le hAone
  have hsqrtAle : Real.sqrt A ≤ A :=
    (Real.sqrt_le_self_iff).2 (Or.inr hAone)
  have hWtwo : 2 ≤ W := by
    dsimp [W, main3LargeAnalyticShiftWeight, A, a]
    linarith
  have hWpos : 0 < W := by linarith
  have hytwo : (2 : ℝ) ≤ y := by
    dsimp [y]
    exact_mod_cast hY
  have hypos : 0 < y := by linarith
  have hy0 : 0 ≤ y := hypos.le
  have hqone : 1 ≤ y * W := by
    calc
      (1 : ℝ) ≤ 2 * 2 := by norm_num
      _ ≤ y * W := by gcongr
  have hsqrtq : Real.sqrt (y * W) ≤ y * W :=
    (Real.sqrt_le_self_iff).2 (Or.inr hqone)
  have hTeight : 8 ≤ T := by
    dsimp [T]
    calc
      (8 : ℝ) = 2 * 2 * 2 := by norm_num
      _ ≤ 2 * W * y := by gcongr
  have hTpos : 0 < T := by linarith
  have hTone : 1 ≤ T := by linarith
  have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg hTone
  have hSone : 1 ≤ S := by
    dsimp [S]
    linarith
  have hEpackage :=
    main3LargeAnalyticFixedKeyTargetScaleUpper_le_ceiling_workspace
      (Y := Y) (h := h) (v := v) (by omega : 0 < Y) hkey
  have hEpos : 0 < E := by
    simpa only [E] using hEpackage.1
  have hMnat : 0 < main3UnbalancedM theta Y :=
    (main3UnbalancedM_parameter_package theta Y htheta hY).1
  have hMone : 1 ≤ Mmesh := by
    dsimp [Mmesh]
    exact_mod_cast hMnat
  have hMpos : 0 < Mmesh := zero_lt_one.trans_le hMone
  have hsqrtApos : 0 < Real.sqrt A := Real.sqrt_pos.2 hApos
  have hsqrtADelta : Real.sqrt A ≤ Delta := by
    simpa only [A, a, Delta] using
      main3LargeAnalytic_sqrt_abs_shift_le_sqrt_fieldDiscriminant_workspace hi
  have hDeltaPos : 0 < Delta := hsqrtApos.trans_le hsqrtADelta
  have hratioNonneg : 0 ≤ E / Delta := by positivity
  have hdivideM : E / Mmesh / Delta ≤ E / Delta := by
    calc
      E / Mmesh / Delta = (E / Delta) / Mmesh := by ring
      _ ≤ E / Delta := div_le_self hratioNonneg hMone
  have hsqrtE : Real.sqrt E ≤ 33 * Real.sqrt (y * W) := by
    simpa only [E, y, W] using
      main3LargeAnalytic_sqrt_targetScale_le_workspace
        (by omega : 0 < Y) hi hkey
  have hratio : E / Delta ≤ 2178 * y * Real.sqrt A := by
    simpa only [E, Delta, y, A, a] using
      main3LargeAnalytic_targetScale_div_discriminant_le_workspace
        (by omega : 0 < Y) hi hkey
  have hySqrtA : y * Real.sqrt A ≤ y * A := by gcongr
  have hTformula : T = 4 * y * A := by
    dsimp [T, W, main3LargeAnalyticShiftWeight, A, a]
    ring
  have hcomplexK : complexK ≤ 3267 * T := by
    calc
      complexK = 6 * (E / Mmesh / Delta) := by
        dsimp [complexK]
        ring
      _ ≤ 6 * (E / Delta) := by gcongr
      _ ≤ 6 * (2178 * y * Real.sqrt A) := by gcongr
      _ ≤ 6 * (2178 * y * A) := by gcongr
      _ = 3267 * T := by rw [hTformula]; ring
  have hrealK : realK ≤ 1089 * T := by
    calc
      realK = 2 * (E / Mmesh / Delta) := by
        dsimp [realK]
        ring
      _ ≤ 2 * (E / Delta) := by gcongr
      _ ≤ 2 * (2178 * y * Real.sqrt A) := by gcongr
      _ ≤ 2 * (2178 * y * A) := by gcongr
      _ = 1089 * T := by rw [hTformula]; ring
  have hcomplexHlinear : complexH₀ ≤ 4000 * T := by
    calc
      complexH₀ ≤ 66 * Real.sqrt (y * W) := by
        dsimp [complexH₀]
        linarith
      _ ≤ 66 * (y * W) := by gcongr
      _ = 33 * T := by dsimp [T]; ring
      _ ≤ 4000 * T := by
        gcongr
        norm_num
  have hrealHlinear : realH₀ ≤ 4000 * T := by
    calc
      realH₀ ≤ 4752 * Real.sqrt (y * W) := by
        dsimp [realH₀]
        nlinarith
      _ ≤ 4752 * (y * W) := by gcongr
      _ = 2376 * T := by dsimp [T]; ring
      _ ≤ 4000 * T := by
        gcongr
        norm_num
  have hcomplexLlinear : 2 * complexL ≤ 4000 * T := by
    dsimp [complexL]
    nlinarith
  have hrealLlinear : 2 * realL ≤ 4000 * T := by
    dsimp [realL]
    nlinarith
  have hTfive : (4000 : ℝ) ≤ T ^ 5 := by
    calc
      (4000 : ℝ) ≤ 8 ^ 5 := by norm_num
      _ ≤ T ^ 5 := by gcongr
  have hlinearPower : 4000 * T ≤ T ^ 6 := by
    calc
      4000 * T ≤ T ^ 5 * T :=
        mul_le_mul_of_nonneg_right hTfive hTpos.le
      _ = T ^ 6 := by ring
  have hcomplexHpos : 0 < complexH₀ := by
    dsimp [complexH₀]
    positivity
  have hrealHpos : 0 < realH₀ := by
    dsimp [realH₀]
    positivity
  have hcomplexLpos : 0 < 2 * complexL := by
    dsimp [complexL, complexK]
    positivity
  have hrealLpos : 0 < 2 * realL := by
    dsimp [realL, realK]
    positivity
  have htwoLogFactor : ∀ x : ℝ, 0 < x → x ≤ T ^ 6 →
      2 + Real.log x ≤ 16 * S := by
    intro x hx hxpower
    have hlog : Real.log x ≤ 6 * Real.log T := by
      calc
        Real.log x ≤ Real.log (T ^ 6) := Real.log_le_log hx hxpower
        _ = 6 * Real.log T := by rw [Real.log_pow]; norm_num
    dsimp [S]
    nlinarith
  have honeLogFactor : ∀ x : ℝ, 0 < x → x ≤ T ^ 6 →
      1 + Real.log x ≤ 16 * S := by
    intro x hx hxpower
    have hlog : Real.log x ≤ 6 * Real.log T := by
      calc
        Real.log x ≤ Real.log (T ^ 6) := Real.log_le_log hx hxpower
        _ = 6 * Real.log T := by rw [Real.log_pow]; norm_num
    dsimp [S]
    nlinarith
  have hcomplexHpower : complexH₀ ≤ T ^ 6 :=
    hcomplexHlinear.trans hlinearPower
  have hcomplexLpower : 2 * complexL ≤ T ^ 6 :=
    hcomplexLlinear.trans hlinearPower
  have hrealHpower : realH₀ ≤ T ^ 6 :=
    hrealHlinear.trans hlinearPower
  have hrealLpower : 2 * realL ≤ T ^ 6 :=
    hrealLlinear.trans hlinearPower
  simpa only [S, T, W, y, E, Delta, Mmesh, complexK, complexL,
      complexH₀, realK, realL, realH₀] using
    ⟨hSone,
      htwoLogFactor complexH₀ hcomplexHpos hcomplexHpower,
      honeLogFactor (2 * complexL) hcomplexLpos hcomplexLpower,
      htwoLogFactor realH₀ hrealHpos hrealHpower,
      honeLogFactor (2 * realL) hrealLpos hrealLpower⟩

end

end PellPaper

#print axioms PellPaper.main3LargeAnalytic_activeKey_outerLogBounds_workspace
