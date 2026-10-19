import Pell.Main3LargeAnalyticShiftWeightAbsorption
import Pell.Main3LargeAnalyticBlockAuxiliaryPartition
import Pell.Main3LargeAnalyticComplexRadialDiscriminantCost
import Pell.Main3LargeAnalyticTargetFibreCoordinateLogBounds
import Pell.ShiftedSquareAuxiliarySurfaceLevelWeight
import Pell.ShiftedSquareFieldDiscriminantLowerBound
import Pell.Main3UnbalancedCeilingParameters
import Pell.Main3BalancedDyadicScaleCount
import Pell.AnnularMultiplicativeCellCover
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Workspace: elementary parameters in the Main3 outer sieve sum

The estimates here deliberately use one coarse bound for every auxiliary key.
This loses the manuscript's sharp intermediate `A^(7/8)` term but preserves
enough exponent margin for the final `1/400` saving.
-/

namespace PellPaper

noncomputable section

local instance main3LargeAnalyticOuterParameterBounds_numberField
    (a : ℤ) [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))] :
    NumberField (rationalQuadraticAlgebra (-a)) :=
  rationalQuadraticAlgebra_numberField (-a)

/-- The unbalanced localization ceiling retains its full `1/(8*theta^2)`
power saving. -/
theorem main3UnbalancedM_cast_le_two_mul_rpow_workspace
    (theta : ℝ) (Y : ℕ) (htheta : 3 ≤ theta) (hY : 2 ≤ Y) :
    (main3UnbalancedM theta Y : ℝ) ≤
      2 * (Y : ℝ) ^ (1 - 1 / (8 * theta ^ 2)) := by
  let y : ℝ := Y
  let m : ℝ := main3UnbalancedMExponent theta
  let z : ℝ := y ^ m
  have hyone : 1 ≤ y := by
    dsimp [y]
    exact_mod_cast (show 1 ≤ Y by omega)
  have hm0 : 0 ≤ m := by
    dsimp [m]
    exact (by norm_num : (0 : ℝ) ≤ 71 / 72).trans
      (main3UnbalancedMExponent_mem htheta).1
  have hzone : 1 ≤ z := by
    dsimp [z]
    calc
      (1 : ℝ) = y ^ (0 : ℝ) := by simp
      _ ≤ y ^ m := Real.rpow_le_rpow_of_exponent_le hyone hm0
  have hceil : (main3UnbalancedM theta Y : ℝ) < z + 1 := by
    dsimp [z, m, main3UnbalancedM]
    exact Nat.ceil_lt_add_one (Real.rpow_nonneg (by positivity) _)
  calc
    (main3UnbalancedM theta Y : ℝ) ≤ z + 1 := hceil.le
    _ ≤ 2 * z := by linarith
    _ = 2 * (Y : ℝ) ^ (1 - 1 / (8 * theta ^ 2)) := rfl

/-- The sharp auxiliary ceiling costs at most `33*sqrt |a|` on an active
large-analytic index. -/
theorem main3LargeAnalytic_auxiliaryC₀Ceiling_cast_le_thirtythree_sqrt_abs_workspace
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y) :
    (main3LargeAnalytic_auxiliaryC₀Ceiling h v : ℝ) ≤
      33 * Real.sqrt |(shiftedSquareA h v : ℝ)| := by
  have ha0 := main3LargeAnalytic_shift_ne_zero_of_largeAnalyticIndex hi
  have habsOne : (1 : ℝ) ≤ |(shiftedSquareA h v : ℝ)| := by
    exact_mod_cast Int.one_le_abs ha0
  have hsqrtOne : 1 ≤ Real.sqrt |(shiftedSquareA h v : ℝ)| := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt habsOne
  have hceil := (main3LargeAnalytic_auxiliaryC₀Ceiling_spec h v).2
  linarith

/-- Membership in the actual block gate exposes the positive scalar ranges
needed for every coarse key estimate. -/
theorem main3LargeAnalytic_blockAuxiliaryKeyGate_component_bounds_workspace
    {h : ℤ} {v : ℕ} {key : ShiftedSquareAuxiliaryKey}
    (hkey : key ∈ main3LargeAnalytic_blockAuxiliaryKeyGate h v) :
    1 ≤ key.C₀ ∧
      key.C₀ ≤ main3LargeAnalytic_auxiliaryC₀Ceiling h v ∧
      0 < key.r ∧ 0 < key.ell := by
  simp only [main3LargeAnalytic_blockAuxiliaryKeyGate,
    shiftedSquareAuxiliaryKeys, Finset.mem_biUnion,
    Finset.mem_image] at hkey
  obtain ⟨C₀, hC₀, bζ, hbζ, p, hp, hkeyEq⟩ := hkey
  rcases p with ⟨r, ell⟩
  have hrange := Finset.mem_Icc.mp hC₀
  have hbCases := mem_shiftedSquareBζValues.mp hbζ
  have hbPos : 0 < C₀ ^ 2 * bζ.natAbs := by
    apply Nat.mul_pos (pow_pos (by omega) 2)
    rcases hbCases with rfl | rfl <;> norm_num
  have hpData :=
    (mem_specialParabolaDenominatorPairs_iff hbPos.ne').mp hp
  subst key
  exact ⟨hrange.1, hrange.2, hpData.1, hpData.2.1⟩

/-- The fixed-key target scale is positive and is bounded using only the
common auxiliary ceiling. -/
theorem main3LargeAnalyticFixedKeyTargetScaleUpper_le_ceiling_workspace
    {Y : ℕ} {h : ℤ} {v : ℕ} {key : ShiftedSquareAuxiliaryKey}
    (hY : 0 < Y)
    (hkey : key ∈ main3LargeAnalytic_blockAuxiliaryKeyGate h v) :
    0 < main3LargeAnalyticFixedKeyTargetScaleUpper Y key ∧
      main3LargeAnalyticFixedKeyTargetScaleUpper Y key ≤
        2 * (Y : ℝ) *
          (main3LargeAnalytic_auxiliaryC₀Ceiling h v : ℝ) ^ 2 := by
  have hk :=
    main3LargeAnalytic_blockAuxiliaryKeyGate_component_bounds_workspace hkey
  have hC₀pos : (0 : ℝ) < key.C₀ := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk.1)
  have hell : (1 : ℝ) ≤ key.ell := by exact_mod_cast hk.2.2.2
  have hC₀R : (key.C₀ : ℝ) ≤
      main3LargeAnalytic_auxiliaryC₀Ceiling h v := by exact_mod_cast hk.2.1
  unfold main3LargeAnalyticFixedKeyTargetScaleUpper
  constructor
  · positivity
  · have hdenom : (1 : ℝ) ≤ (key.ell : ℝ) ^ 2 := by nlinarith
    calc
      2 * (Y : ℝ) * (key.C₀ : ℝ) ^ 2 / (key.ell : ℝ) ^ 2 ≤
          2 * (Y : ℝ) * (key.C₀ : ℝ) ^ 2 :=
        div_le_self (by positivity) hdenom
      _ ≤ 2 * (Y : ℝ) *
          (main3LargeAnalytic_auxiliaryC₀Ceiling h v : ℝ) ^ 2 := by
        gcongr

/-- For squarefree active shifts, the field-discriminant square root
dominates `sqrt |a|`. -/
theorem main3LargeAnalytic_sqrt_abs_shift_le_sqrt_fieldDiscriminant_workspace
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y) :
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    Real.sqrt |(shiftedSquareA h v : ℝ)| ≤
      Real.sqrt
        |(NumberField.discr
          (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ)| := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  have hdiscInt :=
    abs_le_abs_rationalQuadraticAlgebra_neg_fieldDiscriminant_of_squarefree
      (shiftedSquareA h v) (main3LargeAnalytic_shift_squarefree hi)
  have hdisc : |(shiftedSquareA h v : ℝ)| ≤
      |(NumberField.discr
        (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ)| := by
    exact_mod_cast hdiscInt
  exact Real.sqrt_le_sqrt hdisc

/-- Uniformly over the block gate, the exact area scale `E/Delta` costs only
`2178*Y*sqrt |a|`. -/
theorem main3LargeAnalytic_targetScale_div_discriminant_le_workspace
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (hY : 0 < Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    {key : ShiftedSquareAuxiliaryKey}
    (hkey : key ∈ main3LargeAnalytic_blockAuxiliaryKeyGate h v) :
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    main3LargeAnalyticFixedKeyTargetScaleUpper Y key /
        Real.sqrt
          |(NumberField.discr
            (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ)| ≤
      2178 * (Y : ℝ) * Real.sqrt |(shiftedSquareA h v : ℝ)| := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let A : ℝ := |(shiftedSquareA h v : ℝ)|
  let Delta : ℝ := Real.sqrt
    |(NumberField.discr
      (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ)|
  let R : ℝ := main3LargeAnalytic_auxiliaryC₀Ceiling h v
  let E : ℝ := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
  have ha0 := main3LargeAnalytic_shift_ne_zero_of_largeAnalyticIndex hi
  have hA : 0 < A := by dsimp [A]; exact abs_pos.mpr (by exact_mod_cast ha0)
  have hsqrtA : 0 < Real.sqrt A := Real.sqrt_pos.2 hA
  have hDeltaA : Real.sqrt A ≤ Delta := by
    simpa only [A, Delta] using
      main3LargeAnalytic_sqrt_abs_shift_le_sqrt_fieldDiscriminant_workspace hi
  have hDelta : 0 < Delta := hsqrtA.trans_le hDeltaA
  have hR : R ≤ 33 * Real.sqrt A := by
    simpa only [R, A] using
      main3LargeAnalytic_auxiliaryC₀Ceiling_cast_le_thirtythree_sqrt_abs_workspace hi
  have hE :=
    (main3LargeAnalyticFixedKeyTargetScaleUpper_le_ceiling_workspace
      (Y := Y) (h := h) (v := v) hY hkey).2
  have hRsq : R ^ 2 ≤ 1089 * A := by
    calc
      R ^ 2 ≤ (33 * Real.sqrt A) ^ 2 :=
        (sq_le_sq₀ (by dsimp [R]; positivity) (by positivity)).2 hR
      _ = 1089 * A := by rw [mul_pow, Real.sq_sqrt hA.le]; ring
  have hEA : E ≤ 2178 * (Y : ℝ) * A := by
    calc
      E ≤ 2 * (Y : ℝ) * R ^ 2 := by simpa only [E, R] using hE
      _ ≤ 2 * (Y : ℝ) * (1089 * A) := by gcongr
      _ = 2178 * (Y : ℝ) * A := by ring
  apply (div_le_iff₀ hDelta).2
  calc
    E ≤ 2178 * (Y : ℝ) * A := hEA
    _ = 2178 * (Y : ℝ) * (Real.sqrt A * Real.sqrt A) := by
      rw [Real.mul_self_sqrt hA.le]
    _ = (2178 * (Y : ℝ) * Real.sqrt A) * Real.sqrt A := by ring
    _ ≤ (2178 * (Y : ℝ) * Real.sqrt A) * Delta := by gcongr

/-- The fixed-key target square root is bounded by the shift weight with an
absolute constant. -/
theorem main3LargeAnalytic_sqrt_targetScale_le_workspace
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (hY : 0 < Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    {key : ShiftedSquareAuxiliaryKey}
    (hkey : key ∈ main3LargeAnalytic_blockAuxiliaryKeyGate h v) :
    Real.sqrt (main3LargeAnalyticFixedKeyTargetScaleUpper Y key) ≤
      33 * Real.sqrt
        ((Y : ℝ) * main3LargeAnalyticShiftWeight h v) := by
  let A : ℝ := |(shiftedSquareA h v : ℝ)|
  let W : ℝ := main3LargeAnalyticShiftWeight h v
  let R : ℝ := main3LargeAnalytic_auxiliaryC₀Ceiling h v
  let E : ℝ := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
  have ha0 := main3LargeAnalytic_shift_ne_zero_of_largeAnalyticIndex hi
  have hA : 0 < A := by dsimp [A]; exact abs_pos.mpr (by exact_mod_cast ha0)
  have hW : 0 < W := by dsimp [W, main3LargeAnalyticShiftWeight]; positivity
  have hR : R ≤ 33 * Real.sqrt A := by
    simpa only [R, A] using
      main3LargeAnalytic_auxiliaryC₀Ceiling_cast_le_thirtythree_sqrt_abs_workspace hi
  have hRsq : R ^ 2 ≤ 1089 * A := by
    calc
      R ^ 2 ≤ (33 * Real.sqrt A) ^ 2 :=
        (sq_le_sq₀ (by dsimp [R]; positivity) (by positivity)).2 hR
      _ = 1089 * A := by rw [mul_pow, Real.sq_sqrt hA.le]; ring
  have hE :=
    (main3LargeAnalyticFixedKeyTargetScaleUpper_le_ceiling_workspace
      (Y := Y) (h := h) (v := v) hY hkey).2
  have hEW : E ≤ 1089 * (Y : ℝ) * W := by
    calc
      E ≤ 2 * (Y : ℝ) * R ^ 2 := by simpa only [E, R] using hE
      _ ≤ 2 * (Y : ℝ) * (1089 * A) := by gcongr
      _ = 1089 * (Y : ℝ) * W := by
        dsimp [W, main3LargeAnalyticShiftWeight, A]
        ring
  calc
    Real.sqrt E ≤ Real.sqrt (1089 * (Y : ℝ) * W) :=
      Real.sqrt_le_sqrt hEW
    _ = 33 * Real.sqrt ((Y : ℝ) * W) := by
      rw [show 1089 * (Y : ℝ) * W = 1089 * ((Y : ℝ) * W) by ring,
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 1089)]
      norm_num

/-- The square-root reciprocal-minimum scale is bounded in the form used by
the outer power comparison. -/
theorem main3LargeAnalytic_sqrt_targetScale_mul_mesh_div_discriminant_le_workspace
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (hY : 0 < Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y)
    {key : ShiftedSquareAuxiliaryKey}
    (hkey : key ∈ main3LargeAnalytic_blockAuxiliaryKeyGate h v) :
    letI : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
      ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
    Real.sqrt
        (main3LargeAnalyticFixedKeyTargetScaleUpper Y key *
          (main3UnbalancedM theta Y : ℝ) /
          Real.sqrt
            |(NumberField.discr
              (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ)|) ≤
      47 * Real.sqrt
          ((Y : ℝ) * (main3UnbalancedM theta Y : ℝ)) *
        main3LargeAnalyticShiftWeight h v ^ ((1 : ℝ) / 4) := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot
      (-(shiftedSquareA h v))) :=
    ⟨main3LargeAnalytic_shift_noRationalRoot hi⟩
  let A : ℝ := |(shiftedSquareA h v : ℝ)|
  let W : ℝ := main3LargeAnalyticShiftWeight h v
  let E : ℝ := main3LargeAnalyticFixedKeyTargetScaleUpper Y key
  let M : ℝ := main3UnbalancedM theta Y
  let Delta : ℝ := Real.sqrt
    |(NumberField.discr
      (rationalQuadraticAlgebra (-(shiftedSquareA h v))) : ℝ)|
  have ha0 := main3LargeAnalytic_shift_ne_zero_of_largeAnalyticIndex hi
  have hA : 0 < A := by dsimp [A]; exact abs_pos.mpr (by exact_mod_cast ha0)
  have hW : 0 < W := by dsimp [W, main3LargeAnalyticShiftWeight]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hy : 0 ≤ (Y : ℝ) := by positivity
  have hratio :=
    main3LargeAnalytic_targetScale_div_discriminant_le_workspace
      hY hi hkey
  have hratio' : E / Delta ≤ 2178 * (Y : ℝ) * Real.sqrt A := by
    simpa only [E, Delta, A] using hratio
  have hAW : Real.sqrt A ≤ Real.sqrt W := by
    apply Real.sqrt_le_sqrt
    dsimp [A, W, main3LargeAnalyticShiftWeight]
    linarith [abs_nonneg (shiftedSquareA h v : ℝ)]
  have hinside : E * M / Delta ≤
      2178 * ((Y : ℝ) * M) * Real.sqrt W := by
    calc
      E * M / Delta = (E / Delta) * M := by ring
      _ ≤ (2178 * (Y : ℝ) * Real.sqrt A) * M := by gcongr
      _ ≤ (2178 * (Y : ℝ) * Real.sqrt W) * M := by gcongr
      _ = 2178 * ((Y : ℝ) * M) * Real.sqrt W := by ring
  have hbase : 0 ≤ (Y : ℝ) * M := mul_nonneg hy hM
  have hsqrt2178 : Real.sqrt (2178 : ℝ) ≤ 47 := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num
  have hsqrtSqrtW : Real.sqrt (Real.sqrt W) = W ^ ((1 : ℝ) / 4) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
      ← Real.rpow_mul hW.le]
    norm_num
  calc
    Real.sqrt (E * M / Delta) ≤
        Real.sqrt (2178 * ((Y : ℝ) * M) * Real.sqrt W) :=
      Real.sqrt_le_sqrt hinside
    _ = Real.sqrt 2178 * Real.sqrt ((Y : ℝ) * M) *
          Real.sqrt (Real.sqrt W) := by
      rw [show 2178 * ((Y : ℝ) * M) * Real.sqrt W =
          2178 * (((Y : ℝ) * M) * Real.sqrt W) by ring,
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2178),
        Real.sqrt_mul hbase]
      ring
    _ ≤ 47 * Real.sqrt ((Y : ℝ) * M) * Real.sqrt (Real.sqrt W) := by
      gcongr
    _ = 47 * Real.sqrt ((Y : ℝ) * M) * W ^ ((1 : ℝ) / 4) := by
      rw [hsqrtSqrtW]

/-- The additional real-place annular scale count is only logarithmic in the
standard shift/base height. -/
theorem main3LargeAnalytic_annularDyadicScaleCount_cast_le_workspace
    {theta : ℝ} {Y : ℕ} {h : ℤ} {v D N : ℕ}
    (hY : 2 ≤ Y)
    (hi : (h, v, D, N) ∈
      main3UnbalancedEnlargedLargeAnalyticDyadicCoverIndices theta Y) :
    (annularDyadicScaleCount
        (shiftedSquareEmbeddingScaleLoss (shiftedSquareA h v)) : ℝ) ≤
      100 * (1 + Real.log
        (2 * main3LargeAnalyticShiftWeight h v * (Y : ℝ))) := by
  let a : ℤ := shiftedSquareA h v
  let A : ℝ := |(a : ℝ)|
  let W : ℝ := main3LargeAnalyticShiftWeight h v
  let F : ℝ := shiftedSquareEmbeddingScaleLoss a
  let C : ℕ := ⌈F⌉₊
  let H : ℕ := C ^ 4
  have ha0 : a ≠ 0 := by
    dsimp [a]
    exact main3LargeAnalytic_shift_ne_zero_of_largeAnalyticIndex hi
  have hAone : 1 ≤ A := by
    dsimp [A]
    exact_mod_cast Int.one_le_abs ha0
  have hApos : 0 < A := zero_lt_one.trans_le hAone
  have hWpos : 0 < W := by dsimp [W, main3LargeAnalyticShiftWeight, A]; positivity
  have hWtwo : 2 ≤ W := by
    dsimp [W, main3LargeAnalyticShiftWeight, A, a]
    linarith
  have hF : F = 256 * W := by
    dsimp [F, shiftedSquareEmbeddingScaleLoss, W,
      main3LargeAnalyticShiftWeight, A, a]
    ring
  have hFone : 1 ≤ F := by rw [hF]; nlinarith
  have hFpos : 0 < F := zero_lt_one.trans_le hFone
  have hCone : (1 : ℝ) ≤ C := by
    exact_mod_cast (show 1 ≤ C by
      dsimp [C]
      rw [Nat.one_le_ceil_iff]
      linarith)
  have hCupper : (C : ℝ) ≤ 2 * F := by
    have hceil : (C : ℝ) < F + 1 := by
      dsimp [C]
      exact Nat.ceil_lt_add_one hFpos.le
    linarith
  have hHplus : (((H + 1 : ℕ) : ℝ)) ≤ 32 * F ^ 4 := by
    simp only [H, Nat.cast_add, Nat.cast_pow, Nat.cast_one]
    have hCpowOne : (1 : ℝ) ≤ (C : ℝ) ^ 4 := one_le_pow₀ hCone
    calc
      (C : ℝ) ^ 4 + 1 ≤ 2 * (C : ℝ) ^ 4 := by linarith
      _ ≤ 2 * (2 * F) ^ 4 := by gcongr
      _ = 32 * F ^ 4 := by ring
  have hscale := dyadicScaleCount_cast_le_one_add_two_mul_log_add_one H
  have hlogMono : Real.log (((H + 1 : ℕ) : ℝ)) ≤
      Real.log (32 * F ^ 4) := by
    exact Real.log_le_log (by positivity) hHplus
  have hlogTwo0 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hlogTwo1 : Real.log (2 : ℝ) ≤ 1 := by
    linarith [Real.log_two_lt_d9.le]
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg hAone
  have hlogW : Real.log W = Real.log 2 + Real.log A := by
    dsimp [W, main3LargeAnalyticShiftWeight, A, a]
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (abs_pos.mpr (by exact_mod_cast ha0)).ne']
  have hlogF : Real.log F = 8 * Real.log 2 + Real.log W := by
    rw [hF, Real.log_mul (by norm_num : (256 : ℝ) ≠ 0) hWpos.ne',
      show (256 : ℝ) = 2 ^ (8 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hlogArg : Real.log (32 * F ^ 4) =
      5 * Real.log 2 + 4 * Real.log F := by
    rw [Real.log_mul (by norm_num : (32 : ℝ) ≠ 0)
      (pow_ne_zero 4 hFpos.ne'), Real.log_pow,
      show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, Real.log_pow]
    norm_num
  let L : ℝ := 1 + Real.log (2 * W * (Y : ℝ))
  have hYone : (1 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast (show 1 ≤ Y by omega)
  have hargOne : 1 ≤ 2 * W * (Y : ℝ) := by nlinarith
  have hLone : 1 ≤ L := by
    dsimp [L]
    linarith [Real.log_nonneg hargOne]
  have hlogAle : Real.log A ≤ L := by
    have hAarg : A ≤ 2 * W * (Y : ℝ) := by
      dsimp [W, main3LargeAnalyticShiftWeight, A, a]
      nlinarith
    have hmono := Real.log_le_log hApos hAarg
    dsimp [L]
    linarith
  change (dyadicScaleCount H : ℝ) ≤ 100 * L
  calc
    (dyadicScaleCount H : ℝ) ≤
        1 + 2 * Real.log (((H + 1 : ℕ) : ℝ)) := hscale
    _ ≤ 1 + 2 * Real.log (32 * F ^ 4) := by linarith
    _ = 1 + 2 * (5 * Real.log 2 + 4 * Real.log F) := by rw [hlogArg]
    _ = 1 + 2 * (41 * Real.log 2 + 4 * Real.log A) := by
      rw [hlogF, hlogW]
      ring
    _ ≤ 83 + 8 * Real.log A := by nlinarith
    _ ≤ 91 * L := by nlinarith
    _ ≤ 100 * L := by nlinarith

end

end PellPaper
