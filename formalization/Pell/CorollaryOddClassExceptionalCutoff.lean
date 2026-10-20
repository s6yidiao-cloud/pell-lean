import Pell.ClassCutoffGrowth
import Pell.UniformExceptionalDecay

/-!
# The moving exceptional-set cutoff for Corollary 1.2

This file specializes a uniform Pell exceptional estimate at
`T = kappa * sqrt (log X / log (log X))`.  The constant `kappa` is chosen
once, after the two absolute constants in the uniform estimate and before
`X`.  At this cutoff, the shifted count `E (T + 1) X` has a fourth-power
logarithmic saving.  No class-number or L-value estimate is used here.
-/

namespace PellPaper

open Filter

noncomputable section

/-- Two positive constants admit a positive cutoff constant which is small
enough both for uniform admissibility and for four powers of logarithmic
decay. -/
theorem exists_oddClassCutoffConstant {cSave cExc : ℝ}
    (hcSave : 0 < cSave) (hcExc : 0 < cExc) :
    ∃ kappa : ℝ, 0 < kappa ∧ 2 * kappa ≤ cExc ∧
      16 * kappa ^ 2 ≤ cSave := by
  let kappa : ℝ := min (cExc / 4) (Real.sqrt cSave / 8)
  have hkappa : 0 < kappa := by
    dsimp [kappa]
    exact lt_min (div_pos hcExc (by norm_num))
      (div_pos (Real.sqrt_pos.2 hcSave) (by norm_num))
  have hkExc : 2 * kappa ≤ cExc := by
    have h := min_le_left (cExc / 4) (Real.sqrt cSave / 8)
    dsimp [kappa]
    dsimp [kappa] at hkappa
    nlinarith
  have hkRoot : kappa ≤ Real.sqrt cSave / 8 := by
    dsimp [kappa]
    exact min_le_right _ _
  have hkSq : kappa ^ 2 ≤ (Real.sqrt cSave / 8) ^ 2 := by
    nlinarith [sq_nonneg (kappa - Real.sqrt cSave / 8)]
  have hrootSq : (Real.sqrt cSave) ^ 2 = cSave :=
    Real.sq_sqrt hcSave.le
  refine ⟨kappa, hkappa, hkExc, ?_⟩
  rw [div_pow, hrootSq] at hkSq
  norm_num at hkSq ⊢
  nlinarith

/-- A pointwise normalized exceptional estimate at the moving cutoff loses
at most `(log X)^(-4)`, provided the cutoff constant satisfies the two
displayed absolute smallness conditions. -/
theorem exceptional_ratio_at_oddClassCutoff_le_log_pow
    {cSave cExc C kappa X : ℝ}
    (hC : 0 < C) (hkappa : 0 < kappa) (hkExc : 2 * kappa ≤ cExc)
    (hkSave : 16 * kappa ^ 2 ≤ cSave)
    (hX : Real.exp (Real.exp 1) ≤ X)
    (hT : 2 ≤ classAverageCutoff kappa X)
    (hbound : ∀ θ : ℝ, 3 ≤ θ → UniformAdmissible cExc θ X →
      E θ X / X ≤
        C * Real.exp (-cSave * Real.log X / (θ + 1) ^ 2)) :
    E (classAverageCutoff kappa X + 1) X / X ≤
      C / (Real.log X) ^ 4 := by
  let S : ℝ := Real.sqrt (Real.log X / Real.log (Real.log X))
  let T : ℝ := classAverageCutoff kappa X
  let θ : ℝ := T + 1
  have hlogs := classAverage_large_log_bounds hX
  have hlog : 0 < Real.log X := classAverageCutoff_log_pos hlogs.1
  have hloglog : 0 < Real.log (Real.log X) :=
    classAverageCutoff_log_log_pos hlogs.1
  have hratio : 0 < Real.log X / Real.log (Real.log X) :=
    div_pos hlog hloglog
  have hS : 0 < S := by
    dsimp [S]
    exact Real.sqrt_pos.2 hratio
  have hTdef : T = kappa * S := by rfl
  have hTpos : 0 < T := by rw [hTdef]; positivity
  have hθ : 3 ≤ θ := by
    dsimp [θ, T]
    linarith
  have hTtwo : T + 2 ≤ 2 * T := by
    dsimp [T] at hT ⊢
    linarith
  have hSnonneg : 0 ≤ S := hS.le
  have hadmissible : UniformAdmissible cExc θ X := by
    unfold UniformAdmissible
    calc
      (uniformQ θ : ℝ) ≤ θ + 1 := uniformQ_le_theta_add_one hθ
      _ = T + 2 := by dsimp [θ]; ring
      _ ≤ 2 * T := hTtwo
      _ = (2 * kappa) * S := by rw [hTdef]; ring
      _ ≤ cExc * S := mul_le_mul_of_nonneg_right hkExc hSnonneg
      _ = cExc * Real.sqrt
          (Real.log X / Real.log (Real.log X)) := rfl
  have hraw := hbound θ hθ hadmissible
  have hthetaSq : (θ + 1) ^ 2 ≤
      4 * kappa ^ 2 * (Real.log X / Real.log (Real.log X)) := by
    have hsq : (T + 2) ^ 2 ≤ 4 * kappa ^ 2 * S ^ 2 := by
      calc
        (T + 2) ^ 2 ≤ (2 * T) ^ 2 := by nlinarith
        _ = 4 * kappa ^ 2 * S ^ 2 := by rw [hTdef]; ring
    have hSsq : S ^ 2 = Real.log X / Real.log (Real.log X) := by
      dsimp [S]
      exact Real.sq_sqrt hratio.le
    rw [hSsq] at hsq
    calc
      (θ + 1) ^ 2 = (T + 2) ^ 2 := by dsimp [θ]; ring
      _ ≤ _ := hsq
  have hthetaPos : 0 < θ + 1 := by linarith
  have hdecay :
      -cSave * Real.log X / (θ + 1) ^ 2 ≤
        -4 * Real.log (Real.log X) := by
    have hpositive : 4 * Real.log (Real.log X) ≤
        cSave * Real.log X / (θ + 1) ^ 2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hthetaPos)).2
      have hcoeff : 0 ≤ 4 * Real.log (Real.log X) :=
        mul_nonneg (by norm_num) hloglog.le
      have hmul := mul_le_mul_of_nonneg_left hthetaSq hcoeff
      have hklog : 16 * kappa ^ 2 * Real.log X ≤
          cSave * Real.log X :=
        mul_le_mul_of_nonneg_right hkSave hlog.le
      calc
        4 * Real.log (Real.log X) * (θ + 1) ^ 2 ≤
            4 * Real.log (Real.log X) *
              (4 * kappa ^ 2 *
                (Real.log X / Real.log (Real.log X))) := hmul
        _ = 16 * kappa ^ 2 * Real.log X := by
          field_simp [hloglog.ne']
          ring
        _ ≤ cSave * Real.log X := hklog
    calc
      -cSave * Real.log X / (θ + 1) ^ 2 =
          -(cSave * Real.log X / (θ + 1) ^ 2) := by ring
      _ ≤ -(4 * Real.log (Real.log X)) := neg_le_neg hpositive
      _ = -4 * Real.log (Real.log X) := by ring
  have hexp : Real.exp (-cSave * Real.log X / (θ + 1) ^ 2) ≤
      1 / (Real.log X) ^ 4 := by
    calc
      _ ≤ Real.exp (-4 * Real.log (Real.log X)) :=
        Real.exp_le_exp.mpr hdecay
      _ = 1 / (Real.log X) ^ 4 := by
        have hexpFour : Real.exp (4 * Real.log (Real.log X)) =
            (Real.log X) ^ 4 := by
          calc
            _ = (Real.exp (Real.log (Real.log X))) ^ 4 := by
              simpa using Real.exp_nat_mul (Real.log (Real.log X)) 4
            _ = _ := by rw [Real.exp_log hlog]
        rw [show -4 * Real.log (Real.log X) =
          -(4 * Real.log (Real.log X)) by ring, Real.exp_neg, hexpFour]
        simp only [one_div]
  have hmulC := mul_le_mul_of_nonneg_left hexp hC.le
  simpa [θ, T, div_eq_mul_inv] using hraw.trans hmulC

/-- Every uniform exceptional estimate supplies one positive moving-cutoff
constant and one positive absolute majorant with fourth-power logarithmic
decay for the shifted exceptional count used by the finite odd-class split. -/
theorem uniformExceptionalEstimate_eventually_E_oddClassCutoff_add_one_le
    {cSave : ℝ} (hUniform : UniformExceptionalEstimate cSave) :
    ∃ kappa C : ℝ, 0 < kappa ∧ 0 < C ∧
      ∀ᶠ X : ℝ in atTop,
        E (classAverageCutoff kappa X + 1) X ≤
          C * X / (Real.log X) ^ 4 := by
  obtain ⟨cExc, C, hcExc, hC, hbound⟩ :=
    uniformExceptionalEstimate_normalized hUniform
  obtain ⟨kappa, hkappa, hkExc, hkSave⟩ :=
    exists_oddClassCutoffConstant hUniform.1 hcExc
  refine ⟨kappa, C, hkappa, hC, ?_⟩
  filter_upwards [hbound,
    eventually_ge_atTop (Real.exp (Real.exp 1)),
    eventually_le_classAverageCutoff (r₀ := 2) hkappa] with X hboundX hX hT
  have hXpos : 0 < X :=
    (Real.exp_pos (Real.exp 1)).trans_le hX
  have hratio := exceptional_ratio_at_oddClassCutoff_le_log_pow
    hC hkappa hkExc hkSave hX hT hboundX
  have hcleared := (div_le_iff₀ hXpos).mp hratio
  calc
    E (classAverageCutoff kappa X + 1) X ≤
        (C / Real.log X ^ 4) * X := hcleared
    _ = C * X / Real.log X ^ 4 := by ring

end

end PellPaper
