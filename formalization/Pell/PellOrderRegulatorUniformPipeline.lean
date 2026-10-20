import Pell.ClassUniformDynamic
import Pell.ExceptionalMonotonicity
import Pell.FundamentalDiscriminantPellRegulator

/-!
# Uniform Pell decay for the concrete Pell-order regulator

The generic class-side pipeline accepts an abstract regulator parameter and an
abstract implication from a regulator cutoff to a small Pell solution.  For
the concrete regulator `pellOrderRegulator`, both the parameter and that
implication are already defined and proved from the unique fundamental Pell
solution.  This module specializes the moving-family uniform exceptional-set
transfer to that data.

It does not compare this Pell-order regulator with the fundamental unit of the
maximal order, and therefore does not prove the field class-number theorem.
-/

namespace PellPaper

open Filter Set
open scoped BigOperators

noncomputable section

/-- The reparameterized exponent always dominates its original cutoff. -/
theorem le_regulatorPellExponent (t : ℝ) : t ≤ regulatorPellExponent t := by
  unfold regulatorPellExponent
  by_cases ht : t ≤ (1 / 2 : ℝ)
  · rw [max_eq_left ht]
    nlinarith
  · have ht' : (1 / 2 : ℝ) ≤ t := le_of_not_ge ht
    rw [max_eq_right ht']
    nlinarith

/-- A cutoff on the concrete Pell-order regulator gives the reparameterized
small-fundamental-solution condition consumed by the uniform class pipeline. -/
theorem smallFundamentalSolution_regulatorPellExponent_of_pellOrderRegulator_lt
    {D : ℕ} (hD : PositiveFundamentalDiscriminant D) (t : ℝ)
    (hreg : pellOrderRegulator D < t) :
    SmallFundamentalSolution (regulatorPellExponent t) D := by
  apply smallFundamentalSolution_mono (le_regulatorPellExponent t)
  exact smallFundamentalSolution_of_pellOrderRegulator_lt hD t hreg

/-- The moving-family uniform exceptional estimate specialized to the actual
Pell-order regulator.  Unlike the generic theorem, this has no abstract
regulator-to-Pell transfer hypothesis. -/
theorem uniformExceptionalEstimate_pellOrderRegulator_reparam_rate
    (cSave : ℝ) (hUniform : UniformExceptionalEstimate cSave) :
    ∃ cExc C : ℝ, 0 < cExc ∧ 0 < C ∧
      ∀ᶠ X : ℝ in atTop, ∀ t : ℝ, 0 ≤ t →
        UniformAdmissible cExc (regulatorPellExponent t) X →
          (((fundamentalDiscriminantsBelow X).filter
            (fun D ↦ pellOrderRegulator D < t)).card : ℝ) ≤
            C * X * Real.exp
              (-(cSave / 36) * Real.log X / (t + 1) ^ 2) := by
  apply uniformExceptionalEstimate_fundamentalDiscriminantsBelow_reparam_rate
    pellOrderRegulator cSave ?_ hUniform
  intro X t D hDX hreg
  exact smallFundamentalSolution_regulatorPellExponent_of_pellOrderRegulator_lt
    (mem_fundamentalDiscriminantsBelow.mp hDX).1 t hreg

/-- A direct class-side exceptional-set bound for the concrete Pell-order
regulator.  Clipping the regulator threshold at `max 3 t` is enough to enter
the range of `UniformExceptionalEstimate`; no maximal-order unit comparison
is used.  The elementary clipping costs a factor `16` in the exponential
saving. -/
theorem uniformExceptionalEstimate_pellOrderRegulator_clipped_decay
    (cSave : ℝ) (hUniform : UniformExceptionalEstimate cSave) :
    ∃ cExc C : ℝ, 0 < cExc ∧ 0 < C ∧
      ∀ᶠ X : ℝ in atTop, ∀ t : ℝ, 0 ≤ t →
        UniformAdmissible cExc (max 3 t) X →
          (((fundamentalDiscriminantsBelow X).filter
            (fun D ↦ pellOrderRegulator D < t)).card : ℝ) ≤
              C * X * Real.exp
                (-(cSave / 16) * Real.log X / (t + 1) ^ 2) := by
  obtain ⟨hcSave, cExc, C, hcExc, hC, hbound⟩ := hUniform
  refine ⟨cExc, C, hcExc, hC, ?_⟩
  filter_upwards [hbound, eventually_ge_atTop (1 : ℝ)] with X hboundX hX
  intro t ht hadmissible
  let θ : ℝ := max 3 t
  have hθ : 3 ≤ θ := by
    dsimp [θ]
    exact le_max_left _ _
  have hsubset :
      (fundamentalDiscriminantsBelow X).filter (fun D ↦ pellOrderRegulator D < t) ⊆
        (fundamentalDiscriminantsBelow X).filter (fun D ↦ pellOrderRegulator D < θ) := by
    intro D hD
    obtain ⟨hDX, hreg⟩ := Finset.mem_filter.mp hD
    exact Finset.mem_filter.mpr ⟨hDX, hreg.trans_le (by
      dsimp [θ]
      exact le_max_right _ _)⟩
  have hfilter :
      (((fundamentalDiscriminantsBelow X).filter
        (fun D ↦ pellOrderRegulator D < t)).card : ℝ) ≤ E θ X := by
    calc
      (((fundamentalDiscriminantsBelow X).filter
        (fun D ↦ pellOrderRegulator D < t)).card : ℝ) ≤
          (((fundamentalDiscriminantsBelow X).filter
            (fun D ↦ pellOrderRegulator D < θ)).card : ℝ) := by
              exact_mod_cast Finset.card_le_card hsubset
      _ ≤ E θ X :=
        fundamentalDiscriminantsBelow_pellOrderRegulatorFilter_card_le_E
          (le_trans zero_le_one hX)
  have hratio : E θ X / X ≤
      C * Real.exp (-cSave * Real.log X / (θ + 1) ^ 2) :=
    exceptional_ratio_le_exp hθ hcSave.le hC.le hX
      (hboundX θ hθ (by simpa [θ] using hadmissible))
  have hθadd : θ + 1 ≤ 4 * (t + 1) := by
    have hmax : max (3 : ℝ) t ≤ t + 3 := by
      exact max_le (by linarith) (by linarith)
    dsimp [θ]
    nlinarith
  have hθpos : 0 < θ + 1 := by linarith
  have hsq : (θ + 1) ^ 2 ≤ 16 * (t + 1) ^ 2 := by nlinarith
  have hsaving : (cSave / 16) / (t + 1) ^ 2 ≤
      cSave / (θ + 1) ^ 2 := by
    calc
      (cSave / 16) / (t + 1) ^ 2 =
          cSave / (16 * (t + 1) ^ 2) := by
            field_simp
      _ ≤ cSave / (θ + 1) ^ 2 :=
        div_le_div_of_nonneg_left hcSave.le (sq_pos_of_pos hθpos) hsq
  have hlog : 0 ≤ Real.log X := Real.log_nonneg hX
  have hexponent :
      -cSave * Real.log X / (θ + 1) ^ 2 ≤
        -(cSave / 16) * Real.log X / (t + 1) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hsaving hlog
    calc
      -cSave * Real.log X / (θ + 1) ^ 2 =
          -(cSave / (θ + 1) ^ 2 * Real.log X) := by ring
      _ ≤ -((cSave / 16) / (t + 1) ^ 2 * Real.log X) := neg_le_neg hmul
      _ = -(cSave / 16) * Real.log X / (t + 1) ^ 2 := by ring
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hE : E θ X ≤ C * X * Real.exp (-cSave * Real.log X / (θ + 1) ^ 2) := by
    have h := (div_le_iff₀ hXpos).mp hratio
    calc
      E θ X ≤ (C * Real.exp (-cSave * Real.log X / (θ + 1) ^ 2)) * X := h
      _ = C * X * Real.exp (-cSave * Real.log X / (θ + 1) ^ 2) := by ring
  calc
    (((fundamentalDiscriminantsBelow X).filter
      (fun D ↦ pellOrderRegulator D < t)).card : ℝ) ≤ E θ X := hfilter
    _ ≤ C * X * Real.exp (-cSave * Real.log X / (θ + 1) ^ 2) := hE
    _ ≤ C * X * Real.exp (-(cSave / 16) * Real.log X / (t + 1) ^ 2) := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent)
        (mul_nonneg hC.le (le_trans zero_le_one hX))

/-- The concrete Pell-order regulator has the manuscript's elementary lower
bound `1/2`, because the fundamental Pell unit is strictly larger than
`sqrt D`. -/
theorem one_half_lt_pellOrderRegulator {D : ℕ}
    (hD : PositiveFundamentalDiscriminant D) :
    (1 / 2 : ℝ) < pellOrderRegulator D := by
  rw [pellOrderRegulator_eq_pellNormalizedLog hD]
  unfold pellNormalizedLog
  have hDreal : 1 < (D : ℝ) := by exact_mod_cast hD.1
  have hDnonneg : 0 ≤ (D : ℝ) := by linarith
  have hsqrt : 0 < Real.sqrt (D : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hepslt := sqrt_lt_epsilon (fundamentalPellSolution_isFundamental D hD)
  have hloglt : Real.log (Real.sqrt (D : ℝ)) <
      Real.log (epsilon (fundamentalPellSolution D hD)) :=
    Real.log_lt_log hsqrt hepslt
  rw [Real.log_sqrt hDnonneg] at hloglt
  apply (lt_div_iff₀ (Real.log_pos hDreal)).mpr
  nlinarith

/-- The moving-family Cauchy--Schwarz handoff specialized to the concrete
Pell-order regulator.  Relative to the generic class pipeline, both the
regulator lower bound (above any `r₀ ≤ 1/2`) and the regulator-to-Pell
transfer are now proved, rather than supplied as arithmetic hypotheses.

The class-number-formula comparison and the two `L`-value moments remain
external inputs, as does the comparison of this Pell-order regulator with the
maximal-order regulator needed for the manuscript's field theorem. -/
theorem eventually_formClassSum_bound_of_uniformExceptional_pellOrderRegulator
    (M : ClassNumberModel) (L : ℕ → ℝ)
    (B₀ Cmoment r₀ c cSave : ℝ)
    (hB₀ : 0 ≤ B₀) (hCmoment : 0 ≤ Cmoment)
    (hr₀ : 0 < r₀) (hr₀half : r₀ ≤ 1 / 2) (hc : 0 < c)
    (hL : ∀ D, PositiveFundamentalDiscriminant D → 0 ≤ L D)
    (hUniform : UniformExceptionalEstimate cSave)
    (hpoint : ∀ X D, D ∈ fundamentalDiscriminantsBelow X →
      (M.formClassNumber D : ℝ) ≤
        (Real.sqrt X / Real.log X) * (L D / pellOrderRegulator D))
    (hfirst : ∀ᶠ X : ℝ in atTop,
      (∑ D ∈ fundamentalDiscriminantsBelow X, L D) ≤ B₀ * X)
    (hsecond : ∀ᶠ X : ℝ in atTop,
      (∑ D ∈ fundamentalDiscriminantsBelow X, (L D) ^ 2) ≤ Cmoment * X)
    (hcutoff : ∀ᶠ X : ℝ in atTop, r₀ ≤ classAverageCutoff c X)
    (hadmissible : ∀ cExc : ℝ, 0 < cExc →
      ∀ᶠ X : ℝ in atTop, ∀ t ∈ Icc r₀ (classAverageCutoff c X),
        UniformAdmissible cExc (regulatorPellExponent t) X) :
    ∃ cExc C : ℝ, 0 < cExc ∧ 0 < C ∧
      ∀ᶠ X : ℝ in atTop,
        M.formClassSum X ≤
          (B₀ / c + Real.sqrt (C * Cmoment) *
            (((1 + 1 / r₀) ^ 2 + 1) /
              Real.sqrt ((cSave / 36) / 2))) * classAverageScale X := by
  exact eventually_formClassSum_bound_of_uniformExceptional_dynamic
    M L pellOrderRegulator B₀ Cmoment r₀ c cSave
    hB₀ hCmoment hr₀ hc hL
    (fun D hD ↦ hr₀half.trans (one_half_lt_pellOrderRegulator hD).le)
    (fun X t D hDX hreg ↦
      smallFundamentalSolution_regulatorPellExponent_of_pellOrderRegulator_lt
        (mem_fundamentalDiscriminantsBelow.mp hDX).1 t hreg)
    hUniform hpoint hfirst hsecond hcutoff hadmissible

end

end PellPaper
