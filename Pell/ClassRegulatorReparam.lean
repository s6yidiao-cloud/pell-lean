import Pell.ClassUniformDecayBridge

/-!
# Reparameterizing the class-side regulator cutoff

The field-theoretic comparison between a regulator cutoff `t` and a Pell
fundamental solution has a fixed loss.  This file records that comparison as
an explicit hypothesis and makes its effect on the uniform Pell estimate
quantitative.  In particular, it does *not* assert a unit comparison for
quadratic fields.

The parameter used on the Pell side is
`Θ(t) = 6 max(1 / 2, t)`.  The harmless maximum ensures that it is in the
range `Θ(t) ≥ 3` required by the uniform Pell estimate.
-/

namespace PellPaper

open Filter

noncomputable section

/-- The Pell exponent associated to a regulator cutoff `t`.  This is the
normalization `Θ(t) = 6 max(1/2,t)` used in the class-side reduction. -/
def regulatorPellExponent (t : ℝ) : ℝ := 6 * max (1 / 2) t

/-- The reparameterized exponent is always in the admissible degree range. -/
theorem three_le_regulatorPellExponent (t : ℝ) : 3 ≤ regulatorPellExponent t := by
  unfold regulatorPellExponent
  have hhalf : (1 / 2 : ℝ) ≤ max (1 / 2) t := le_max_left _ _
  nlinarith

/-- For a nonnegative regulator cutoff, the reparameterized denominator is
at most six times the natural regulator denominator. -/
theorem regulatorPellExponent_add_one_le_six_mul {t : ℝ} (ht : 0 ≤ t) :
    regulatorPellExponent t + 1 ≤ 6 * (t + 1) := by
  unfold regulatorPellExponent
  have hmax : max (1 / 2 : ℝ) t ≤ t + 1 / 2 := by
    exact max_le (by linarith) (by linarith)
  nlinarith

/-- The square comparison behind the loss of a factor `36` in the saving. -/
theorem regulatorPellExponent_denominator_sq_le {t : ℝ} (ht : 0 ≤ t) :
    (regulatorPellExponent t + 1) ^ 2 ≤ 36 * (t + 1) ^ 2 := by
  have hpos : 0 ≤ regulatorPellExponent t + 1 := by
    have hthree := three_le_regulatorPellExponent t
    linarith
  have hupper := regulatorPellExponent_add_one_le_six_mul ht
  have hright : 0 ≤ 6 * (t + 1) := by positivity
  nlinarith

/-- Replacing the Pell-side denominator by the regulator-side denominator
costs at most a factor `36` in a nonnegative saving. -/
theorem regulatorPellExponent_saving_ge {t c : ℝ} (ht : 0 ≤ t) (hc : 0 ≤ c) :
    c / (36 * (t + 1) ^ 2) ≤ c / (regulatorPellExponent t + 1) ^ 2 := by
  have hthetaPos : 0 < regulatorPellExponent t + 1 := by
    have hthree := three_le_regulatorPellExponent t
    linarith
  have hthetaSqPos : 0 < (regulatorPellExponent t + 1) ^ 2 := sq_pos_of_pos hthetaPos
  have hsq := regulatorPellExponent_denominator_sq_le ht
  exact div_le_div_of_nonneg_left hc hthetaSqPos hsq

/-- The associated exponential decay has saving `c / 36` in the natural
regulator denominator. -/
theorem regulatorPellExponent_decay_exponent_le {t c X : ℝ}
    (ht : 0 ≤ t) (hc : 0 ≤ c) (hX : 1 ≤ X) :
    -c * Real.log X / (regulatorPellExponent t + 1) ^ 2 ≤
      -c * Real.log X / (36 * (t + 1) ^ 2) := by
  have hlog : 0 ≤ Real.log X := Real.log_nonneg hX
  have hsaving := regulatorPellExponent_saving_ge ht hc
  have hmul := mul_le_mul_of_nonneg_right hsaving hlog
  calc
    -c * Real.log X / (regulatorPellExponent t + 1) ^ 2 =
        -(c / (regulatorPellExponent t + 1) ^ 2 * Real.log X) := by ring
    _ ≤ -(c / (36 * (t + 1) ^ 2) * Real.log X) := neg_le_neg hmul
    _ = -c * Real.log X / (36 * (t + 1) ^ 2) := by ring

/-- The same comparison, with the loss displayed as the saving `c / 36`. -/
theorem regulatorPellExponent_decay_exponent_le_div_36 {t c X : ℝ}
    (ht : 0 ≤ t) (hc : 0 ≤ c) (hX : 1 ≤ X) :
    -c * Real.log X / (regulatorPellExponent t + 1) ^ 2 ≤
      -(c / 36) * Real.log X / (t + 1) ^ 2 := by
  calc
    -c * Real.log X / (regulatorPellExponent t + 1) ^ 2 ≤
        -c * Real.log X / (36 * (t + 1) ^ 2) :=
      regulatorPellExponent_decay_exponent_le ht hc hX
    _ = -(c / 36) * Real.log X / (t + 1) ^ 2 := by
      have hbase : 0 < t + 1 := by linarith
      have hne : (t + 1) ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos hbase)
      field_simp

/-- If all members of the ambient finite family already satisfy the
discriminant cutoff, the class-side exceptional set is simply the regulator
filter. -/
theorem classRegulatorExceptionalSet_eq_regulatorFilter_of_cutoff
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (D : ι → ℕ) (r : ι → ℝ) (X : ℝ) (t : ℝ)
    (hcutoff : ∀ i, i ∈ s → D i ≤ ⌊X⌋₊) :
    classRegulatorExceptionalSet s D r ⌊X⌋₊ t =
      s.filter (fun i ↦ r i < t) := by
  classical
  ext i
  constructor
  · intro hi
    obtain ⟨his, -, hir⟩ := mem_classRegulatorExceptionalSet.mp hi
    exact Finset.mem_filter.mpr ⟨his, hir⟩
  · intro hi
    obtain ⟨his, hir⟩ := Finset.mem_filter.mp hi
    exact mem_classRegulatorExceptionalSet.mpr ⟨his, hcutoff i his, hir⟩

/-- A uniform Pell exceptional-set estimate transfers to regulator-small
families after the explicit reparameterization `Θ(t) = 6 max(1/2,t)`.

The hypothesis `htransfer` is intentionally the only field/unit input.  It
says that regulator height below `t` yields a Pell fundamental solution at
exponent `Θ(t)`; no such comparison is proved here.  The resulting decay has
the promised saving `cSave / 36` in the natural denominator `(t + 1)^2`. -/
theorem uniformExceptionalEstimate_regulatorSmall_reparam_decay
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (D : ι → ℕ) (r : ι → ℝ) (cSave : ℝ)
    (hDinj : Set.InjOn D (↑s : Set ι))
    (htransfer : ∀ t i, i ∈ s → r i < t →
      SmallFundamentalSolution (regulatorPellExponent t) (D i))
    (hUniform : UniformExceptionalEstimate cSave) :
    ∃ cExc C : ℝ, 0 < cExc ∧ 0 < C ∧
      ∀ᶠ X : ℝ in atTop, ∀ t : ℝ, 0 ≤ t →
        UniformAdmissible cExc (regulatorPellExponent t) X →
          ((classRegulatorExceptionalSet s D r ⌊X⌋₊ t).card : ℝ) ≤
            C * X * Real.exp
              (-(cSave / 36) * Real.log X / (t + 1) ^ 2) := by
  obtain ⟨hcSave, cExc, C, hcExc, hC, hbound⟩ := hUniform
  refine ⟨cExc, C, hcExc, hC, ?_⟩
  filter_upwards [hbound, eventually_ge_atTop (1 : ℝ)] with X hX hXone
  intro t ht hadmissible
  let θ := regulatorPellExponent t
  have hθ : 3 ≤ θ := three_le_regulatorPellExponent t
  have hratio : E θ X / X ≤
      C * Real.exp (-cSave * Real.log X / (θ + 1) ^ 2) := by
    exact exceptional_ratio_le_exp hθ hcSave.le hC.le hXone
      (hX θ hθ hadmissible)
  have hcard :
      ((classRegulatorExceptionalSet s D r ⌊X⌋₊ t).card : ℝ) ≤ E θ X := by
    apply classRegulatorExceptional_card_le_E s D r θ t X hDinj
    intro i hi _ hir
    exact htransfer t i hi hir
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hXone
  have hE : E θ X ≤
      C * X * Real.exp (-cSave * Real.log X / (θ + 1) ^ 2) := by
    have h := (div_le_iff₀ hXpos).mp hratio
    calc
      E θ X ≤ (C * Real.exp (-cSave * Real.log X / (θ + 1) ^ 2)) * X := h
      _ = C * X * Real.exp (-cSave * Real.log X / (θ + 1) ^ 2) := by ring
  have hexp := regulatorPellExponent_decay_exponent_le_div_36 ht hcSave.le hXone
  have hXnonneg : 0 ≤ X := le_trans (by norm_num) hXone
  have hCXnonneg : 0 ≤ C * X := mul_nonneg hC.le hXnonneg
  calc
    ((classRegulatorExceptionalSet s D r ⌊X⌋₊ t).card : ℝ) ≤ E θ X := hcard
    _ ≤ C * X * Real.exp (-cSave * Real.log X / (θ + 1) ^ 2) := hE
    _ ≤ C * X * Real.exp (-(cSave / 36) * Real.log X / (t + 1) ^ 2) := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hCXnonneg

end

end PellPaper
