import Pell.FundamentalDiscriminantCutoff
import Pell.ClassAverageCauchyPipeline

/-!
# A moving-family class-side use of the uniform Pell estimate

The finite family of positive fundamental discriminants below `X` changes
with `X`.  Consequently, an eventual statement proved for one fixed finite
family cannot simply be specialized with
`s = fundamentalDiscriminantsBelow X`.  This file instead first proves a
*pointwise* transfer at a fixed cutoff `X`, and only then places that
pointwise statement under the uniform eventual quantifier supplied by
`UniformExceptionalEstimate`.

All quadratic-field, unit-comparison, moment, and cutoff-admissibility input
is left explicit.  In particular, the last theorem is an eventual
Cauchy--Schwarz reduction, not a proof of the class-number theorem.
-/

namespace PellPaper

open Filter Set
open scoped BigOperators

noncomputable section

/-- At a fixed real cutoff, an explicit pointwise Pell exceptional-count
bound controls the literal regulator filter on the *varying* family of
positive fundamental discriminants below that same cutoff.  The
discriminant cutoff in `classRegulatorExceptionalSet` is automatic here. -/
theorem fundamentalDiscriminantsBelow_filtered_cardinality_reparam_pointwise
    (r : ℕ → ℝ) (t cSave C X : ℝ)
    (hX : 0 ≤ X)
    (htransfer : ∀ D, D ∈ fundamentalDiscriminantsBelow X → r D < t →
      SmallFundamentalSolution (regulatorPellExponent t) D)
    (hbound : E (regulatorPellExponent t) X ≤
      C * X ^ (1 - cSave /
        (uniformQ (regulatorPellExponent t) : ℝ) ^ 2)) :
    (((fundamentalDiscriminantsBelow X).filter (fun D ↦ r D < t)).card : ℝ) ≤
      C * X ^ (1 - cSave /
        (uniformQ (regulatorPellExponent t) : ℝ) ^ 2) := by
  rw [← classRegulatorExceptionalSet_fundamentalDiscriminantsBelow_eq_regulatorFilter
    X t r hX]
  calc
    ((classRegulatorExceptionalSet (fundamentalDiscriminantsBelow X) id r
        ⌊X⌋₊ t).card : ℝ) ≤ E (regulatorPellExponent t) X := by
      apply classRegulatorExceptional_card_le_E
        (fundamentalDiscriminantsBelow X) id r (regulatorPellExponent t) t X
      · intro D hD E hE hDE
        exact hDE
      · intro D hD _ hrD
        exact htransfer D hD hrD
    _ ≤ C * X ^ (1 - cSave /
        (uniformQ (regulatorPellExponent t) : ℝ) ^ 2) := hbound

/-- The pointwise moving-family transfer in the exponential form used by the
Cauchy--Schwarz pipeline.  The factor `36` is exactly the elementary loss of
the regulator-to-Pell reparameterization. -/
theorem fundamentalDiscriminantsBelow_filtered_cardinality_reparam_decay_pointwise
    (r : ℕ → ℝ) (t cSave C X : ℝ)
    (hX : 1 ≤ X) (ht : 0 ≤ t) (hcSave : 0 ≤ cSave) (hC : 0 ≤ C)
    (htransfer : ∀ D, D ∈ fundamentalDiscriminantsBelow X → r D < t →
      SmallFundamentalSolution (regulatorPellExponent t) D)
    (hbound : E (regulatorPellExponent t) X ≤
      C * X ^ (1 - cSave /
        (uniformQ (regulatorPellExponent t) : ℝ) ^ 2)) :
    (((fundamentalDiscriminantsBelow X).filter (fun D ↦ r D < t)).card : ℝ) ≤
      C * X * Real.exp
        (-(cSave / 36) * Real.log X / (t + 1) ^ 2) := by
  rw [← classRegulatorExceptionalSet_fundamentalDiscriminantsBelow_eq_regulatorFilter
    X t r (le_trans zero_le_one hX)]
  have hcard :
      ((classRegulatorExceptionalSet (fundamentalDiscriminantsBelow X) id r
        ⌊X⌋₊ t).card : ℝ) ≤
        C * X * Real.exp
          (-cSave * Real.log X /
            (regulatorPellExponent t + 1) ^ 2) := by
    let θ := regulatorPellExponent t
    have hθ : 3 ≤ θ := three_le_regulatorPellExponent t
    have hratio : E θ X / X ≤
        C * Real.exp (-cSave * Real.log X / (θ + 1) ^ 2) :=
      exceptional_ratio_le_exp hθ hcSave hC hX hbound
    have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
    have hE : E θ X ≤
        C * X * Real.exp (-cSave * Real.log X / (θ + 1) ^ 2) := by
      have h := (div_le_iff₀ hXpos).mp hratio
      calc
        E θ X ≤ (C * Real.exp (-cSave * Real.log X / (θ + 1) ^ 2)) * X := h
        _ = C * X * Real.exp (-cSave * Real.log X / (θ + 1) ^ 2) := by ring
    calc
      ((classRegulatorExceptionalSet (fundamentalDiscriminantsBelow X) id r
          ⌊X⌋₊ t).card : ℝ) ≤ E θ X := by
        apply classRegulatorExceptional_card_le_E
          (fundamentalDiscriminantsBelow X) id r θ t X
        · intro D hD E hE hDE
          exact hDE
        · intro D hD _ hrD
          exact htransfer D hD hrD
      _ ≤ C * X * Real.exp (-cSave * Real.log X / (θ + 1) ^ 2) := hE
  have hexp := regulatorPellExponent_decay_exponent_le_div_36 ht hcSave hX
  have hCX : 0 ≤ C * X := mul_nonneg hC (le_trans zero_le_one hX)
  exact hcard.trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr hexp) hCX)

/-- `UniformExceptionalEstimate` can be used on the changing family
`fundamentalDiscriminantsBelow X` because the injection and cutoff checks are
performed anew at each `X`.  This is deliberately different from applying an
eventual theorem with a fixed finite set as a parameter. -/
theorem uniformExceptionalEstimate_fundamentalDiscriminantsBelow_reparam_rate
    (r : ℕ → ℝ) (cSave : ℝ)
    (htransfer : ∀ X t D, D ∈ fundamentalDiscriminantsBelow X → r D < t →
      SmallFundamentalSolution (regulatorPellExponent t) D)
    (hUniform : UniformExceptionalEstimate cSave) :
    ∃ cExc C : ℝ, 0 < cExc ∧ 0 < C ∧
      ∀ᶠ X : ℝ in atTop, ∀ t : ℝ, 0 ≤ t →
        UniformAdmissible cExc (regulatorPellExponent t) X →
          (((fundamentalDiscriminantsBelow X).filter (fun D ↦ r D < t)).card : ℝ) ≤
            C * X * Real.exp
              (-(cSave / 36) * Real.log X / (t + 1) ^ 2) := by
  obtain ⟨hcSave, cExc, C, hcExc, hC, hUniformBound⟩ := hUniform
  refine ⟨cExc, C, hcExc, hC, ?_⟩
  filter_upwards [hUniformBound, eventually_ge_atTop (1 : ℝ)] with X hbound hX
  intro t ht hadmissible
  exact fundamentalDiscriminantsBelow_filtered_cardinality_reparam_decay_pointwise
    r t cSave C X hX ht hcSave.le hC.le
    (fun D hD hrD ↦ htransfer X t D hD hrD)
    (hbound (regulatorPellExponent t) (three_le_regulatorPellExponent t)
      hadmissible)

/-- A fully explicit moving-family Cauchy--Schwarz handoff from the uniform
Pell estimate.  The regulator-to-Pell comparison, class-number-formula type
pointwise bound, two moment bounds, regulator lower bound, cutoff condition,
and uniform admissibility condition remain hypotheses.  The conclusion is
only eventual; a finite initial range is a separate input needed for the
all-`X` theorem in `main.tex`. -/
theorem eventually_formClassSum_bound_of_uniformExceptional_dynamic
    (M : ClassNumberModel) (L r : ℕ → ℝ)
    (B₀ Cmoment r₀ c cSave : ℝ)
    (hB₀ : 0 ≤ B₀) (hCmoment : 0 ≤ Cmoment)
    (hr₀ : 0 < r₀) (hc : 0 < c)
    (hL : ∀ D, PositiveFundamentalDiscriminant D → 0 ≤ L D)
    (hr : ∀ D, PositiveFundamentalDiscriminant D → r₀ ≤ r D)
    (htransfer : ∀ X t D, D ∈ fundamentalDiscriminantsBelow X → r D < t →
      SmallFundamentalSolution (regulatorPellExponent t) D)
    (hUniform : UniformExceptionalEstimate cSave)
    (hpoint : ∀ X D, D ∈ fundamentalDiscriminantsBelow X →
      (M.formClassNumber D : ℝ) ≤
        (Real.sqrt X / Real.log X) * (L D / r D))
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
  obtain ⟨cExc, C, hcExc, hC, hcard⟩ :=
    uniformExceptionalEstimate_fundamentalDiscriminantsBelow_reparam_rate
      r cSave htransfer hUniform
  refine ⟨cExc, C, hcExc, hC, ?_⟩
  filter_upwards [hcard, hfirst, hsecond, hcutoff, hadmissible cExc hcExc,
    eventually_ge_atTop (Real.exp (Real.exp 1))] with
      X hcardX hfirstX hsecondX hcutoffX hadmissibleX hlargeX
  have hsave : 0 < cSave / 36 := by
    obtain ⟨hcSave, -⟩ := hUniform
    positivity
  have hcardAt : ∀ t ∈ Icc r₀ (classAverageCutoff c X),
      (((fundamentalDiscriminantsBelow X).filter (fun D ↦ r D < t)).card : ℝ) ≤
        C * X * Real.exp
          (-(cSave / 36) * Real.log X / (t + 1) ^ 2) := by
    intro t ht
    exact hcardX t (hr₀.le.trans ht.1) (hadmissibleX t ht)
  have hfinite := finite_sum_class_bound_of_exponential_cardinality_rate
    (fundamentalDiscriminantsBelow X)
    (fun D ↦ (M.formClassNumber D : ℝ)) L r
    B₀ C Cmoment r₀ (cSave / 36) c X
    hB₀ hC.le hCmoment
    (fun D hD ↦ hL D (mem_fundamentalDiscriminantsBelow.mp hD).1)
    (fun D hD ↦ hr D (mem_fundamentalDiscriminantsBelow.mp hD).1)
    hr₀ hc hsave hlargeX hcutoffX
    (fun D hD ↦ hpoint X D hD)
    hfirstX hsecondX hcardAt
  simpa [ClassNumberModel.formClassSum] using hfinite

end

end PellPaper
