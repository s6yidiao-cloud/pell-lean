import Pell.ClassAverageCauchyPipeline

/-!
# A conditional route to the exact class-average target

This file is deliberately an interface, not a proof of the class-number
theorem in `main.tex`.  It packages precisely the inputs consumed by the
already proved finite Cauchy--Schwarz pipeline, specialized to the
fundamental-discriminant family of a `ClassNumberModel`.

In an arithmetic instantiation, `L` is expected to be a Dirichlet `L`-value
and `r` a normalized regulator parameter.  The class-number-formula
comparison, the first and second `L`-moments, the regulator cutoff condition,
and the exceptional-cardinality estimate are all hypotheses below.  The
finite small-range bound is included so that the conclusion has the exact
all-`X ≥ 3` quantifier of `FieldClassAverageAssertion`.
-/

namespace PellPaper

open Set
open scoped BigOperators

noncomputable section

/-- The explicit arithmetic and analytic inputs which the finite
Cauchy--Schwarz class-average pipeline needs in order to prove the exact
all-cutoff target.  No field, unit, class-number formula, or `L`-function
moment theorem is asserted by this structure. -/
structure ClassAverageCauchyInputs (M : ClassNumberModel) where
  /-- The weight which, in the intended application, is `L(1, χ_D)`. -/
  L : ℕ → ℝ
  /-- The regulator parameter used to split the family. -/
  r : ℕ → ℝ
  B₀ : ℝ
  Ccard : ℝ
  Cmoment : ℝ
  r₀ : ℝ
  a : ℝ
  c : ℝ
  Bsmall : ℝ
  B₀_nonneg : 0 ≤ B₀
  Ccard_nonneg : 0 ≤ Ccard
  Cmoment_nonneg : 0 ≤ Cmoment
  r₀_pos : 0 < r₀
  a_pos : 0 < a
  c_pos : 0 < c
  Bsmall_nonneg : 0 ≤ Bsmall
  L_nonneg : ∀ D, PositiveFundamentalDiscriminant D → 0 ≤ L D
  regulator_lower : ∀ D, PositiveFundamentalDiscriminant D → r₀ ≤ r D
  /-- The chosen regulator cutoff lies above the fixed lower endpoint in the
  large range where the finite pipeline is applied. -/
  cutoff_lower : ∀ X : ℝ, Real.exp (Real.exp 1) ≤ X →
    r₀ ≤ classAverageCutoff c X
  /-- The pointwise class-number-formula-type comparison. -/
  pointwise : ∀ X : ℝ, ∀ D ∈ fundamentalDiscriminantsBelow X,
    (M.formClassNumber D : ℝ) ≤
      (Real.sqrt X / Real.log X) * (L D / r D)
  /-- The ambient first moment. -/
  first_moment : ∀ X : ℝ, Real.exp (Real.exp 1) ≤ X →
    (∑ D ∈ fundamentalDiscriminantsBelow X, L D) ≤ B₀ * X
  /-- The ambient second moment. -/
  second_moment : ∀ X : ℝ, Real.exp (Real.exp 1) ≤ X →
    (∑ D ∈ fundamentalDiscriminantsBelow X, (L D) ^ 2) ≤ Cmoment * X
  /-- The Pell/regulator exceptional-cardinality input in exactly the form
  used by the Cauchy--Schwarz pipeline. -/
  exceptional_cardinality : ∀ X : ℝ, Real.exp (Real.exp 1) ≤ X →
    ∀ θ ∈ Icc r₀ (classAverageCutoff c X),
      (((fundamentalDiscriminantsBelow X).filter (fun D ↦ r D < θ)).card : ℝ) ≤
        Ccard * X * Real.exp (-a * Real.log X / (θ + 1) ^ 2)
  /-- A separate finite-range estimate, needed only to turn the eventual
  Cauchy conclusion into a statement for every `X ≥ 3`. -/
  small_range : ∀ X : ℝ, 3 ≤ X → X ≤ Real.exp (Real.exp 1) →
    M.formClassSum X ≤ Bsmall * classAverageScale X

/-- The finite Cauchy--Schwarz pipeline proves the exact form-class upper
bound, provided all of its field-specific and analytic premises are supplied
through `ClassAverageCauchyInputs`.  The extra `+ 1` merely combines the
large- and small-range constants into one positive constant. -/
theorem fieldClassAverageAssertion_of_cauchyInputs
    (M : ClassNumberModel) (H : ClassAverageCauchyInputs M) :
    FieldClassAverageAssertion M := by
  let K : ℝ := H.B₀ / H.c +
    Real.sqrt (H.Ccard * H.Cmoment) *
      (((1 + 1 / H.r₀) ^ 2 + 1) / Real.sqrt (H.a / 2))
  have hK : 0 ≤ K := by
    dsimp [K]
    apply add_nonneg
    · exact div_nonneg H.B₀_nonneg H.c_pos.le
    · apply mul_nonneg (Real.sqrt_nonneg _)
      exact div_nonneg (by positivity) (Real.sqrt_nonneg _)
  have hC : 0 < K + H.Bsmall + 1 := by
    linarith [H.Bsmall_nonneg]
  refine ⟨K + H.Bsmall + 1, hC, ?_⟩
  intro X hXthree
  constructor
  · exact M.ordinaryClassSum_le_formClassSum X
  · by_cases hlarge : Real.exp (Real.exp 1) ≤ X
    · have hfinite := finite_sum_class_bound_of_exponential_cardinality_rate
        (fundamentalDiscriminantsBelow X)
        (fun D ↦ (M.formClassNumber D : ℝ)) H.L H.r
        H.B₀ H.Ccard H.Cmoment H.r₀ H.a H.c X
        H.B₀_nonneg H.Ccard_nonneg H.Cmoment_nonneg
        (fun D hD ↦ H.L_nonneg D (mem_fundamentalDiscriminantsBelow.mp hD).1)
        (fun D hD ↦ H.regulator_lower D
          (mem_fundamentalDiscriminantsBelow.mp hD).1)
        H.r₀_pos H.c_pos H.a_pos hlarge
        (H.cutoff_lower X hlarge)
        (fun D hD ↦ H.pointwise X D hD)
        (H.first_moment X hlarge) (H.second_moment X hlarge)
        (fun θ hθ ↦ H.exceptional_cardinality X hlarge θ hθ)
      have hscale : 0 ≤ classAverageScale X :=
        classAverageScale_nonneg (by linarith)
      calc
        M.formClassSum X =
            ∑ D ∈ fundamentalDiscriminantsBelow X, (M.formClassNumber D : ℝ) := rfl
        _ ≤ K * classAverageScale X := by
          simpa [K] using hfinite
        _ ≤ (K + H.Bsmall + 1) * classAverageScale X := by
          apply mul_le_mul_of_nonneg_right _ hscale
          linarith [H.Bsmall_nonneg]
    · have hsmall : X ≤ Real.exp (Real.exp 1) := le_of_not_ge hlarge
      have hscale : 0 ≤ classAverageScale X :=
        classAverageScale_nonneg (by linarith)
      calc
        M.formClassSum X ≤ H.Bsmall * classAverageScale X :=
          H.small_range X hXthree hsmall
        _ ≤ (K + H.Bsmall + 1) * classAverageScale X := by
          apply mul_le_mul_of_nonneg_right _ hscale
          linarith [hK]

end

end PellPaper
