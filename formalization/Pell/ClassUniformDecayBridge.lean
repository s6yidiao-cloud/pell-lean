import Pell.ClassExceptionalInjection
import Pell.UniformExceptionalDecay

/-!
# From uniform Pell decay to class-side regulator decay

The class-average Cauchy--Schwarz pipeline consumes a bound for the finite
family whose regulator parameter is below a threshold. This file joins the
two already-verified elementary transfers: a discriminant-injective regulator
family maps into `E`, and the uniform Pell estimate gives exponential decay
after normalization by the cutoff.

The field/unit comparison remains an explicit hypothesis. Thus this is a
precise conditional handoff, not a proof of the quadratic-field arithmetic.
-/

namespace PellPaper

open Filter

noncomputable section

/-- A normalized Pell exceptional-count bound transfers directly to the
discriminant-injective regulator-small family. -/
theorem classRegulatorExceptional_card_le_of_E_ratio
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (D : ι → ℕ) (r : ι → ℝ)
    (θ a C X : ℝ)
    (hDinj : Set.InjOn D (↑s : Set ι))
    (htransfer : ∀ i, i ∈ s → D i ≤ ⌊X⌋₊ → r i < θ →
      SmallFundamentalSolution θ (D i))
    (hX : 1 ≤ X)
    (hratio : E θ X / X ≤
      C * Real.exp (-a * Real.log X / (θ + 1) ^ 2)) :
    ((classRegulatorExceptionalSet s D r ⌊X⌋₊ θ).card : ℝ) ≤
      C * X * Real.exp (-a * Real.log X / (θ + 1) ^ 2) := by
  have hcard := classRegulatorExceptional_card_le_E s D r θ θ X hDinj htransfer
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hE : E θ X ≤
      (C * Real.exp (-a * Real.log X / (θ + 1) ^ 2)) * X :=
    (div_le_iff₀ hXpos).mp hratio
  calc
    ((classRegulatorExceptionalSet s D r ⌊X⌋₊ θ).card : ℝ) ≤ E θ X := hcard
    _ ≤ (C * Real.exp (-a * Real.log X / (θ + 1) ^ 2)) * X := hE
    _ = C * X * Real.exp (-a * Real.log X / (θ + 1) ^ 2) := by ring

/-- The pointwise uniform exceptional-set estimate supplies the preceding
class-side exponential bound. -/
theorem classRegulatorExceptional_card_le_uniform_exp
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (D : ι → ℕ) (r : ι → ℝ)
    (θ cSave C X : ℝ)
    (hDinj : Set.InjOn D (↑s : Set ι))
    (htransfer : ∀ i, i ∈ s → D i ≤ ⌊X⌋₊ → r i < θ →
      SmallFundamentalSolution θ (D i))
    (hθ : 3 ≤ θ) (hcSave : 0 ≤ cSave) (hC : 0 ≤ C) (hX : 1 ≤ X)
    (hbound : E θ X ≤
      C * X ^ (1 - cSave / (uniformQ θ : ℝ) ^ 2)) :
    ((classRegulatorExceptionalSet s D r ⌊X⌋₊ θ).card : ℝ) ≤
      C * X * Real.exp (-cSave * Real.log X / (θ + 1) ^ 2) := by
  apply classRegulatorExceptional_card_le_of_E_ratio s D r θ cSave C X
    hDinj htransfer hX
  exact exceptional_ratio_le_exp hθ hcSave hC hX hbound

/-- A `UniformExceptionalEstimate` yields a common eventual exponential
cardinality estimate for every admissible regulator threshold in a fixed,
discriminant-injective finite family. The sole field-specific input is the
stated regulator-to-Pell transfer. -/
theorem uniformExceptionalEstimate_regulatorSmall_decay
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (D : ι → ℕ) (r : ι → ℝ) (cSave : ℝ)
    (hDinj : Set.InjOn D (↑s : Set ι))
    (htransfer : ∀ θ i, i ∈ s → r i < θ →
      SmallFundamentalSolution θ (D i))
    (hUniform : UniformExceptionalEstimate cSave) :
    ∃ cExc C : ℝ, 0 < cExc ∧ 0 < C ∧
      ∀ᶠ X : ℝ in atTop, ∀ θ : ℝ, 3 ≤ θ →
        UniformAdmissible cExc θ X →
          ((classRegulatorExceptionalSet s D r ⌊X⌋₊ θ).card : ℝ) ≤
            C * X * Real.exp (-cSave * Real.log X / (θ + 1) ^ 2) := by
  obtain ⟨cExc, C, hcExc, hC, hdecay⟩ :=
    uniformExceptionalEstimate_normalized hUniform
  refine ⟨cExc, C, hcExc, hC, ?_⟩
  filter_upwards [hdecay, eventually_ge_atTop (1 : ℝ)] with X hX hXone
  intro θ hθ hadmissible
  apply classRegulatorExceptional_card_le_of_E_ratio s D r θ cSave C X
    hDinj (fun i hi _ hir ↦ htransfer θ i hi hir) hXone
  exact hX θ hθ hadmissible

end

end PellPaper
