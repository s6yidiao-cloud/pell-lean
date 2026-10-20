import Pell.Elementary

/-!
# The Pell power-saving target

`PellPowerSaving` in `Pell.Definitions` is the exact formal statement of
Theorem `T:pell-power-saving` in `main.tex`. The determinant-method estimate
which proves it is not present in Mathlib, so this module records only verified
elementary facts about its exponent and imports the completed square-part
transfer needed by the paper's final reduction.
-/

namespace PellPaper

/-- The saving exponent from the paper is strictly positive. -/
theorem Delta_pos (θ : ℝ) : 0 < Delta θ := by
  unfold Delta
  positivity

/-- The saving exponent is at most one half. This elementary bound is useful
when summing the square-part tail in the proof of `T:pell-power-saving`. -/
theorem Delta_le_one_half (θ : ℝ) : Delta θ ≤ (1 : ℝ) / 2 := by
  unfold Delta
  apply (div_le_iff₀ (by positivity : 0 < 8 * θ ^ 2 + 6)).2
  nlinarith [sq_nonneg θ]

/-- The determinant threshold `G(ξ)` from equation `e:fixed-delta`. -/
noncomputable def determinantThreshold (ξ : ℝ) : ℝ :=
  4 * ξ ^ 2 / (4 * ξ ^ 2 + 3)

/-- The exact relation between the determinant threshold and the power saving
in equation `e:fixed-delta`. -/
theorem one_sub_determinantThreshold_div_two (ξ : ℝ) :
    (1 - determinantThreshold ξ) / 2 = Delta ξ := by
  have hden : 4 * ξ ^ 2 + 3 ≠ 0 := by positivity
  unfold determinantThreshold Delta
  field_simp
  ring

/-- The squarefree cutoff condition used in the balanced-box argument: choosing
`κ < Δ(θ)` is exactly the same as putting the exponent `1 - 2κ` above
the determinant threshold `G(θ)`. -/
theorem lt_Delta_iff_determinantThreshold_lt (θ κ : ℝ) :
    κ < Delta θ ↔ determinantThreshold θ < 1 - 2 * κ := by
  have hrelation := one_sub_determinantThreshold_div_two θ
  constructor <;> intro h <;> nlinarith

/-- In the squarefree range `θ ≥ 3`, the saving is at most `1/26`, as
used in the unbalanced parameter choice. -/
theorem Delta_le_one_div_twenty_six (θ : ℝ) (hθ : 3 ≤ θ) :
    Delta θ ≤ (1 : ℝ) / 26 := by
  have hden : 0 < 8 * θ ^ 2 + 6 := by positivity
  unfold Delta
  apply (div_le_iff₀ hden).2
  nlinarith [sq_nonneg (θ - 3)]

/-- The exponent saved on the square-part layer `s = Y^α`.  This is the
quantity `F_θ(α)` in equation `e:fixed-layer-saving` of the manuscript,
using the rational normalization displayed there.  In particular, this
definition remains meaningful at the endpoint `1 - 2α = 0`. -/
noncomputable def squarePartLayerSaving (θ α : ℝ) : ℝ :=
  α + 3 * (1 - 2 * α) ^ 3 /
    (2 * (4 * θ ^ 2 + 3 * (1 - 2 * α) ^ 2))

/-- The layer-saving expression is exactly the rescaled fixed-height saving
from the squarefree part, when `σ = 1 - 2α` is nonzero.  This is the identity
`F_θ(α) = α + σ Δ(θ / σ)` displayed in the square-parts proof. -/
theorem squarePartLayerSaving_eq_add_scaled_Delta {θ α : ℝ}
    (hσ : 1 - 2 * α ≠ 0) :
    squarePartLayerSaving θ α =
      α + (1 - 2 * α) * Delta (θ / (1 - 2 * α)) := by
  let σ : ℝ := 1 - 2 * α
  have hσ' : σ ≠ 0 := by simpa [σ] using hσ
  have hσsq : 0 < σ ^ 2 := sq_pos_of_ne_zero hσ'
  have hden : 0 < 4 * θ ^ 2 + 3 * σ ^ 2 := by
    positivity
  have hscaled : 0 < 8 * (θ / σ) ^ 2 + 6 := by
    positivity
  unfold squarePartLayerSaving Delta
  change α + 3 * σ ^ 3 / (2 * (4 * θ ^ 2 + 3 * σ ^ 2)) =
    α + σ * (3 / (8 * (θ / σ) ^ 2 + 6))
  field_simp [hσ', hden.ne', hscaled.ne']
  ring

/-- At the squarefree layer, the rescaled saving is the original one. -/
theorem squarePartLayerSaving_zero (θ : ℝ) :
    squarePartLayerSaving θ 0 = Delta θ := by
  unfold squarePartLayerSaving Delta
  field_simp
  ring

/-- The exact algebraic gain of a square-part layer over the base saving.
The hypothesis on `θ` also keeps every displayed denominator strictly
positive.  The proof treats `1 - 2α = 0` separately, since division in a
field is totalized at zero. -/
theorem squarePartLayerSaving_sub_Delta (θ α : ℝ) (hθ : 3 ≤ θ) :
    squarePartLayerSaving θ α - Delta θ =
      4 * α * θ ^ 2 * (6 * α + 4 * θ ^ 2 - 3) /
        ((4 * θ ^ 2 + 3) * (4 * θ ^ 2 + 3 * (1 - 2 * α) ^ 2)) := by
  have hθpos : 0 < θ := by linarith
  have hbase : 0 < 4 * θ ^ 2 + 3 := by positivity
  by_cases hσ : 1 - 2 * α = 0
  · have hα : α = 1 / 2 := by linarith
    subst α
    unfold squarePartLayerSaving Delta
    (field_simp; ring)
  · have hscaled : 0 < 4 * θ ^ 2 + 3 * (1 - 2 * α) ^ 2 := by positivity
    unfold squarePartLayerSaving Delta
    (field_simp; ring)

/-- **Square-part layer saving** (the algebra in
`e:fixed-layer-saving`--`e:fixed-layer-derivative`): no layer with a
nonnegative square-part exponent loses any of the saving `Delta θ`. -/
theorem Delta_le_squarePartLayerSaving (θ α : ℝ) (hθ : 3 ≤ θ) (hα : 0 ≤ α) :
    Delta θ ≤ squarePartLayerSaving θ α := by
  rw [← sub_nonneg, squarePartLayerSaving_sub_Delta θ α hθ]
  have hθpos : 0 < θ := by linarith
  have hbase : 0 < 4 * θ ^ 2 + 3 := by positivity
  have hscaled : 0 < 4 * θ ^ 2 + 3 * (1 - 2 * α) ^ 2 := by positivity
  have hproduct : 0 ≤ (θ - 3) * (θ + 3) :=
    mul_nonneg (sub_nonneg.mpr hθ) (by linarith)
  have hfactor : 0 ≤ 6 * α + 4 * θ ^ 2 - 3 := by
    nlinarith
  positivity

/-- A named alias for the manuscript's second theorem. It is a proposition,
not an assumed axiom: a future determinant-method development must construct
a term of this type. -/
abbrev PellPowerSavingTheorem : Prop := PellPowerSaving

end PellPaper
