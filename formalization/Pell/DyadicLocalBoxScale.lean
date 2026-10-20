import Pell.DyadicBoxReduction
import Pell.LocalRatioDisplacementScale

/-!
# Local displacement denominator from a dyadic coordinate box

`dyadicBox` records lower endpoints for the four integer coordinates.  This
module turns the `e`- and `u`-endpoint facts, together with an independently
specified positive lower scale for the local centre, into the denominator
comparison needed by `LocalRatioDisplacementScale`.

Neither box membership nor `DyadicFactorCondition` is used to invent the
centre lower bound or the product-scale inequality: both remain explicit
hypotheses.
-/

namespace PellPaper

/-- Membership of a four-coordinate dyadic box supplies its four natural
lower endpoints. -/
theorem dyadicBox_coordinate_lower_bounds
    {i : ℕ × ℕ × ℕ × ℕ} {d e u v : ℕ}
    (hbox : (d, e, u, v) ∈ dyadicBox i) :
    2 ^ i.1 ≤ d ∧ 2 ^ i.2.1 ≤ e ∧ 2 ^ i.2.2.1 ≤ u ∧ 2 ^ i.2.2.2 ≤ v := by
  unfold dyadicBox at hbox
  rcases Finset.mem_product.mp hbox with ⟨hd, hrest⟩
  rcases Finset.mem_product.mp hrest with ⟨he, hrest⟩
  rcases Finset.mem_product.mp hrest with ⟨hu, hv⟩
  exact ⟨(Finset.mem_Ico.mp hd).1, (Finset.mem_Ico.mp he).1,
    (Finset.mem_Ico.mp hu).1, (Finset.mem_Ico.mp hv).1⟩

/-- An explicit local-centre lower scale and the lower endpoints of a
dyadic `e,u` box imply the full denominator comparison.  The premise
`hscale` is the precise source-side scale relation still needed to connect
the local coordinate cell to `X`. -/
theorem two_mul_le_local_displacement_denominator_of_mem_dyadicBox
    {i : ℕ × ℕ × ℕ × ℕ} {d e u v : ℕ} {s₀ sₗ X : ℝ}
    (hbox : (d, e, u, v) ∈ dyadicBox i)
    (hsₗ_pos : 0 < sₗ) (hsₗ : sₗ ≤ s₀)
    (hscale : 2 * X ≤ sₗ ^ 2 *
      ((2 ^ i.2.1 : ℕ) : ℝ) ^ 2 * ((2 ^ i.2.2.1 : ℕ) : ℝ)) :
    2 * X ≤ s₀ ^ 2 * (e : ℝ) ^ 2 * (u : ℝ) := by
  have hbox_lower := dyadicBox_coordinate_lower_bounds hbox
  have he_lower : ((2 ^ i.2.1 : ℕ) : ℝ) ≤ (e : ℝ) := by
    exact_mod_cast hbox_lower.2.1
  have hu_lower : ((2 ^ i.2.2.1 : ℕ) : ℝ) ≤ (u : ℝ) := by
    exact_mod_cast hbox_lower.2.2.1
  exact two_mul_le_local_displacement_denominator_of_lower_scales
    hsₗ_pos (by positivity) (by positivity) hsₗ he_lower hu_lower hscale

end PellPaper
