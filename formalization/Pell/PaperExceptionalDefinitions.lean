import Pell.ExceptionalMonotonicity
import Pell.UniformExceptional
import Mathlib.Tactic

/-!
# The manuscript's exceptional count

The source uses the strict real cutoff `D < X`. These definitions and their
comparison with the inclusive count are independent of the counting proof.
-/

namespace PellPaper
noncomputable section

/-- The literal exceptional set in `paper/main.tex`, with strict real cutoff `D < X`. -/
def paperExceptionalSet (θ X : ℝ) : Finset ℕ :=
  (exceptionalSet θ ⌊X⌋₊).filter fun D => (D : ℝ) < X

/-- The literal count `E_θ(X)` from `paper/main.tex`. -/
def paperExceptionalCount (θ X : ℝ) : ℕ :=
  (paperExceptionalSet θ X).card

theorem mem_paperExceptionalSet {θ X : ℝ} {D : ℕ} :
    D ∈ paperExceptionalSet θ X ↔
      0 < D ∧ (D : ℝ) < X ∧ SmallFundamentalSolution θ D := by
  simp only [paperExceptionalSet, Finset.mem_filter, mem_exceptionalSet,
    Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero]
  constructor
  · rintro ⟨⟨hD, _, hsmall⟩, hDX⟩
    exact ⟨hD, hDX, hsmall⟩
  · rintro ⟨hD, hDX, hsmall⟩
    refine ⟨⟨hD, ?_, hsmall⟩, hDX⟩
    exact Nat.le_floor hDX.le

/-- Strict-endpoint counts are bounded by the closed-cutoff API used in the
analytic proof. -/
theorem paperExceptionalCount_le_E (θ X : ℝ) :
    (paperExceptionalCount θ X : ℝ) ≤ E θ X := by
  change ((paperExceptionalSet θ X).card : ℝ) ≤
    ((exceptionalSet θ ⌊X⌋₊).card : ℝ)
  unfold paperExceptionalSet
  exact_mod_cast Finset.card_filter_le
    (s := exceptionalSet θ ⌊X⌋₊) (p := fun D : ℕ => (D : ℝ) < X)

theorem paperExceptionalCount_mono {θ φ X : ℝ} (hθφ : θ ≤ φ) :
    paperExceptionalCount θ X ≤ paperExceptionalCount φ X := by
  unfold paperExceptionalCount
  apply Finset.card_le_card
  intro D hD
  obtain ⟨hDpos, hDX, hsmall⟩ := mem_paperExceptionalSet.mp hD
  exact mem_paperExceptionalSet.mpr
    ⟨hDpos, hDX, smallFundamentalSolution_mono hθφ hsmall⟩

/-- In the theorem's range, the ceiling degree is no larger than `θ`. -/
theorem uniformQ_le_theta {θ : ℝ} (hθ : 3 ≤ θ) :
    (uniformQ θ : ℝ) ≤ θ := by
  linarith [two_mul_uniformQ_lt hθ]


end
end PellPaper
