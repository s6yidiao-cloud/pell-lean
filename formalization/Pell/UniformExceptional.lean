import Pell.Definitions

/-!
# The uniform Pell exceptional-set target

This file specifies the uniform exceptional-set estimate proved by the
determinant and square-sieve argument. The unconditional proof is in
`Pell.Main3ElementaryFinalAssembly`; `Pell.FinalPaperResults` translates its
ceiling parameter and inclusive cutoff into the statement of `paper/main.tex`.
The elementary facts about the ceiling parameter are proved below.
-/

open Filter

namespace PellPaper

/-- The two-layer degree
`Q(θ) = ⌈θ / 2 + 1 / 4⌉` in Proposition `P:uniform-exceptional`.

It is natural-number-valued because it is used as a polynomial degree in the
proof of the proposition. -/
noncomputable def uniformQ (θ : ℝ) : ℕ :=
  ⌈θ / 2 + 1 / 4⌉₊

/-- The logarithmic range in which the uniform exceptional-set estimate is
asserted. -/
def UniformAdmissible (cExc θ X : ℝ) : Prop :=
  (uniformQ θ : ℝ) ≤
    cExc * Real.sqrt (Real.log X / Real.log (Real.log X))

/-- Exact formal target of Proposition `P:uniform-exceptional` for the fixed
absolute saving `cSave` chosen in equation `e:uniform-saving-choice`.

The witnesses `cExc` and `C` precede both `X` and `θ`; this expresses that the
admissibility constant and the implied constant are absolute.  The `atTop`
quantifier expresses "for all sufficiently large `X`" and, because it precedes
the quantifier over `θ`, supplies one threshold that is uniform in `θ`. -/
def UniformExceptionalEstimate (cSave : ℝ) : Prop :=
  0 < cSave ∧
    ∃ cExc C : ℝ, 0 < cExc ∧ 0 < C ∧
      ∀ᶠ X : ℝ in atTop, ∀ θ : ℝ, 3 ≤ θ →
        UniformAdmissible cExc θ X →
          E θ X ≤ C * X ^ (1 - cSave / (uniformQ θ : ℝ) ^ 2)

/-- The defining real number lies below its natural ceiling. -/
theorem uniformQ_lower (θ : ℝ) :
    θ / 2 + 1 / 4 ≤ (uniformQ θ : ℝ) := by
  exact Nat.le_ceil (θ / 2 + 1 / 4)

/-- In the range of the proposition the degree is at least two. -/
theorem two_le_uniformQ {θ : ℝ} (hθ : 3 ≤ θ) :
    2 ≤ uniformQ θ := by
  change 1 < uniformQ θ
  rw [uniformQ, Nat.lt_ceil]
  linarith

/-- In particular, the degree is positive after coercion to the reals. -/
theorem uniformQ_pos {θ : ℝ} (hθ : 3 ≤ θ) :
    0 < (uniformQ θ : ℝ) := by
  exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) (two_le_uniformQ hθ))

/-- Doubling the ceiling dominates `θ + 1/2`. -/
theorem theta_add_half_le_two_mul_uniformQ (θ : ℝ) :
    θ + 1 / 2 ≤ 2 * (uniformQ θ : ℝ) := by
  linarith [uniformQ_lower θ]

/-- The strict estimate `θ + 1/4 < 2Q` used in the proof of
Proposition `P:uniform-exceptional`. -/
theorem theta_add_quarter_lt_two_mul_uniformQ (θ : ℝ) :
    θ + 1 / 4 < 2 * (uniformQ θ : ℝ) := by
  linarith [uniformQ_lower θ]

/-- The ceiling is less than one above its defining real number. -/
theorem uniformQ_lt_add_one {θ : ℝ} (hθ : 3 ≤ θ) :
    (uniformQ θ : ℝ) < θ / 2 + 1 / 4 + 1 := by
  apply Nat.ceil_lt_add_one
  linarith

/-- A matching elementary upper comparison, making `Q(θ) ≍ θ` explicit. -/
theorem two_mul_uniformQ_lt {θ : ℝ} (hθ : 3 ≤ θ) :
    2 * (uniformQ θ : ℝ) < θ + 5 / 2 := by
  linarith [uniformQ_lt_add_one hθ]

end PellPaper
