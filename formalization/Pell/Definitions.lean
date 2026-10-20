import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Interval
import Mathlib.NumberTheory.Pell

/-!
# Definitions for the Pell exceptional set

This file supplies the Pell-solution definitions used for `paper/main.tex`.
The source-shaped strict-cutoff exceptional count and the final theorem are
stated in `Pell.FinalPaperResults`. `PellPowerSaving` is a legacy fixed-height
intermediate proposition used by the proof development.
-/

open Filter

namespace PellPaper

/-- The real number `x + y * sqrt d` attached to a solution of Pell's equation.

For the fundamental solution `a` of `x^2 - d*y^2 = 1`, this is the quantity
`epsilon_d = x_d + y_d sqrt d` used throughout `main.tex`.  Defining it for every
`Pell.Solution₁ d` avoids making a noncomputable choice of a fundamental solution.
-/
noncomputable def epsilon {d : ℤ} (a : Pell.Solution₁ d) : ℝ :=
  (a.x : ℝ) + (a.y : ℝ) * Real.sqrt (d : ℝ)

/-- `SmallFundamentalSolution θ m` is the condition
`epsilon_m ≤ m^θ` from the subsection "Small fundamental solutions" of `main.tex`.

The witness is required to be Mathlib's (necessarily unique) positive fundamental
solution.  In particular, the predicate is false when `m` is zero or a square.
-/
def SmallFundamentalSolution (θ : ℝ) (m : ℕ) : Prop :=
  ∃ a : Pell.Solution₁ (m : ℤ),
    Pell.IsFundamental a ∧ epsilon a ≤ (m : ℝ) ^ θ

/-- The positive radicands at most the integer cutoff `X` counted by `E_θ(X)` in
`main.tex`.
-/
noncomputable def exceptionalSet (θ : ℝ) (X : ℕ) : Finset ℕ :=
  by
    classical
    exact (Finset.Icc 1 X).filter (SmallFundamentalSolution θ)

/-- The natural-number-valued exceptional count at an integer cutoff.

This is exactly
`#{m ≤ X : m is nonsquare and epsilon_m ≤ m^θ}` from `main.tex`; positivity and
nonsquareness are consequences of the existence of a fundamental Pell solution.
-/
noncomputable def EInt (θ : ℝ) (X : ℕ) : ℕ :=
  (exceptionalSet θ X).card

/-- The real-valued, real-cutoff version of the exceptional count `E_θ(X)`.

It uses the greatest natural number at most `X`, then coerces the cardinality to `ℝ`.
This is the form used in the asymptotic statement `PellPowerSaving`.
-/
noncomputable def E (θ X : ℝ) : ℝ :=
  EInt θ ⌊X⌋₊

/-- The power saving `Δ(θ) = 3 / (8 θ² + 6)` from equation `e:fixed-delta` of
`main.tex`.
-/
noncomputable def Delta (θ : ℝ) : ℝ :=
  3 / (8 * θ ^ 2 + 6)

/-- Exact formal statement of Theorem `T:pell-power-saving` in `main.tex`:
for fixed `θ ≥ 3` and every positive `ε`,
`E_θ(X) = O_{θ,ε}(X^(1 - 3/(8θ²+6) + ε))` as `X → ∞`.

The nesting of the quantifiers before `IsBigO` permits the implied constant to depend
on `θ` and `ε`, exactly as indicated by the subscript in the paper.
-/
def PellPowerSaving : Prop :=
  ∀ θ : ℝ, 3 ≤ θ → ∀ ε : ℝ, 0 < ε →
    Asymptotics.IsBigO atTop (E θ)
      (fun X : ℝ => X ^ (1 - Delta θ + ε))

/-- A fundamental solution exists uniquely exactly for positive nonsquare Pell
parameters.  This justifies using an existential witness in
`SmallFundamentalSolution`: its value, and hence `epsilon`, is unambiguous.
-/
theorem existsUnique_isFundamental_iff {d : ℤ} :
    (∃! a : Pell.Solution₁ d, Pell.IsFundamental a) ↔
      0 < d ∧ ¬ IsSquare d := by
  constructor
  · rintro ⟨a, ha, _⟩
    exact ⟨ha.d_pos, ha.d_nonsquare⟩
  · rintro ⟨hd_pos, hd_nonsquare⟩
    obtain ⟨a, ha⟩ := Pell.IsFundamental.exists_of_not_isSquare hd_pos hd_nonsquare
    exact ⟨a, ha, fun b hb => Pell.IsFundamental.subsingleton hb ha⟩

/-- Once the fundamental solution has been supplied, the existential definition of
`SmallFundamentalSolution` is equivalent to the expected inequality for that solution.
-/
theorem smallFundamentalSolution_iff_of_isFundamental {θ : ℝ} {m : ℕ}
    {a : Pell.Solution₁ (m : ℤ)} (ha : Pell.IsFundamental a) :
    SmallFundamentalSolution θ m ↔ epsilon a ≤ (m : ℝ) ^ θ := by
  constructor
  · rintro ⟨b, hb, hsmall⟩
    rw [Pell.IsFundamental.subsingleton hb ha] at hsmall
    exact hsmall
  · exact fun hsmall => ⟨a, ha, hsmall⟩

/-- Any radicand satisfying `SmallFundamentalSolution` is positive and nonsquare,
as required in the definition of `E_θ(X)` in `main.tex`.
-/
theorem positive_nonsquare_of_smallFundamentalSolution {θ : ℝ} {m : ℕ}
    (h : SmallFundamentalSolution θ m) : 0 < m ∧ ¬ IsSquare m := by
  obtain ⟨a, ha, _⟩ := h
  constructor
  · exact_mod_cast ha.d_pos
  · simpa only [Int.isSquare_natCast_iff] using ha.d_nonsquare

/-- Membership in the exceptional set unfolds to the paper's two defining
conditions: a positive cutoff condition and a small fundamental solution.
-/
theorem mem_exceptionalSet {θ : ℝ} {X m : ℕ} :
    m ∈ exceptionalSet θ X ↔ 1 ≤ m ∧ m ≤ X ∧ SmallFundamentalSolution θ m := by
  simp [exceptionalSet, and_assoc]

end PellPaper
