import Mathlib.Data.Nat.Squarefree
import Pell.Definitions

/-!
# The fixed-height estimate for squarefree radicands

This file gives the precise interface for Proposition
`P:fixed-height-squarefree` of `main.tex`.  The analytic estimate is recorded as
a proposition, while the elementary facts about the finite dyadic set are proved.
-/

open Filter

namespace PellPaper

/-- The squarefree radicands in the half-open dyadic interval `[Y, 2Y)` whose
fundamental Pell solution satisfies `epsilon_w ≤ w^θ`.

This is the set inside the cardinality in equation
`e:fixed-squarefree-conclusion` of `main.tex`; `Squarefree w` is the
natural-number formulation of `μ²(w) = 1`.
-/
noncomputable def squarefreeDyadicExceptionalSet (θ : ℝ) (Y : ℕ) : Finset ℕ :=
  by
    classical
    exact (Finset.Ico Y (2 * Y)).filter
      (fun w => Squarefree w ∧ SmallFundamentalSolution θ w)

/-- The cardinality of `squarefreeDyadicExceptionalSet`. -/
noncomputable def squarefreeDyadicExceptionalCount (θ : ℝ) (Y : ℕ) : ℕ :=
  (squarefreeDyadicExceptionalSet θ Y).card

/-- Exact formal statement of Proposition `P:fixed-height-squarefree`:
for every fixed `θ ≥ 3` and `0 < δ < Δ(θ)`, the number of squarefree
exceptional radicands in `[Y, 2Y)` is `O_{θ,δ}(Y^(1-δ))`.

Putting `θ` and `δ` outside `IsBigO` lets its implicit constant depend on both
parameters, as in the manuscript.
-/
def FixedHeightSquarefree : Prop :=
  ∀ θ : ℝ, 3 ≤ θ → ∀ δ : ℝ, 0 < δ → δ < Delta θ →
    Asymptotics.IsBigO atTop
      (fun Y : ℕ => (squarefreeDyadicExceptionalCount θ Y : ℝ))
      (fun Y : ℕ => (Y : ℝ) ^ (1 - δ))

/-- Membership unfolds to the four conditions displayed in the manuscript. -/
theorem mem_squarefreeDyadicExceptionalSet {θ : ℝ} {Y w : ℕ} :
    w ∈ squarefreeDyadicExceptionalSet θ Y ↔
      Y ≤ w ∧ w < 2 * Y ∧ Squarefree w ∧
        SmallFundamentalSolution θ w := by
  simp [squarefreeDyadicExceptionalSet, and_assoc]

/-- Supplying the fundamental Pell solution turns the membership predicate
into the literal inequality appearing in the manuscript. -/
theorem mem_squarefreeDyadicExceptionalSet_iff_of_isFundamental
    {θ : ℝ} {Y w : ℕ} {a : Pell.Solution₁ (w : ℤ)}
    (ha : Pell.IsFundamental a) :
    w ∈ squarefreeDyadicExceptionalSet θ Y ↔
      Y ≤ w ∧ w < 2 * Y ∧ Squarefree w ∧ epsilon a ≤ (w : ℝ) ^ θ := by
  rw [mem_squarefreeDyadicExceptionalSet,
    smallFundamentalSolution_iff_of_isFundamental ha]

/-- The exceptional set is a subset of its defining finite interval. -/
theorem squarefreeDyadicExceptionalSet_subset_Ico (θ : ℝ) (Y : ℕ) :
    squarefreeDyadicExceptionalSet θ Y ⊆ Finset.Ico Y (2 * Y) := by
  classical
  exact Finset.filter_subset _ _

/-- Every member lies in the defining dyadic half-open interval. -/
theorem dyadic_bounds_of_mem_squarefreeDyadicExceptionalSet {θ : ℝ} {Y w : ℕ}
    (hw : w ∈ squarefreeDyadicExceptionalSet θ Y) :
    Y ≤ w ∧ w < 2 * Y := by
  exact ⟨(mem_squarefreeDyadicExceptionalSet.mp hw).1,
    (mem_squarefreeDyadicExceptionalSet.mp hw).2.1⟩

/-- Every member of the fixed-height set is squarefree. -/
theorem squarefree_of_mem_squarefreeDyadicExceptionalSet {θ : ℝ} {Y w : ℕ}
    (hw : w ∈ squarefreeDyadicExceptionalSet θ Y) : Squarefree w := by
  exact (mem_squarefreeDyadicExceptionalSet.mp hw).2.2.1

/-- Every member satisfies the same small-fundamental-solution predicate used
by the global exceptional set `exceptionalSet`. -/
theorem smallFundamentalSolution_of_mem_squarefreeDyadicExceptionalSet
    {θ : ℝ} {Y w : ℕ} (hw : w ∈ squarefreeDyadicExceptionalSet θ Y) :
    SmallFundamentalSolution θ w := by
  exact (mem_squarefreeDyadicExceptionalSet.mp hw).2.2.2

/-- Fixed-height squarefree exceptional radicands are positive and nonsquare. -/
theorem positive_nonsquare_of_mem_squarefreeDyadicExceptionalSet
    {θ : ℝ} {Y w : ℕ} (hw : w ∈ squarefreeDyadicExceptionalSet θ Y) :
    0 < w ∧ ¬ IsSquare w := by
  exact positive_nonsquare_of_smallFundamentalSolution
    (smallFundamentalSolution_of_mem_squarefreeDyadicExceptionalSet hw)

/-- Consequently every radicand counted in the dyadic squarefree set is
strictly greater than one. -/
theorem one_lt_of_mem_squarefreeDyadicExceptionalSet {θ : ℝ} {Y w : ℕ}
    (hw : w ∈ squarefreeDyadicExceptionalSet θ Y) : 1 < w := by
  obtain ⟨hwpos, hwnsq⟩ :=
    positive_nonsquare_of_mem_squarefreeDyadicExceptionalSet hw
  have hw_ne_one : w ≠ 1 := by
    intro h
    apply hwnsq
    simp [h]
  omega

/-- The zero and unit radicands never occur in a squarefree dyadic
exceptional set. -/
theorem not_mem_squarefreeDyadicExceptionalSet_of_le_one {θ : ℝ} {Y w : ℕ}
    (hw : w ≤ 1) : w ∉ squarefreeDyadicExceptionalSet θ Y := by
  intro hmem
  exact (Nat.not_lt_of_ge hw) (one_lt_of_mem_squarefreeDyadicExceptionalSet hmem)

/-- A dyadic interval containing an exceptional radicand must have scale
greater than one. -/
theorem one_lt_scale_of_mem_squarefreeDyadicExceptionalSet {θ : ℝ} {Y w : ℕ}
    (hw : w ∈ squarefreeDyadicExceptionalSet θ Y) : 1 < Y := by
  have hwgt := one_lt_of_mem_squarefreeDyadicExceptionalSet hw
  have hwlt := (dyadic_bounds_of_mem_squarefreeDyadicExceptionalSet hw).2
  omega

/-- The fixed-height set is contained in the global exceptional set at cutoff
`2Y`; the latter uses a closed upper endpoint, so this formulation is valid
without a special case at `Y = 0`. -/
theorem mem_exceptionalSet_two_mul_of_mem_squarefreeDyadicExceptionalSet
    {θ : ℝ} {Y w : ℕ} (hw : w ∈ squarefreeDyadicExceptionalSet θ Y) :
    w ∈ exceptionalSet θ (2 * Y) := by
  rw [mem_exceptionalSet]
  have hsmall := smallFundamentalSolution_of_mem_squarefreeDyadicExceptionalSet hw
  have hwpos := (positive_nonsquare_of_smallFundamentalSolution hsmall).1
  have hwlt := (dyadic_bounds_of_mem_squarefreeDyadicExceptionalSet hw).2
  exact ⟨hwpos, Nat.le_of_lt hwlt, hsmall⟩

/-- Equivalently, the fixed-height set consists of those global exceptional
radicands which are squarefree and lie in the half-open dyadic interval. -/
theorem mem_squarefreeDyadicExceptionalSet_iff_mem_exceptionalSet
    {θ : ℝ} {Y w : ℕ} :
    w ∈ squarefreeDyadicExceptionalSet θ Y ↔
      w ∈ exceptionalSet θ (2 * Y) ∧ Y ≤ w ∧ w < 2 * Y ∧ Squarefree w := by
  constructor
  · intro hw
    obtain ⟨hlo, hhi, hsf, _⟩ := mem_squarefreeDyadicExceptionalSet.mp hw
    exact ⟨mem_exceptionalSet_two_mul_of_mem_squarefreeDyadicExceptionalSet hw,
      hlo, hhi, hsf⟩
  · rintro ⟨hglobal, hlo, hhi, hsf⟩
    exact mem_squarefreeDyadicExceptionalSet.mpr
      ⟨hlo, hhi, hsf, (mem_exceptionalSet.mp hglobal).2.2⟩

/-- The dyadic squarefree count is bounded by the global exceptional count at
cutoff `2Y`. -/
theorem squarefreeDyadicExceptionalCount_le_EInt (θ : ℝ) (Y : ℕ) :
    squarefreeDyadicExceptionalCount θ Y ≤ EInt θ (2 * Y) := by
  classical
  exact Finset.card_le_card fun w hw =>
    mem_exceptionalSet_two_mul_of_mem_squarefreeDyadicExceptionalSet hw

/-- The elementary interval-length bound for the fixed-height count. -/
theorem squarefreeDyadicExceptionalCount_le_scale (θ : ℝ) (Y : ℕ) :
    squarefreeDyadicExceptionalCount θ Y ≤ Y := by
  have hcard := Finset.card_le_card (squarefreeDyadicExceptionalSet_subset_Ico θ Y)
  simpa [squarefreeDyadicExceptionalCount, Nat.card_Ico, two_mul] using hcard

/-- At the zero scale the half-open dyadic interval is empty. -/
@[simp] theorem squarefreeDyadicExceptionalSet_zero (θ : ℝ) :
    squarefreeDyadicExceptionalSet θ 0 = ∅ := by
  simp [squarefreeDyadicExceptionalSet]

/-- The corresponding count at the zero scale is zero. -/
@[simp] theorem squarefreeDyadicExceptionalCount_zero (θ : ℝ) :
    squarefreeDyadicExceptionalCount θ 0 = 0 := by
  simp [squarefreeDyadicExceptionalCount]

/-- The only natural radicand in `[1, 2)` is one, which is a square. -/
@[simp] theorem squarefreeDyadicExceptionalSet_one (θ : ℝ) :
    squarefreeDyadicExceptionalSet θ 1 = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  have hscale := one_lt_scale_of_mem_squarefreeDyadicExceptionalSet hw
  omega

/-- The corresponding count at scale one is zero. -/
@[simp] theorem squarefreeDyadicExceptionalCount_one (θ : ℝ) :
    squarefreeDyadicExceptionalCount θ 1 = 0 := by
  simp [squarefreeDyadicExceptionalCount]

end PellPaper
