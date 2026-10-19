import Mathlib.LinearAlgebra.Lagrange

/-!
# The finite general-bidegree exponent grid

This module formalizes the elementary coefficient grid used in `L:sheared`
of `main.tex`:

`Γ_{A,B} = {(a + 2b, b) : 0 ≤ a ≤ A, 0 ≤ b ≤ B}`.

It records its faithful finite indexing, its cardinality, and the
parallel-line polynomial that vanishes on it.  It also gives a literal
two-coordinate Lagrange formula over `ℚ`: every rational-valued function on
the finite grid is recovered by the formula from its values.

Nothing here estimates a rank filtration, a determinant, a coefficient
height, or a number of solutions.  In particular, the module is only the
finite algebraic input preceding the determinant-decay step of `L:sheared`.
-/

namespace PellPaper

open Finset
open scoped BigOperators

/-- The finite index set for the coefficient grid of bidegree `(A,B)`. -/
abbrev generalBidegreeGridIndex (A B : ℕ) := Fin (A + 1) × Fin (B + 1)

/-- The coordinate map `(a,b) ↦ (a + 2b,b)` for the general-bidegree grid. -/
def generalBidegreeCoordinateEmbedding : ℕ × ℕ ↪ ℤ × ℤ where
  toFun p := (((p.1 + 2 * p.2 : ℕ) : ℤ), (p.2 : ℤ))
  inj' := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    have hfst : ((a + 2 * b : ℕ) : ℤ) = ((c + 2 * d : ℕ) : ℤ) :=
      congrArg Prod.fst h
    have hsnd : (b : ℤ) = (d : ℤ) := congrArg Prod.snd h
    have hbd : b = d := by
      exact_mod_cast hsnd
    subst d
    have hsum : a + 2 * b = c + 2 * b := by
      exact_mod_cast hfst
    have hac : a = c := Nat.add_right_cancel hsum
    subst c
    rfl

/-- The finite coefficient grid `Γ_{A,B}`. -/
def generalBidegreeGrid (A B : ℕ) : Finset (ℤ × ℤ) :=
  ((range (A + 1)).product (range (B + 1))).map
    generalBidegreeCoordinateEmbedding

/-- The grid index set has the expected number of elements. -/
@[simp] theorem card_generalBidegreeGridIndex (A B : ℕ) :
    Fintype.card (generalBidegreeGridIndex A B) = (A + 1) * (B + 1) := by
  simp

/-- The finite coefficient grid has exactly `(A+1)(B+1)` distinct points. -/
theorem card_generalBidegreeGrid (A B : ℕ) :
    (generalBidegreeGrid A B).card = (A + 1) * (B + 1) := by
  simp [generalBidegreeGrid, Finset.card_product]

/-- The point indexed by permitted coordinates belongs to the finite grid. -/
theorem mem_generalBidegreeGrid (A B a b : ℕ) (ha : a ≤ A) (hb : b ≤ B) :
    (((a + 2 * b : ℕ) : ℤ), (b : ℤ)) ∈ generalBidegreeGrid A B := by
  unfold generalBidegreeGrid
  apply mem_map.mpr
  refine ⟨(a, b), ?_, rfl⟩
  apply mem_product.mpr
  constructor
  · exact mem_range.mpr (Nat.lt_succ_of_le ha)
  · exact mem_range.mpr (Nat.lt_succ_of_le hb)

/-- Every grid point has the advertised bounded coordinate description. -/
theorem mem_generalBidegreeGrid_iff {A B : ℕ} {N₁ N₂ : ℤ} :
    (N₁, N₂) ∈ generalBidegreeGrid A B ↔
      ∃ a b : ℕ, a ≤ A ∧ b ≤ B ∧
        N₁ = ((a + 2 * b : ℕ) : ℤ) ∧ N₂ = (b : ℤ) := by
  constructor
  · intro h
    unfold generalBidegreeGrid at h
    rcases mem_map.mp h with ⟨⟨a, b⟩, hab, hcoord⟩
    rcases Finset.mem_product.mp hab with ⟨ha, hb⟩
    have ha' : a < A + 1 := Finset.mem_range.mp ha
    have hb' : b < B + 1 := Finset.mem_range.mp hb
    refine ⟨a, b, by omega, by omega, ?_, ?_⟩
    · simpa [generalBidegreeCoordinateEmbedding] using
        congrArg Prod.fst hcoord.symm
    · simpa [generalBidegreeCoordinateEmbedding] using
        congrArg Prod.snd hcoord.symm
  · rintro ⟨a, b, ha, hb, rfl, rfl⟩
    exact mem_generalBidegreeGrid A B a b ha hb

/-- The explicit bijective parametrization of the finite grid by its two
bounded coefficient indices. -/
def generalBidegreeGridPoint (A B : ℕ)
    (ab : generalBidegreeGridIndex A B) : generalBidegreeGrid A B :=
  ⟨(((ab.1.1 + 2 * ab.2.1 : ℕ) : ℤ), (ab.2.1 : ℤ)),
    mem_generalBidegreeGrid A B ab.1.1 ab.2.1
      (Nat.le_of_lt_succ ab.1.2) (Nat.le_of_lt_succ ab.2.2)⟩

/-- The index-to-grid map is injective. -/
theorem generalBidegreeGridPoint_injective (A B : ℕ) :
    Function.Injective (generalBidegreeGridPoint A B) := by
  intro ab cd h
  have hval := congrArg Subtype.val h
  have hfst : ((ab.1.1 + 2 * ab.2.1 : ℕ) : ℤ) =
      ((cd.1.1 + 2 * cd.2.1 : ℕ) : ℤ) := by
    simpa [generalBidegreeGridPoint] using congrArg Prod.fst hval
  have hsnd : (ab.2.1 : ℤ) = (cd.2.1 : ℤ) := by
    simpa [generalBidegreeGridPoint] using congrArg Prod.snd hval
  have hsecond : ab.2.1 = cd.2.1 := by
    exact_mod_cast hsnd
  have hsum : ab.1.1 + 2 * ab.2.1 = cd.1.1 + 2 * cd.2.1 := by
    exact_mod_cast hfst
  have hfirst : ab.1.1 = cd.1.1 := by
    have hsum' : ab.1.1 + 2 * ab.2.1 = cd.1.1 + 2 * ab.2.1 := by
      simpa [hsecond] using hsum
    exact Nat.add_right_cancel hsum'
  apply Prod.ext
  · apply Fin.ext
    exact hfirst
  · apply Fin.ext
    exact hsecond

/-- The index-to-grid map covers the entire finite grid. -/
theorem generalBidegreeGridPoint_surjective (A B : ℕ) :
    Function.Surjective (generalBidegreeGridPoint A B) := by
  intro p
  rcases mem_generalBidegreeGrid_iff.mp p.2 with
    ⟨a, b, ha, hb, hfst, hsnd⟩
  refine ⟨(⟨a, Nat.lt_succ_of_le ha⟩, ⟨b, Nat.lt_succ_of_le hb⟩), ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · simpa [generalBidegreeGridPoint] using hfst.symm
  · simpa [generalBidegreeGridPoint] using hsnd.symm

/-- The bounded coefficient indices and the finite grid are in bijection. -/
theorem generalBidegreeGridPoint_bijective (A B : ℕ) :
    Function.Bijective (generalBidegreeGridPoint A B) :=
  ⟨generalBidegreeGridPoint_injective A B,
    generalBidegreeGridPoint_surjective A B⟩

/-- The parallel-line annihilator for the grid, represented by its integer
evaluation. -/
def generalBidegreeParallelLineVanishing (A : ℕ) (N₁ N₂ : ℤ) : ℤ :=
  ∏ a ∈ range (A + 1), (N₁ - 2 * N₂ - a)

/-- The `a`-th parallel line kills the parallel-line annihilator. -/
theorem generalBidegreeParallelLineVanishing_eval (A a b : ℕ) (ha : a ≤ A) :
    generalBidegreeParallelLineVanishing A
      ((a + 2 * b : ℕ) : ℤ) (b : ℤ) = 0 := by
  unfold generalBidegreeParallelLineVanishing
  apply Finset.prod_eq_zero (i := a) (f := fun i : ℕ =>
    ((a + 2 * b : ℕ) : ℤ) - 2 * (b : ℤ) - i)
  · exact mem_range.mpr (Nat.lt_succ_of_le ha)
  · push_cast
    ring

/-- A function in the two exponent variables vanishes on the general grid
when all of its grid evaluations vanish. -/
def VanishesOnGeneralBidegreeGrid (A B : ℕ) (f : ℤ → ℤ → ℤ) : Prop :=
  ∀ p ∈ generalBidegreeGrid A B, f p.1 p.2 = 0

/-- The parallel-line annihilator vanishes on every point of `Γ_{A,B}`. -/
theorem generalBidegreeParallelLineVanishing_vanishesOn_grid (A B : ℕ) :
    VanishesOnGeneralBidegreeGrid A B
      (generalBidegreeParallelLineVanishing A) := by
  intro p hp
  rcases mem_generalBidegreeGrid_iff.mp hp with
    ⟨a, b, ha, _hb, hfst, hsnd⟩
  have hp' : p = (((a + 2 * b : ℕ) : ℤ), (b : ℤ)) :=
    Prod.ext hfst hsnd
  rw [hp']
  exact generalBidegreeParallelLineVanishing_eval A a b ha

/-- The ordinary univariate Lagrange weight at a finite rational node. -/
noncomputable def finiteLagrangeWeight {n : ℕ} (i : Fin n) (x : ℚ) : ℚ :=
  (Lagrange.basis (Finset.univ : Finset (Fin n))
    (fun j : Fin n => (j.1 : ℚ)) i).eval x

/-- Natural-number casts give distinct rational Lagrange nodes. -/
theorem finiteLagrangeNode_injective (n : ℕ) :
    Function.Injective (fun i : Fin n => (i.1 : ℚ)) := by
  intro i j h
  apply Fin.ext
  exact Nat.cast_injective h

/-- A finite Lagrange weight is one at its own node. -/
@[simp] theorem finiteLagrangeWeight_self {n : ℕ} (i : Fin n) :
    finiteLagrangeWeight i (i.1 : ℚ) = 1 := by
  unfold finiteLagrangeWeight
  exact Lagrange.eval_basis_self
    (s := (Finset.univ : Finset (Fin n)))
    (v := fun j : Fin n => (j.1 : ℚ))
    (i := i) (finiteLagrangeNode_injective n).injOn (Finset.mem_univ i)

/-- A finite Lagrange weight is zero at every other node. -/
@[simp] theorem finiteLagrangeWeight_ne {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    finiteLagrangeWeight i (j.1 : ℚ) = 0 := by
  unfold finiteLagrangeWeight
  exact Lagrange.eval_basis_of_ne
    (s := (Finset.univ : Finset (Fin n)))
    (v := fun k : Fin n => (k.1 : ℚ))
    (i := i) (j := j) hij (Finset.mem_univ j)

/-- The explicit tensor-product Lagrange formula on the general-bidegree
grid.  Its two variables are `N₁` and `N₂`; the first univariate factor is
applied to the sheared coordinate `N₁ - 2N₂`. -/
noncomputable def generalBidegreeGridInterpolant (A B : ℕ)
    (f : generalBidegreeGrid A B → ℚ) : ℚ → ℚ → ℚ :=
  fun N₁ N₂ =>
    ∑ a : Fin (A + 1), ∑ b : Fin (B + 1),
      f (generalBidegreeGridPoint A B (a, b)) *
        finiteLagrangeWeight a (N₁ - 2 * N₂) *
          finiteLagrangeWeight b N₂

/-- The explicit interpolation formula recovers a grid value at an indexed
point. -/
theorem generalBidegreeGridInterpolant_eval_point (A B : ℕ)
    (f : generalBidegreeGrid A B → ℚ) (a : Fin (A + 1)) (b : Fin (B + 1)) :
    generalBidegreeGridInterpolant A B f
      ((a.1 + 2 * b.1 : ℕ) : ℚ) (b.1 : ℚ) =
        f (generalBidegreeGridPoint A B (a, b)) := by
  classical
  unfold generalBidegreeGridInterpolant
  have hshear : ((a.1 + 2 * b.1 : ℕ) : ℚ) - 2 * (b.1 : ℚ) = (a.1 : ℚ) := by
    push_cast
    ring
  rw [hshear]
  rw [Fintype.sum_eq_single a]
  · rw [Fintype.sum_eq_single b]
    · simp
    · intro b' hb'
      rw [finiteLagrangeWeight_ne b' b hb']
      ring
  · intro a' ha'
    rw [finiteLagrangeWeight_ne a' a ha']
    simp

/-- Every rational-valued function on `Γ_{A,B}` is recovered by the explicit
two-coordinate Lagrange formula.  This is the finite separation fact used
before the rank-filtration argument in `L:sheared`; it makes no weighted-rank
or determinant assertion. -/
theorem generalBidegreeGridInterpolant_eval (A B : ℕ)
    (f : generalBidegreeGrid A B → ℚ) (p : generalBidegreeGrid A B) :
    generalBidegreeGridInterpolant A B f (p.1.1 : ℚ) (p.1.2 : ℚ) = f p := by
  rcases generalBidegreeGridPoint_surjective A B p with ⟨⟨a, b⟩, rfl⟩
  simpa [generalBidegreeGridPoint] using
    generalBidegreeGridInterpolant_eval_point A B f a b

/-- In particular, distinct grid points are separated by an explicit
Lagrange formula. -/
theorem generalBidegreeGrid_separated (A B : ℕ)
    (p q : generalBidegreeGrid A B) (hpq : p ≠ q) :
    ∃ F : ℚ → ℚ → ℚ,
      F (p.1.1 : ℚ) (p.1.2 : ℚ) = 1 ∧
        F (q.1.1 : ℚ) (q.1.2 : ℚ) = 0 := by
  let f : generalBidegreeGrid A B → ℚ := fun r => if r = p then 1 else 0
  refine ⟨generalBidegreeGridInterpolant A B f, ?_, ?_⟩
  · rw [generalBidegreeGridInterpolant_eval]
    simp [f]
  · rw [generalBidegreeGridInterpolant_eval]
    have hqp : q ≠ p := Ne.symm hpq
    simp [f, hqp]

end PellPaper
