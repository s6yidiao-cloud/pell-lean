import Pell.TwoLayerVanishing
import Pell.TwoLayerWeights

/-!
# The finite two-layer exponent grid

This module gives a finite-set formulation of the grid
`Γ_{1,B} = {(a + 2b, b) : a = 0,1, 0 ≤ b ≤ B}` from
`L:two-layer-fan` in `main.tex`.  It records the elementary facts that the
two displayed generators vanish on that grid, together with its exact
cardinality.  It deliberately does not assert the standard-basis
independence or the initial-ideal calculation.
-/

namespace PellPaper

open Finset

/-- The coordinate map `(a,b) ↦ (a + 2b,b)` used for the two-layer grid. -/
def twoLayerCoordinateEmbedding : ℕ × ℕ ↪ ℤ × ℤ where
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

/-- The finite two-layer grid `Γ_{1,B}`. -/
def twoLayerGrid (B : ℕ) : Finset (ℤ × ℤ) :=
  ((range 2).product (range (B + 1))).map twoLayerCoordinateEmbedding

/-- The grid has its expected `2(B+1)` distinct points. -/
theorem card_twoLayerGrid (B : ℕ) :
    (twoLayerGrid B).card = 2 * (B + 1) := by
  simp [twoLayerGrid, Finset.card_product]

/-- A coordinate pair indexed by the two allowed rows and by a permitted
vertical coordinate belongs to the grid. -/
theorem mem_twoLayerGrid (B a b : ℕ) (ha : a ≤ 1) (hb : b ≤ B) :
    (((a + 2 * b : ℕ) : ℤ), (b : ℤ)) ∈ twoLayerGrid B := by
  unfold twoLayerGrid
  apply mem_map.mpr
  refine ⟨(a, b), ?_, rfl⟩
  apply mem_product.mpr
  constructor
  · exact mem_range.mpr (Nat.lt_succ_of_le (by omega))
  · exact mem_range.mpr (Nat.lt_succ_of_le hb)

/-- Every point of the finite grid has the advertised row-and-height
description. -/
theorem mem_twoLayerGrid_iff {B : ℕ} {N₁ N₂ : ℤ} :
    (N₁, N₂) ∈ twoLayerGrid B ↔
      ∃ a b : ℕ, a ≤ 1 ∧ b ≤ B ∧
        N₁ = ((a + 2 * b : ℕ) : ℤ) ∧ N₂ = (b : ℤ) := by
  constructor
  · intro h
    unfold twoLayerGrid at h
    rcases mem_map.mp h with ⟨⟨a, b⟩, hab, hcoord⟩
    rcases Finset.mem_product.mp hab with ⟨ha, hb⟩
    have ha' : a < 2 := Finset.mem_range.mp ha
    have hb' : b < B + 1 := Finset.mem_range.mp hb
    refine ⟨a, b, by omega, by omega, ?_, ?_⟩
    · simpa [twoLayerCoordinateEmbedding] using congrArg Prod.fst hcoord.symm
    · simpa [twoLayerCoordinateEmbedding] using congrArg Prod.snd hcoord.symm
  · rintro ⟨a, b, ha, hb, rfl, rfl⟩
    exact mem_twoLayerGrid B a b ha hb

/-- A function in the two exponent variables vanishes on a finite grid when
all of its evaluations at grid points are zero. -/
def VanishesOnTwoLayerGrid (B : ℕ) (f : ℤ → ℤ → ℤ) : Prop :=
  ∀ p ∈ twoLayerGrid B, f p.1 p.2 = 0

/-- The quadratic parallel-line generator vanishes on `Γ_{1,B}`. -/
theorem twoLayerQuadratic_vanishesOn_grid (B : ℕ) :
    VanishesOnTwoLayerGrid B twoLayerQuadratic := by
  intro p hp
  rcases (mem_twoLayerGrid_iff.mp hp) with ⟨a, b, ha, _hb, hfst, hsnd⟩
  have hp' : p = (((a + 2 * b : ℕ) : ℤ), (b : ℤ)) := Prod.ext hfst hsnd
  rw [hp']
  exact twoLayerQuadratic_eval a b ha

/-- The vertical-coordinate generator vanishes on `Γ_{1,B}`. -/
theorem twoLayerVerticalVanishing_vanishesOn_grid (B : ℕ) :
    VanishesOnTwoLayerGrid B (fun _ N₂ => twoLayerVerticalVanishing B N₂) := by
  intro p hp
  rcases (mem_twoLayerGrid_iff.mp hp) with ⟨a, b, _ha, hb, hfst, hsnd⟩
  have hp' : p = (((a + 2 * b : ℕ) : ℤ), (b : ℤ)) := Prod.ext hfst hsnd
  rw [hp']
  exact twoLayerVerticalVanishing_eval B a b hb

/-- Evaluation of a monomial indexed by an exponent pair. -/
def twoLayerMonomialEval (ij : ℕ × ℕ) (p : ℤ × ℤ) : ℤ :=
  p.1 ^ ij.1 * p.2 ^ ij.2

/-- The first row of the standard basis evaluates as powers of the first
grid coordinate. -/
theorem twoLayerMonomialEval_first_row (i a b : ℕ) :
    twoLayerMonomialEval (i, 0)
      (((a + 2 * b : ℕ) : ℤ), (b : ℤ)) =
        ((a + 2 * b : ℕ) : ℤ) ^ i := by
  simp [twoLayerMonomialEval]

/-- The second row of the standard basis evaluates as the first-coordinate
power times the vertical coordinate. -/
theorem twoLayerMonomialEval_second_row (i a b : ℕ) :
    twoLayerMonomialEval (i, 1)
      (((a + 2 * b : ℕ) : ℤ), (b : ℤ)) =
        ((a + 2 * b : ℕ) : ℤ) ^ i * (b : ℤ) := by
  simp [twoLayerMonomialEval]

end PellPaper
