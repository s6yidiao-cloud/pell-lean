import Pell.TwoLayerWeights

/-!
# The elementary vanishing relation for the two-layer grid

The determinant calculation in `main.tex` uses the exponent grid
`(N₁, N₂) = (a + 2b, b)`.  Its parallel-line relation is elementary but is
the source of the rank defect used by the two-layer argument.  This module
records that relation over the integers, without asserting any determinant
or rank estimate.
-/

namespace PellPaper

open Finset

/-- The polynomial in the two exponent variables which vanishes on the
parallel lines `N₁ - 2 N₂ = 0, …, A`.  It is represented by its integer
evaluation, which is all that is needed for the elementary grid relation. -/
def twoLayerVanishing (A : ℕ) (N₁ N₂ : ℤ) : ℤ :=
  ∏ a ∈ range (A + 1), (N₁ - 2 * N₂ - a)

/-- The two-layer grid point indexed by `(a,b)` lies on the `a`-th parallel
line and hence is a zero of `twoLayerVanishing`. -/
theorem twoLayerVanishing_eval (A a b : ℕ) (ha : a ≤ A) :
    twoLayerVanishing A ((a + 2 * b : ℕ) : ℤ) (b : ℤ) = 0 := by
  unfold twoLayerVanishing
  apply Finset.prod_eq_zero (i := a) (f := fun i : ℕ =>
    ((a + 2 * b : ℕ) : ℤ) - 2 * (b : ℤ) - i)
  · exact mem_range.mpr (Nat.lt_succ_of_le ha)
  · push_cast
    ring

/-- Translating a pair of exponent variables in the direction `(2,1)` leaves
the defining parallel-line polynomial unchanged. -/
theorem twoLayerVanishing_translate (A : ℕ) (N₁ N₂ t : ℤ) :
    twoLayerVanishing A (N₁ + 2 * t) (N₂ + t) =
      twoLayerVanishing A N₁ N₂ := by
  unfold twoLayerVanishing
  apply Finset.prod_congr rfl
  intro a ha
  ring

/-- A more invariant form of the grid vanishing: whenever the difference
`N₁ - 2N₂` is an integer in the allowed row range, the evaluation vanishes. -/
theorem twoLayerVanishing_of_difference (A : ℕ) (N₁ N₂ : ℤ) {a : ℕ}
    (ha : a ≤ A) (hdiff : N₁ - 2 * N₂ = a) :
    twoLayerVanishing A N₁ N₂ = 0 := by
  unfold twoLayerVanishing
  apply Finset.prod_eq_zero (i := a) (f := fun i : ℕ => N₁ - 2 * N₂ - i)
  · exact mem_range.mpr (Nat.lt_succ_of_le ha)
  · rw [hdiff]
    norm_num

/-- The quadratic generator of the vanishing ideal of the two-layer grid
`Γ_{1,B}`.  It is the product of the two parallel-line equations. -/
def twoLayerQuadratic (N₁ N₂ : ℤ) : ℤ :=
  (N₁ - 2 * N₂) * (N₁ - 2 * N₂ - 1)

/-- Expanded form of the quadratic generator.  In particular its leading
degree-two contribution contains the `N₂²` term used in the two-layer fan. -/
theorem twoLayerQuadratic_expand (N₁ N₂ : ℤ) :
    twoLayerQuadratic N₁ N₂ =
      N₁ ^ 2 - 4 * N₁ * N₂ + 4 * N₂ ^ 2 - N₁ + 2 * N₂ := by
  unfold twoLayerQuadratic
  ring

/-- The quadratic generator vanishes at every point in either layer of the
two-layer grid. -/
theorem twoLayerQuadratic_eval (a b : ℕ) (ha : a ≤ 1) :
    twoLayerQuadratic ((a + 2 * b : ℕ) : ℤ) (b : ℤ) = 0 := by
  unfold twoLayerQuadratic
  interval_cases a <;> push_cast <;> ring

/-- The second generator of the vanishing ideal: it vanishes on every target
coordinate `N₂ = 0, …, B`. -/
def twoLayerVerticalVanishing (B : ℕ) (N₂ : ℤ) : ℤ :=
  ∏ b ∈ range (B + 1), (N₂ - b)

/-- The vertical generator vanishes at a grid point whose second coordinate
is in the permitted range. -/
theorem twoLayerVerticalVanishing_eval (B _a b : ℕ) (hb : b ≤ B) :
    twoLayerVerticalVanishing B (b : ℤ) = 0 := by
  unfold twoLayerVerticalVanishing
  apply Finset.prod_eq_zero (i := b) (f := fun j : ℕ => (b : ℤ) - j)
  · exact mem_range.mpr (Nat.lt_succ_of_le hb)
  · norm_num

end PellPaper
