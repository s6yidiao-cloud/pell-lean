import Pell.TwoLayerFanMinimum
import Mathlib.Tactic

/-!
# Choosing the nearest admissible two-layer fan index

This module constructs the integer nearest to `q/(2m)` by a natural floor
and proves the two adjacent fan-wall inequalities.  Under the very generous
upper range `q <= 2mB`, the chosen index lies in `1,...,B`.
-/

namespace PellPaper

noncomputable section

/-- The natural nearest-integer choice for the two-layer fan. -/
def nearestTwoLayerFanIndex (m q : ℝ) : ℕ :=
  ⌊q / (2 * m) + 1 / 2⌋₊

/-- The nearest fan index lies between one and `B` and satisfies both exact
fan walls. -/
theorem nearestTwoLayerFanIndex_spec
    (B : ℕ) (m q : ℝ)
    (hm : 0 < m) (hmq : m ≤ q)
    (hqB : q ≤ 2 * m * (B : ℝ)) :
    1 ≤ nearestTwoLayerFanIndex m q ∧
      nearestTwoLayerFanIndex m q ≤ B ∧
      (2 * (nearestTwoLayerFanIndex m q : ℝ) - 1) * m ≤ q ∧
      q ≤ (2 * (nearestTwoLayerFanIndex m q : ℝ) + 1) * m := by
  let x : ℝ := q / (2 * m)
  let y : ℝ := x + 1 / 2
  let k : ℕ := ⌊y⌋₊
  have hq0 : 0 ≤ q := hm.le.trans hmq
  have hx0 : 0 ≤ x := by
    dsimp [x]
    positivity
  have hy0 : 0 ≤ y := by dsimp [y]; positivity
  have hkLower : (k : ℝ) ≤ y := by
    dsimp [k]
    exact Nat.floor_le hy0
  have hyUpper : y < (k : ℝ) + 1 := by
    dsimp [k]
    exact Nat.lt_floor_add_one y
  have hxhalf : (1 : ℝ) / 2 ≤ x := by
    dsimp [x]
    apply (le_div_iff₀ (by positivity : 0 < 2 * m)).mpr
    nlinarith
  have hkpos : 1 ≤ k := by
    dsimp [k]
    apply Nat.le_floor
    dsimp [y]
    linarith
  have hxB : x ≤ (B : ℝ) := by
    dsimp [x]
    apply (div_le_iff₀ (by positivity : 0 < 2 * m)).mpr
    nlinarith
  have hkCastUpper : (k : ℝ) < (B : ℝ) + 1 := by
    calc
      (k : ℝ) ≤ y := hkLower
      _ = x + 1 / 2 := rfl
      _ ≤ (B : ℝ) + 1 / 2 := by linarith
      _ < (B : ℝ) + 1 := by linarith
  have hkB : k ≤ B := by
    have hkNat : k < B + 1 := by exact_mod_cast hkCastUpper
    omega
  have hleftCoeff : 2 * (k : ℝ) - 1 ≤ 2 * x := by
    dsimp [y] at hkLower
    linarith
  have hleftMul : (2 * (k : ℝ) - 1) * m ≤ 2 * x * m :=
    mul_le_mul_of_nonneg_right hleftCoeff hm.le
  have hleftIdentity : 2 * x * m = q := by
    dsimp [x]
    field_simp [hm.ne']
  have hleft : (2 * (k : ℝ) - 1) * m ≤ q := by
    rw [← hleftIdentity]
    exact hleftMul
  have hrightCoeff : 2 * x < 2 * (k : ℝ) + 1 := by
    dsimp [y] at hyUpper
    linarith
  have hrightMul : 2 * x * m < (2 * (k : ℝ) + 1) * m :=
    mul_lt_mul_of_pos_right hrightCoeff hm
  have hright : q ≤ (2 * (k : ℝ) + 1) * m := by
    rw [← hleftIdentity]
    exact hrightMul.le
  simpa only [nearestTwoLayerFanIndex, k, y, x] using
    And.intro hkpos (And.intro hkB (And.intro hleft hright))

/-- The nearest-index fan walls remain valid after multiplying both weights
by a common nonnegative logarithmic scale. -/
theorem exists_twoLayerFanIndex_scaled
    (B : ℕ) (m q L : ℝ)
    (hm : 0 < m) (hL : 0 ≤ L)
    (hmq : m ≤ q) (hqB : q ≤ 2 * m * (B : ℝ)) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ B ∧
      (2 * (k : ℝ) - 1) * (m * L) ≤ q * L ∧
      q * L ≤ (2 * (k : ℝ) + 1) * (m * L) := by
  let k := nearestTwoLayerFanIndex m q
  obtain ⟨hkpos, hkB, hleft, hright⟩ :=
    nearestTwoLayerFanIndex_spec B m q hm hmq hqB
  have hleftL := mul_le_mul_of_nonneg_right hleft hL
  have hrightL := mul_le_mul_of_nonneg_right hright hL
  refine ⟨k, hkpos, hkB, ?_, ?_⟩
  · simpa only [mul_assoc] using hleftL
  · simpa only [mul_assoc] using hrightL

end

end PellPaper

