import Pell.QuadraticProperFormClassWeightedBound
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Transferring a selected-L-value moment from cubic to real cutoffs

This conditional endpoint uses the literal strict real cutoff on positive
fundamental discriminants. An eventual bound with constant `65` on natural
cube cutoffs gives an eventual bound with constant `520` on all real cutoffs.
For `M = floorNat X`, the cube of `nthRoot 3 M + 1` strictly exceeds `M` and
is at most `8 * M` once `M >= 1`. Every integer discriminant below `X` is at
most `M`, so it lies below this cube, including at nonintegral real cutoffs.

The cubic second-moment estimate is an explicit hypothesis, not an asserted
analytic theorem. No nonnegativity hypothesis on the selected L-values is
needed because the summands are their real squares.
-/

namespace PellPaper

open Filter
open scoped BigOperators

/-- An eventual actual selected-L-value moment at natural cube cutoffs
implies the all-real-cutoff moment, with the explicit loss of a factor eight. -/
theorem eventually_sum_selectedKroneckerLValue_sq_le_of_cubic_bound
    (hcubic : ∀ᶠ Y : ℕ in atTop,
      (∑ D ∈ fundamentalDiscriminantsBelow ((Y : ℝ) ^ 3),
        selectedKroneckerLValue D ^ 2) ≤ 65 * (Y : ℝ) ^ 3) :
    ∀ᶠ X : ℝ in atTop,
      (∑ D ∈ fundamentalDiscriminantsBelow X,
        selectedKroneckerLValue D ^ 2) ≤ 520 * X := by
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.mp hcubic
  filter_upwards [eventually_ge_atTop ((((max Y₀ 1) ^ 3 : ℕ) : ℝ))] with X hX
  have hX0 : 0 ≤ X := (Nat.cast_nonneg _).trans hX
  let M : ℕ := ⌊X⌋₊
  let r : ℕ := Nat.nthRoot 3 M
  let Y : ℕ := r + 1
  have hfloor : (max Y₀ 1) ^ 3 ≤ M := (Nat.le_floor_iff hX0).mpr hX
  have hr : max Y₀ 1 ≤ r :=
    (Nat.le_nthRoot_iff (by decide : (3 : ℕ) ≠ 0)).mpr hfloor
  have hr1 : 1 ≤ r := (le_max_right Y₀ 1).trans hr
  have hYlarge : Y₀ ≤ Y :=
    (le_max_left Y₀ 1).trans (hr.trans (Nat.le_succ r))
  have hMcube : M < Y ^ 3 :=
    Nat.lt_pow_nthRoot_add_one (by decide : (3 : ℕ) ≠ 0) M
  have hroot : r ^ 3 ≤ M := Nat.pow_nthRoot_le (Or.inl (by decide))
  have hYroot : Y ≤ 2 * r := by dsimp only [Y]; omega
  have hcube : Y ^ 3 ≤ 8 * M := by
    calc
      Y ^ 3 ≤ (2 * r) ^ 3 := Nat.pow_le_pow_left hYroot 3
      _ = 8 * r ^ 3 := by ring
      _ ≤ 8 * M := Nat.mul_le_mul_left 8 hroot
  have hsubset : fundamentalDiscriminantsBelow X ⊆
      fundamentalDiscriminantsBelow ((Y : ℝ) ^ 3) := by
    intro D hD
    obtain ⟨hfund, hDX⟩ := mem_fundamentalDiscriminantsBelow.mp hD
    have hDM : D ≤ M := (Nat.le_floor_iff hX0).mpr hDX.le
    apply mem_fundamentalDiscriminantsBelow.mpr
    refine ⟨hfund, ?_⟩
    exact_mod_cast hDM.trans_lt hMcube
  have hcubeReal : (Y : ℝ) ^ 3 ≤ 8 * (M : ℝ) := by exact_mod_cast hcube
  have hMReal : (M : ℝ) ≤ X := Nat.floor_le hX0
  calc
    (∑ D ∈ fundamentalDiscriminantsBelow X, selectedKroneckerLValue D ^ 2) ≤
        ∑ D ∈ fundamentalDiscriminantsBelow ((Y : ℝ) ^ 3),
          selectedKroneckerLValue D ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun D _ _ ↦ sq_nonneg _)
    _ ≤ 65 * (Y : ℝ) ^ 3 := hY₀ Y hYlarge
    _ ≤ 65 * (8 * (M : ℝ)) := mul_le_mul_of_nonneg_left hcubeReal (by norm_num)
    _ ≤ 520 * X := by nlinarith

end PellPaper
