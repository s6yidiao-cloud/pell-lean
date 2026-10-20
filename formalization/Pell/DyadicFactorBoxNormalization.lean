import Pell.DyadicFactorScaleComparability
import Pell.FiniteCellSparsity
import Mathlib.Tactic

/-!
# Normalization supplied by a nonempty dyadic factor box

The global factor condition says that the point product `uv` lies in
`[Y, 2Y)`.  Membership of the dyadic box compares each point coordinate with
its lower endpoint.  This file records the exact endpoint consequences:

`UV < 2Y`, `Y < 4UV`, and
`DE sqrt(Y) <= (2Y)^theta`.

These are project-specific consequences of the actual finite cell, rather
than analytic black-box assumptions.  In particular, nonemptiness alone does
not imply the stronger normalization `UV <= Y` used by some downstream
endpoint-specialized estimates; the literal dyadic loss is retained here.
-/

namespace PellPaper

/-- Membership in a half-open dyadic box gives strict upper bounds by twice
each lower endpoint.  The canonical coordinate-upper-bound theorem records
the corresponding weak inequalities; strictness is useful for the exact
product normalization below. -/
theorem dyadicBox_coordinate_strict_upper_bounds
    {i : ℕ × ℕ × ℕ × ℕ} {d e u v : ℕ}
    (hbox : (d, e, u, v) ∈ dyadicBox i) :
    d < 2 * 2 ^ i.1 ∧ e < 2 * 2 ^ i.2.1 ∧
      u < 2 * 2 ^ i.2.2.1 ∧ v < 2 * 2 ^ i.2.2.2 := by
  unfold dyadicBox at hbox
  rcases Finset.mem_product.mp hbox with ⟨hd, hrest⟩
  rcases Finset.mem_product.mp hrest with ⟨he, hrest⟩
  rcases Finset.mem_product.mp hrest with ⟨hu, hv⟩
  exact ⟨by
      simpa [pow_succ, Nat.succ_eq_add_one, Nat.mul_comm] using
        (Finset.mem_Ico.mp hd).2,
    by
      simpa [pow_succ, Nat.succ_eq_add_one, Nat.mul_comm] using
        (Finset.mem_Ico.mp he).2,
    by
      simpa [pow_succ, Nat.succ_eq_add_one, Nat.mul_comm] using
        (Finset.mem_Ico.mp hu).2,
    by
      simpa [pow_succ, Nat.succ_eq_add_one, Nat.mul_comm] using
        (Finset.mem_Ico.mp hv).2⟩

/-- The exact endpoint normalization inherited from a factor tuple in a
dyadic box.  Besides the two-sided target-product comparison, the final
component transfers the global height budget from the point product `de` to
the source endpoint product `DE`. -/
theorem dyadicFactorCondition_dyadicBox_endpoint_normalization
    {theta : ℝ} {Y d e u v : ℕ} {i : ℕ × ℕ × ℕ × ℕ}
    (hcond : DyadicFactorCondition theta Y d e u v)
    (hbox : (d, e, u, v) ∈ dyadicBox i) :
    ((2 ^ i.2.2.1 : ℕ) : ℝ) * ((2 ^ i.2.2.2 : ℕ) : ℝ) <
        2 * (Y : ℝ) ∧
      (Y : ℝ) <
        4 * (((2 ^ i.2.2.1 : ℕ) : ℝ) * ((2 ^ i.2.2.2 : ℕ) : ℝ)) ∧
      (((2 ^ i.1 : ℕ) : ℝ) * ((2 ^ i.2.1 : ℕ) : ℝ)) *
          Real.sqrt (Y : ℝ) ≤ ((2 * Y : ℕ) : ℝ) ^ theta := by
  let D : ℝ := ((2 ^ i.1 : ℕ) : ℝ)
  let E : ℝ := ((2 ^ i.2.1 : ℕ) : ℝ)
  let U : ℝ := ((2 ^ i.2.2.1 : ℕ) : ℝ)
  let V : ℝ := ((2 ^ i.2.2.2 : ℕ) : ℝ)
  change U * V < 2 * (Y : ℝ) ∧
    (Y : ℝ) < 4 * (U * V) ∧
      (D * E) * Real.sqrt (Y : ℝ) ≤ ((2 * Y : ℕ) : ℝ) ^ theta
  rcases hcond with
    ⟨hd, he, hu, hv, _hdHeight, _heHeight, _huHeight, _hvHeight,
      _hsquarefreeU, _hsquarefreeV, _hcoprime, hYuv, huvY,
      _hvu, _hvSquare, _hdifference, hheight⟩
  have hlower := dyadicBox_coordinate_lower_bounds hbox
  have hupper := dyadicBox_coordinate_strict_upper_bounds hbox
  have hDle : D ≤ (d : ℝ) := by
    dsimp [D]
    exact_mod_cast hlower.1
  have hEle : E ≤ (e : ℝ) := by
    dsimp [E]
    exact_mod_cast hlower.2.1
  have hUle : U ≤ (u : ℝ) := by
    dsimp [U]
    exact_mod_cast hlower.2.2.1
  have hVle : V ≤ (v : ℝ) := by
    dsimp [V]
    exact_mod_cast hlower.2.2.2
  have huUpper : (u : ℝ) < 2 * U := by
    dsimp [U]
    exact_mod_cast hupper.2.2.1
  have hvUpper : (v : ℝ) < 2 * V := by
    dsimp [V]
    exact_mod_cast hupper.2.2.2
  have hUVle : U * V ≤ (u : ℝ) * (v : ℝ) := by
    exact mul_le_mul hUle hVle (by positivity) (by positivity)
  have huvUpper : (u : ℝ) * (v : ℝ) < 4 * (U * V) := by
    calc
      (u : ℝ) * (v : ℝ) < (2 * U) * (v : ℝ) :=
        mul_lt_mul_of_pos_right huUpper (by exact_mod_cast hv)
      _ < (2 * U) * (2 * V) :=
        mul_lt_mul_of_pos_left hvUpper (by positivity)
      _ = 4 * (U * V) := by ring
  have hDEle : D * E ≤ (d : ℝ) * (e : ℝ) := by
    exact mul_le_mul hDle hEle (by positivity) (by positivity)
  constructor
  · calc
      U * V ≤ (u : ℝ) * (v : ℝ) := hUVle
      _ < 2 * (Y : ℝ) := by exact_mod_cast huvY
  constructor
  · calc
      (Y : ℝ) ≤ (u : ℝ) * (v : ℝ) := by exact_mod_cast hYuv
      _ < 4 * (U * V) := huvUpper
  · calc
      (D * E) * Real.sqrt (Y : ℝ) ≤
          ((d : ℝ) * (e : ℝ)) * Real.sqrt (Y : ℝ) :=
        mul_le_mul_of_nonneg_right hDEle (Real.sqrt_nonneg _)
      _ = ((d * e : ℕ) : ℝ) * Real.sqrt (Y : ℝ) := by norm_num
      _ ≤ ((2 * Y : ℕ) : ℝ) ^ theta := hheight

/-- Cell membership itself supplies the endpoint normalization, with no
separate arithmetic or geometric hypothesis. -/
theorem mem_dyadicFactorBoxCell_endpoint_normalization
    {theta : ℝ} {Y : ℕ} {i : ℕ × ℕ × ℕ × ℕ}
    {p : ℕ × ℕ × ℕ × ℕ}
    (hp : p ∈ dyadicFactorBoxCell theta Y i) :
    ((2 ^ i.2.2.1 : ℕ) : ℝ) * ((2 ^ i.2.2.2 : ℕ) : ℝ) <
        2 * (Y : ℝ) ∧
      (Y : ℝ) <
        4 * (((2 ^ i.2.2.1 : ℕ) : ℝ) * ((2 ^ i.2.2.2 : ℕ) : ℝ)) ∧
      (((2 ^ i.1 : ℕ) : ℝ) * ((2 ^ i.2.1 : ℕ) : ℝ)) *
          Real.sqrt (Y : ℝ) ≤ ((2 * Y : ℕ) : ℝ) ^ theta := by
  rcases Finset.mem_inter.mp hp with ⟨hfactor, hbox⟩
  exact dyadicFactorCondition_dyadicBox_endpoint_normalization
    (mem_dyadicFactorTuples.mp hfactor) hbox

/-- A nonempty actual factor cell has endpoints normalized to the global
dyadic parameter.  This is the box-level bridge needed before applying a
balanced local estimate. -/
theorem nonempty_dyadicFactorBoxCell_endpoint_normalization
    {theta : ℝ} {Y : ℕ} {i : ℕ × ℕ × ℕ × ℕ}
    (hcell : (dyadicFactorBoxCell theta Y i).Nonempty) :
    ((2 ^ i.2.2.1 : ℕ) : ℝ) * ((2 ^ i.2.2.2 : ℕ) : ℝ) <
        2 * (Y : ℝ) ∧
      (Y : ℝ) <
        4 * (((2 ^ i.2.2.1 : ℕ) : ℝ) * ((2 ^ i.2.2.2 : ℕ) : ℝ)) ∧
      (((2 ^ i.1 : ℕ) : ℝ) * ((2 ^ i.2.1 : ℕ) : ℝ)) *
          Real.sqrt (Y : ℝ) ≤ ((2 * Y : ℕ) : ℝ) ^ theta := by
  obtain ⟨p, hp⟩ := hcell
  exact mem_dyadicFactorBoxCell_endpoint_normalization hp

end PellPaper
