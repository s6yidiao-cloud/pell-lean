import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith

/-!
# Integer exponents in a geometric-height interval

For a positive base value and a real ratio greater than one, a finite set of
integer exponents with all geometric heights in `[L,H]` has cardinality at
most `1 + log (H/L) / log ε`. The base value cancels, so it needs no bound
in terms of the height endpoints. No orbit or Pell-specific count is asserted.
-/

namespace PellPaper

/-- The exact logarithmic span bound for any finite family of integer
exponents whose positive geometric heights lie in the closed interval
`[L,H]`. This includes negative exponents, empty families, and `L = H`. -/
theorem card_finset_zpow_height_le
    (E : Finset ℤ) (ε α L H : ℝ)
    (hε : 1 < ε) (hα : 0 < α) (hL : 0 < L) (hLH : L ≤ H)
    (hE : ∀ n ∈ E, L ≤ α * ε ^ n ∧ α * ε ^ n ≤ H) :
    (E.card : ℝ) ≤ 1 + Real.log (H / L) / Real.log ε := by
  have hεpos : 0 < ε := zero_lt_one.trans hε
  have hH : 0 < H := hL.trans_le hLH
  have hlogε : 0 < Real.log ε := Real.log_pos hε
  have hlogLH : 0 ≤ Real.log (H / L) := by
    rw [Real.log_div hH.ne' hL.ne']
    exact sub_nonneg.mpr (Real.log_le_log hL hLH)
  rcases E.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.card_empty, Nat.cast_zero]
    exact le_trans (by norm_num : (0 : ℝ) ≤ 1)
      (le_add_of_nonneg_right (div_nonneg hlogLH hlogε.le))
  · let m := E.min' hne
    let n := E.max' hne
    have hm : m ∈ E := (Finset.isLeast_min' E hne).1
    have hn : n ∈ E := (Finset.isGreatest_max' E hne).1
    have hmn : m ≤ n := (Finset.isLeast_min' E hne).2 hn
    have hsub : E ⊆ Finset.Icc m n := by
      intro k hk
      exact Finset.mem_Icc.mpr
        ⟨(Finset.isLeast_min' E hne).2 hk, (Finset.isGreatest_max' E hne).2 hk⟩
    have hcardZ : (E.card : ℤ) ≤ n + 1 - m := by
      calc
        (E.card : ℤ) ≤ ((Finset.Icc m n).card : ℤ) := by
          exact_mod_cast Finset.card_le_card hsub
        _ = n + 1 - m := Int.card_Icc_of_le m n (by linarith)
    have hcard : (E.card : ℝ) ≤ (n : ℝ) + 1 - (m : ℝ) := by
      exact_mod_cast hcardZ
    have hlow := Real.log_le_log hL (hE m hm).1
    have hupp := Real.log_le_log (mul_pos hα (zpow_pos hεpos n)) (hE n hn).2
    rw [Real.log_mul hα.ne' (zpow_pos hεpos m).ne', Real.log_zpow] at hlow
    rw [Real.log_mul hα.ne' (zpow_pos hεpos n).ne', Real.log_zpow] at hupp
    have hspan : ((n : ℝ) - (m : ℝ)) * Real.log ε ≤ Real.log (H / L) := by
      rw [Real.log_div hH.ne' hL.ne']
      linarith
    have hspan' := (le_div_iff₀ hlogε).mpr hspan
    linarith

end PellPaper
