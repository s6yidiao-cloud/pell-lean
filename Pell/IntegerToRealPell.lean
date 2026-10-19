import Pell.PowerSaving

/-!
# Passing integer-cutoff bounds to the real Pell count

The count `E θ X` is defined by taking the natural floor of the real cutoff.
This module proves the final analytic bridge: an explicit power bound for the
integer count, beyond an integer threshold, gives the corresponding real-cutoff
big-O estimate.  The integer estimate remains a hypothesis to be supplied by the
counting argument.
-/

open Filter

namespace PellPaper

/-- For a nonnegative exponent, a bound for the integer count transfers without
changing its constant to every nonnegative real cutoff whose floor is in range. -/
theorem E_le_rpow_of_integer_bound {θ p C X : ℝ} {N₀ : ℕ}
    (hp : 0 ≤ p) (hC : 0 ≤ C) (hX : 0 ≤ X) (hN : (N₀ : ℝ) ≤ X)
    (hbound : ∀ N : ℕ, N₀ ≤ N → (EInt θ N : ℝ) ≤ C * (N : ℝ) ^ p) :
    E θ X ≤ C * X ^ p := by
  have hfloor : N₀ ≤ ⌊X⌋₊ := (Nat.le_floor_iff hX).2 hN
  exact (hbound ⌊X⌋₊ hfloor).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le hX) hp) hC)

/-- An explicit eventual integer-cutoff bound gives the real-cutoff big-O
estimate used in the manuscript.  The threshold and constant may depend on
parameters fixed before this theorem is applied. -/
theorem isBigO_E_rpow_of_eventual_integer_bound {θ p C : ℝ} {N₀ : ℕ}
    (hp : 0 ≤ p) (hC : 0 ≤ C)
    (hbound : ∀ N : ℕ, N₀ ≤ N → (EInt θ N : ℝ) ≤ C * (N : ℝ) ^ p) :
    Asymptotics.IsBigO atTop (E θ) (fun X : ℝ => X ^ p) := by
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop (N₀ : ℝ)] with X hX
  have hX₀ : 0 ≤ X := (Nat.cast_nonneg N₀).trans hX
  have hE : 0 ≤ E θ X := Nat.cast_nonneg _
  have hpow : 0 ≤ X ^ p := Real.rpow_nonneg hX₀ _
  simpa only [Real.norm_eq_abs, abs_of_nonneg hE, abs_of_nonneg hpow] using
    E_le_rpow_of_integer_bound hp hC hX₀ hX hbound

/-- The common special case where the integer bound holds at every cutoff. -/
theorem isBigO_E_rpow_of_integer_bound {θ p C : ℝ}
    (hp : 0 ≤ p) (hC : 0 ≤ C)
    (hbound : ∀ N : ℕ, (EInt θ N : ℝ) ≤ C * (N : ℝ) ^ p) :
    Asymptotics.IsBigO atTop (E θ) (fun X : ℝ => X ^ p) := by
  exact isBigO_E_rpow_of_eventual_integer_bound (N₀ := 0) hp hC
    (fun N _ => hbound N)

/-- The exponent in the Pell power-saving statement is nonnegative. -/
theorem pellPowerSaving_exponent_nonneg (θ ε : ℝ) (hε : 0 ≤ ε) :
    0 ≤ 1 - Delta θ + ε := by
  have hΔ := Delta_le_one_half θ
  linarith

/-- To prove the manuscript's full real-cutoff Pell theorem it suffices to
prove its explicit integer-cutoff inequalities.  This reduction supplies the
floor comparison, exponent sign, and eventual norm bound. -/
theorem pellPowerSaving_of_eventual_integer_estimates
    (hbound : ∀ θ : ℝ, 3 ≤ θ → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (EInt θ N : ℝ) ≤ C * (N : ℝ) ^ (1 - Delta θ + ε)) :
    PellPowerSaving := by
  intro θ hθ ε hε
  obtain ⟨C, hC, N₀, hN⟩ := hbound θ hθ ε hε
  exact isBigO_E_rpow_of_eventual_integer_bound
    (pellPowerSaving_exponent_nonneg θ ε hε.le) hC hN

/-- A version of the reduction for estimates valid at every integer cutoff. -/
theorem pellPowerSaving_of_integer_estimates
    (hbound : ∀ θ : ℝ, 3 ≤ θ → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
        (EInt θ N : ℝ) ≤ C * (N : ℝ) ^ (1 - Delta θ + ε)) :
    PellPowerSaving := by
  apply pellPowerSaving_of_eventual_integer_estimates
  intro θ hθ ε hε
  obtain ⟨C, hC, hN⟩ := hbound θ hθ ε hε
  exact ⟨C, hC, 0, fun N _ => hN N⟩

end PellPaper
