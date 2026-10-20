import Pell.Main3UnbalancedCeilingParameters
import Mathlib.Tactic

/-!
# Workspace: Main3 outer power ledger

This file isolates the elementary real-power comparisons used when the
unbalanced mesh is combined with the moving square-sieve scale.
-/

namespace PellPaper

noncomputable section

/-- A local, production-import-only ceiling estimate for the unbalanced mesh.
This is kept in the power-ledger file so the package does not depend on the
separate outer-parameter workspace. -/
theorem main3UnbalancedM_cast_le_two_mul_rpow_outerPowerLedger
    (theta : ℝ) (Y : ℕ) (htheta : 3 ≤ theta) (hY : 2 ≤ Y) :
    (main3UnbalancedM theta Y : ℝ) ≤
      2 * (Y : ℝ) ^ (1 - 1 / (8 * theta ^ 2)) := by
  let y : ℝ := Y
  let m : ℝ := main3UnbalancedMExponent theta
  let z : ℝ := y ^ m
  have hyone : 1 ≤ y := by
    dsimp [y]
    exact_mod_cast (show 1 ≤ Y by omega)
  have hm0 : 0 ≤ m := by
    dsimp [m]
    exact (by norm_num : (0 : ℝ) ≤ 71 / 72).trans
      (main3UnbalancedMExponent_mem htheta).1
  have hzone : 1 ≤ z := by
    dsimp [z]
    calc
      (1 : ℝ) = y ^ (0 : ℝ) := by simp
      _ ≤ y ^ m := Real.rpow_le_rpow_of_exponent_le hyone hm0
  have hceil : (main3UnbalancedM theta Y : ℝ) < z + 1 := by
    dsimp [z, m, main3UnbalancedM]
    exact Nat.ceil_lt_add_one (Real.rpow_nonneg (by positivity) _)
  calc
    (main3UnbalancedM theta Y : ℝ) ≤ z + 1 := hceil.le
    _ ≤ 2 * z := by linarith
    _ = 2 * (Y : ℝ) ^ (1 - 1 / (8 * theta ^ 2)) := rfl

/-- The mesh, the square-sieve scale, and the square-root reciprocal term
all fit under the common retained power `Y^(1-1/(32*theta^2))`. -/
theorem main3LargeAnalytic_outer_mesh_sieve_power_package_workspace
    (theta : ℝ) (Y : ℕ) (htheta : 3 ≤ theta) (hY : 2 ≤ Y) :
    let y : ℝ := Y
    let s : ℝ := 1 / (32 * theta ^ 2)
    let Z : ℝ := y ^ s
    let M : ℝ := main3UnbalancedM theta Y
    let Q : ℝ := y ^ (1 - s)
    M ≤ 2 * Q ∧
      M * Z ^ 2 ≤ 2 * Q ∧
      y / Z ≤ Q ∧
      Z * Real.sqrt (y * M) ≤ 2 * Q ∧
      Real.sqrt (y * M) ≤ 2 * Q ∧
      Z * Real.sqrt y ≤ Q ∧
      Real.sqrt y ≤ Q := by
  dsimp only
  let y : ℝ := Y
  let s : ℝ := 1 / (32 * theta ^ 2)
  let Z : ℝ := y ^ s
  let M : ℝ := main3UnbalancedM theta Y
  let Q : ℝ := y ^ (1 - s)
  have hypos : 0 < y := by dsimp [y]; positivity
  have hyone : 1 ≤ y := by
    dsimp [y]
    exact_mod_cast (show 1 ≤ Y by omega)
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hsQuarter : 4 * s ≤ 1 := by
    dsimp [s]
    rw [show 4 * (1 / (32 * theta ^ 2)) =
      1 / (8 * theta ^ 2) by ring]
    apply (div_le_one (by positivity : (0 : ℝ) < 8 * theta ^ 2)).2
    nlinarith [sq_nonneg (theta - 3)]
  have hsHalf : s ≤ (1 : ℝ) / 2 := by linarith
  have hsOne : s ≤ 1 := by linarith
  have hq0 : 0 ≤ 1 - s := by linarith
  have hZpos : 0 < Z := by
    dsimp [Z]
    exact Real.rpow_pos_of_pos hypos _
  have hQpos : 0 < Q := by
    dsimp [Q]
    exact Real.rpow_pos_of_pos hypos _
  have hMnonneg : 0 ≤ M := by dsimp [M]; positivity
  have hMraw : M ≤ 2 * y ^ (1 - 4 * s) := by
    have h := main3UnbalancedM_cast_le_two_mul_rpow_outerPowerLedger
      theta Y htheta hY
    have hexponent : 1 - 1 / (8 * theta ^ 2) = 1 - 4 * s := by
      dsimp [s]
      ring
    simpa only [M, y, hexponent] using h
  have hM : M ≤ 2 * Q := by
    calc
      M ≤ 2 * y ^ (1 - 4 * s) := hMraw
      _ ≤ 2 * y ^ (1 - s) := by
        gcongr
        linarith
      _ = 2 * Q := by rfl
  have hMZ : M * Z ^ 2 ≤ 2 * Q := by
    have hZsq : Z ^ 2 = y ^ (2 * s) := by
      dsimp only [Z]
      rw [← Real.rpow_mul_natCast hypos.le]
      congr 1
      norm_num
      ring
    have hpower :
        (2 * y ^ (1 - 4 * s)) * Z ^ 2 =
          2 * y ^ (1 - 2 * s) := by
      rw [hZsq]
      calc
        2 * y ^ (1 - 4 * s) * y ^ (2 * s) =
            2 * (y ^ (1 - 4 * s) * y ^ (2 * s)) := by ring
        _ = 2 * y ^ ((1 - 4 * s) + 2 * s) := by
          rw [← Real.rpow_add hypos]
        _ = 2 * y ^ (1 - 2 * s) := by
          congr 2
          ring
    calc
      M * Z ^ 2 ≤ (2 * y ^ (1 - 4 * s)) * Z ^ 2 := by gcongr
      _ = 2 * y ^ (1 - 2 * s) := hpower
      _ ≤ 2 * y ^ (1 - s) := by
        gcongr
        linarith
      _ = 2 * Q := by rfl
  have hyZ : y / Z ≤ Q := by
    calc
      y / Z = y ^ (1 - s) := by
        dsimp only [Z]
        simpa only [Real.rpow_one] using
          (Real.rpow_sub hypos (1 : ℝ) s).symm
      _ ≤ Q := le_rfl
  have hyM : y * M ≤ 2 * y ^ (2 - 4 * s) := by
    have hyPower : y * y ^ (1 - 4 * s) = y ^ (2 - 4 * s) := by
      calc
        y * y ^ (1 - 4 * s) =
            y ^ (1 : ℝ) * y ^ (1 - 4 * s) := by rw [Real.rpow_one]
        _ = y ^ ((1 : ℝ) + (1 - 4 * s)) := by
          rw [← Real.rpow_add hypos]
        _ = y ^ (2 - 4 * s) := by
          congr 1
          ring
    calc
      y * M ≤ y * (2 * y ^ (1 - 4 * s)) := by gcongr
      _ = 2 * y ^ (2 - 4 * s) := by
        rw [show y * (2 * y ^ (1 - 4 * s)) =
          2 * (y * y ^ (1 - 4 * s)) by ring, hyPower]
  have hsqrtYM : Real.sqrt (y * M) ≤
      Real.sqrt 2 * y ^ (1 - 2 * s) := by
    have hsqrtPower : Real.sqrt (y ^ (2 - 4 * s)) =
        y ^ (1 - 2 * s) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hypos.le]
      congr 1
      ring
    calc
      Real.sqrt (y * M) ≤ Real.sqrt (2 * y ^ (2 - 4 * s)) :=
        Real.sqrt_le_sqrt hyM
      _ = Real.sqrt 2 * Real.sqrt (y ^ (2 - 4 * s)) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      _ = Real.sqrt 2 * y ^ (1 - 2 * s) := by
        rw [hsqrtPower]
  have hsqrtTwo : Real.sqrt (2 : ℝ) ≤ 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hZsqrtYM : Z * Real.sqrt (y * M) ≤ 2 * Q := by
    have hpower : Z * (Real.sqrt 2 * y ^ (1 - 2 * s)) =
        Real.sqrt 2 * y ^ (1 - s) := by
      dsimp only [Z]
      calc
        y ^ s * (Real.sqrt 2 * y ^ (1 - 2 * s)) =
            Real.sqrt 2 * (y ^ s * y ^ (1 - 2 * s)) := by ring
        _ = Real.sqrt 2 * y ^ (s + (1 - 2 * s)) := by
          rw [← Real.rpow_add hypos]
        _ = Real.sqrt 2 * y ^ (1 - s) := by
          congr 2
          ring
    calc
      Z * Real.sqrt (y * M) ≤
          Z * (Real.sqrt 2 * y ^ (1 - 2 * s)) := by gcongr
      _ = Real.sqrt 2 * y ^ (1 - s) := hpower
      _ ≤ 2 * y ^ (1 - s) := by gcongr
      _ = 2 * Q := rfl
  have hsqrtYM_Q : Real.sqrt (y * M) ≤ 2 * Q := by
    calc
      Real.sqrt (y * M) ≤ Real.sqrt 2 * y ^ (1 - 2 * s) := hsqrtYM
      _ ≤ 2 * y ^ (1 - 2 * s) := by gcongr
      _ ≤ 2 * y ^ (1 - s) := by
        gcongr
        linarith
      _ = 2 * Q := rfl
  have hsqrtY : Real.sqrt y = y ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow y
  have hZsqrtY : Z * Real.sqrt y ≤ Q := by
    calc
      Z * Real.sqrt y = y ^ (s + (1 : ℝ) / 2) := by
        rw [hsqrtY]
        dsimp only [Z]
        rw [← Real.rpow_add hypos]
      _ ≤ y ^ (1 - s) := by
        apply Real.rpow_le_rpow_of_exponent_le hyone
        linarith
      _ = Q := rfl
  have hsqrtYQ : Real.sqrt y ≤ Q := by
    rw [hsqrtY]
    dsimp only [Q]
    apply Real.rpow_le_rpow_of_exponent_le hyone
    linarith
  exact ⟨hM, hMZ, hyZ, hZsqrtYM, hsqrtYM_Q, hZsqrtY, hsqrtYQ⟩

end

end PellPaper

#print axioms PellPaper.main3LargeAnalytic_outer_mesh_sieve_power_package_workspace
#print axioms PellPaper.main3UnbalancedM_cast_le_two_mul_rpow_outerPowerLedger
