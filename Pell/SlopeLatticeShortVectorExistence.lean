import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Analysis.Real.Sqrt

/-!
# An actual nonzero short vector for the normalized slope map

For arbitrary real center `z` and positive `U,V,M`, Dirichlet approximation
produces a nonzero integer pair whose image under
`(a,b) ↦ (M*a/V-z*b/U,b/U)` has sup norm at most `sqrt(M/(U*V))`.
The bound has constant one.  No supplied lattice minimum, center cover,
curve count, or capacity estimate enters the statement.
-/

namespace PellPaper

/-- An actual nonzero integer vector satisfies the determinant-scale sup-norm
bound for the displayed normalized slope map, with constant one. -/
theorem exists_nonzero_int_slope_vector_sup_norm_le_sqrt
    (U V M z : ℝ) (hU : 0 < U) (hV : 0 < V) (hM : 0 < M) :
    ∃ a b : ℤ, (a ≠ 0 ∨ b ≠ 0) ∧
      max |M * (a : ℝ) / V - z * (b : ℝ) / U| |(b : ℝ) / U| ≤
        Real.sqrt (M / (U * V)) := by
  let q := Real.sqrt (M / (U * V))
  have hq : 0 < q := Real.sqrt_pos.mpr (by positivity)
  have hq2 : q ^ 2 = M / (U * V) := Real.sq_sqrt (by positivity)
  have hrel : M / V = U * q ^ 2 := by
    rw [hq2]
    field_simp
  by_cases hlarge : 1 ≤ U * q
  · let n : ℕ := ⌊U * q⌋₊
    have hn : 0 < n := Nat.floor_pos.mpr hlarge
    let ξ := z * V / (M * U)
    obtain ⟨a, b, hbpos, hbn, happ⟩ := Real.exists_int_int_abs_mul_sub_le ξ hn
    have hbposR : 0 < (b : ℝ) := by exact_mod_cast hbpos
    have hbnR : (b : ℝ) ≤ (n : ℝ) := by exact_mod_cast hbn
    have hnfloor : (n : ℝ) ≤ U * q := Nat.floor_le (by positivity)
    have hnupper : U * q < (n : ℝ) + 1 := Nat.lt_floor_add_one (U * q)
    refine ⟨a, b, Or.inr (ne_of_gt hbpos), max_le ?_ ?_⟩
    · have heq : M * (a : ℝ) / V - z * (b : ℝ) / U =
          (M / V) * ((a : ℝ) - (b : ℝ) * ξ) := by
        dsimp [ξ]
        field_simp
      calc
        |M * (a : ℝ) / V - z * (b : ℝ) / U| =
            (M / V) * |(b : ℝ) * ξ - (a : ℝ)| := by
          rw [heq, abs_mul, abs_of_pos (div_pos hM hV), abs_sub_comm]
        _ ≤ (M / V) * (1 / ((n : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left happ (div_nonneg hM.le hV.le)
        _ ≤ (M / V) * (1 / (U * q)) :=
          mul_le_mul_of_nonneg_left
            (one_div_le_one_div_of_le (mul_pos hU hq) hnupper.le)
            (div_nonneg hM.le hV.le)
        _ = q := by rw [hrel]; field_simp
    · rw [abs_div, abs_of_pos hbposR, abs_of_pos hU]
      exact (div_le_iff₀ hU).mpr (by nlinarith)
  · refine ⟨1, 0, Or.inl (by norm_num), ?_⟩
    have hsmall : M / V ≤ q := by nlinarith
    simpa only [Int.cast_one, Int.cast_zero, mul_one, mul_zero, zero_div,
      sub_zero, abs_of_pos (div_pos hM hV), abs_zero, max_eq_left (div_nonneg hM.le hV.le)]
      using hsmall

end PellPaper
