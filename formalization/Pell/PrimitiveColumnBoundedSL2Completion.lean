import Pell.SL2RoundedColumn
import Mathlib.Tactic

/-!
# A bounded determinant-one completion of a primitive column

An arbitrary Bezout completion of a primitive integral column can have a
large second column.  We shear that column after selecting a nonzero
coordinate of the primitive vector.  Rounding makes the corresponding
second-column entry at most half the selected first-column entry; the
determinant-one identity then bounds the remaining entry.
-/

namespace PellPaper

open scoped MatrixGroups

noncomputable section

/-- Evaluation of an integral column at one coordinate, viewed as a
real-valued additive functional. -/
private def primitiveColumnCoordinateAddHom (i : Fin 2) :
    (Fin 2 → ℤ) →+ ℝ where
  toFun x := (x i : ℝ)
  map_zero' := by simp
  map_add' x y := by simp

/-- A primitive integral column of coordinate size at most `T` has a
determinant-one completion all of whose entries have size at most `T + 1`.

The first coordinate is used for rounding when it is nonzero.  If it
vanishes, primitivity forces the second coordinate to be nonzero and the
same argument is run in the other row. -/
theorem exists_primitiveColumn_bounded_SL2_completion
    (y : Fin 2 → ℤ) (T : ℝ)
    (hprimitive : IsCoprime (y 0) (y 1))
    (hT : 1 ≤ T)
    (hy : ∀ i, |(y i : ℝ)| ≤ T) :
    ∃ G : SL(2, ℤ),
      (∀ i, G i 0 = y i) ∧
      ∀ i j, |((G i j : ℤ) : ℝ)| ≤ T + 1 := by
  obtain ⟨G₀, hG₀00, hG₀10⟩ := hprimitive.exists_SL2_col 0
  have hG₀col : ∀ i, G₀ i 0 = y i := by
    intro i
    fin_cases i
    · exact hG₀00
    · exact hG₀10
  by_cases hy₀ : y 0 = 0
  · have hy₁ : y 1 ≠ 0 := by
      intro hy₁
      rw [hy₀, hy₁] at hprimitive
      exact not_isCoprime_zero_zero hprimitive
    have hell :
        primitiveColumnCoordinateAddHom 1 (fun i ↦ G₀ i 0) ≠ 0 := by
      change ((G₀ 1 0 : ℤ) : ℝ) ≠ 0
      rw [hG₀10]
      exact_mod_cast hy₁
    obtain ⟨G, _hG, hfirst, _hsecond, hrounded⟩ :=
      exists_sl2_rounded_column G₀
        (primitiveColumnCoordinateAddHom 1) hell
    have hcol : ∀ i, G i 0 = y i := by
      intro i
      exact (congrFun hfirst i).trans (hG₀col i)
    have hrounded' : |((G 1 1 : ℤ) : ℝ)| ≤ |(y 1 : ℝ)| / 2 := by
      change |((G 1 1 : ℤ) : ℝ)| ≤ |((G₀ 1 0 : ℤ) : ℝ)| / 2 at hrounded
      simpa only [hG₀10] using hrounded
    have hselected : |((G 1 1 : ℤ) : ℝ)| ≤ T + 1 := by
      calc
        |((G 1 1 : ℤ) : ℝ)| ≤ |(y 1 : ℝ)| / 2 := hrounded'
        _ ≤ T / 2 := div_le_div_of_nonneg_right (hy 1) (by norm_num)
        _ ≤ T + 1 := by linarith
    have hdetZ : G 0 0 * G 1 1 - G 0 1 * G 1 0 = (1 : ℤ) := by
      simpa only [Matrix.det_fin_two] using G.det_coe
    have hdetR :
        ((G 0 0 : ℤ) : ℝ) * ((G 1 1 : ℤ) : ℝ) -
          ((G 0 1 : ℤ) : ℝ) * ((G 1 0 : ℤ) : ℝ) = 1 := by
      exact_mod_cast hdetZ
    rw [hcol 0, hcol 1, hy₀, Int.cast_zero, zero_mul, zero_sub] at hdetR
    have hproduct :
        ((G 0 1 : ℤ) : ℝ) * (y 1 : ℝ) = -1 := by
      linarith
    have hproductAbs :
        |((G 0 1 : ℤ) : ℝ)| * |(y 1 : ℝ)| = 1 := by
      calc
        |((G 0 1 : ℤ) : ℝ)| * |(y 1 : ℝ)| =
            |((G 0 1 : ℤ) : ℝ) * (y 1 : ℝ)| :=
          (abs_mul _ _).symm
        _ = |-1| := congrArg abs hproduct
        _ = 1 := by norm_num
    have hy₁one : (1 : ℝ) ≤ |(y 1 : ℝ)| := by
      exact_mod_cast Int.one_le_abs hy₁
    have hother : |((G 0 1 : ℤ) : ℝ)| ≤ T + 1 := by
      calc
        |((G 0 1 : ℤ) : ℝ)| =
            |((G 0 1 : ℤ) : ℝ)| * 1 := by ring
        _ ≤ |((G 0 1 : ℤ) : ℝ)| * |(y 1 : ℝ)| :=
          mul_le_mul_of_nonneg_left hy₁one (abs_nonneg _)
        _ = 1 := hproductAbs
        _ ≤ T + 1 := by linarith
    have hfirstBound : ∀ i, |((G i 0 : ℤ) : ℝ)| ≤ T + 1 := by
      intro i
      rw [hcol i]
      exact (hy i).trans (by linarith)
    refine ⟨G, hcol, ?_⟩
    intro i j
    fin_cases i <;> fin_cases j
    · exact hfirstBound 0
    · exact hother
    · exact hfirstBound 1
    · exact hselected
  · have hell :
        primitiveColumnCoordinateAddHom 0 (fun i ↦ G₀ i 0) ≠ 0 := by
      change ((G₀ 0 0 : ℤ) : ℝ) ≠ 0
      rw [hG₀00]
      exact_mod_cast hy₀
    obtain ⟨G, _hG, hfirst, _hsecond, hrounded⟩ :=
      exists_sl2_rounded_column G₀
        (primitiveColumnCoordinateAddHom 0) hell
    have hcol : ∀ i, G i 0 = y i := by
      intro i
      exact (congrFun hfirst i).trans (hG₀col i)
    have hrounded' : |((G 0 1 : ℤ) : ℝ)| ≤ |(y 0 : ℝ)| / 2 := by
      change |((G 0 1 : ℤ) : ℝ)| ≤ |((G₀ 0 0 : ℤ) : ℝ)| / 2 at hrounded
      simpa only [hG₀00] using hrounded
    have hselected : |((G 0 1 : ℤ) : ℝ)| ≤ T + 1 := by
      calc
        |((G 0 1 : ℤ) : ℝ)| ≤ |(y 0 : ℝ)| / 2 := hrounded'
        _ ≤ T / 2 := div_le_div_of_nonneg_right (hy 0) (by norm_num)
        _ ≤ T + 1 := by linarith
    have hdetZ : G 0 0 * G 1 1 - G 0 1 * G 1 0 = (1 : ℤ) := by
      simpa only [Matrix.det_fin_two] using G.det_coe
    have hdetR :
        ((G 0 0 : ℤ) : ℝ) * ((G 1 1 : ℤ) : ℝ) -
          ((G 0 1 : ℤ) : ℝ) * ((G 1 0 : ℤ) : ℝ) = 1 := by
      exact_mod_cast hdetZ
    rw [hcol 0, hcol 1] at hdetR
    have hsolve :
        (y 0 : ℝ) * ((G 1 1 : ℤ) : ℝ) =
          1 + ((G 0 1 : ℤ) : ℝ) * (y 1 : ℝ) := by
      linarith
    have hy₀pos : (0 : ℝ) < |(y 0 : ℝ)| := by
      exact abs_pos.mpr (by exact_mod_cast hy₀)
    have hy₀one : (1 : ℝ) ≤ |(y 0 : ℝ)| := by
      exact_mod_cast Int.one_le_abs hy₀
    have hotherMul :
        |(y 0 : ℝ)| * |((G 1 1 : ℤ) : ℝ)| ≤
          |(y 0 : ℝ)| * (T + 1) := by
      calc
        |(y 0 : ℝ)| * |((G 1 1 : ℤ) : ℝ)| =
            |(y 0 : ℝ) * ((G 1 1 : ℤ) : ℝ)| :=
          (abs_mul _ _).symm
        _ = |1 + ((G 0 1 : ℤ) : ℝ) * (y 1 : ℝ)| :=
          congrArg abs hsolve
        _ ≤ |(1 : ℝ)| +
            |((G 0 1 : ℤ) : ℝ) * (y 1 : ℝ)| := abs_add_le _ _
        _ = 1 + |((G 0 1 : ℤ) : ℝ)| * |(y 1 : ℝ)| := by
          rw [abs_one, abs_mul]
        _ ≤ 1 + (|(y 0 : ℝ)| / 2) * T := by
          exact add_le_add le_rfl
            (mul_le_mul hrounded' (hy 1) (abs_nonneg _)
              (div_nonneg (abs_nonneg _) (by norm_num)))
        _ ≤ |(y 0 : ℝ)| * (T + 1) := by
          have hTnonneg : (0 : ℝ) ≤ T := by linarith
          have hprodNonneg :
              0 ≤ |(y 0 : ℝ)| * T :=
            mul_nonneg (abs_nonneg _) hTnonneg
          nlinarith
    have hother : |((G 1 1 : ℤ) : ℝ)| ≤ T + 1 :=
      le_of_mul_le_mul_left hotherMul hy₀pos
    have hfirstBound : ∀ i, |((G i 0 : ℤ) : ℝ)| ≤ T + 1 := by
      intro i
      rw [hcol i]
      exact (hy i).trans (by linarith)
    refine ⟨G, hcol, ?_⟩
    intro i j
    fin_cases i <;> fin_cases j
    · exact hfirstBound 0
    · exact hselected
    · exact hfirstBound 1
    · exact hother

end

end PellPaper
