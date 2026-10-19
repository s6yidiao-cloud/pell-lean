import Pell.NonprincipalDirichletShiftedWindow

/-!
# Linear Dirichlet-character sums on shifted rectangles

If one coefficient of a linear form is a unit modulo `q`, summing first in
that coordinate turns each inner sum into a residue-shifted character
window.  The all-nonprincipal Pólya--Vinogradov bound then controls the
rectangle by the length of the other coordinate.  The public symmetric
statement bounds both side lengths by a common parameter.
-/

open scoped BigOperators

namespace PellPaper

private theorem nonprincipalDirichletCharacter_linear_rectangle_norm_le_of_isUnit_first
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (alpha beta x0 y0 : ZMod q) (L1 L2 : ℕ)
    (halpha : IsUnit alpha) :
    ‖∑ y ∈ Finset.range L2, ∑ x ∈ Finset.range L1,
        chi (alpha * ((x : ZMod q) + x0) +
          beta * ((y : ZMod q) + y0))‖ ≤
      4 * (L2 : ℝ) * Real.sqrt (q : ℝ) *
        (1 + Real.log (q : ℝ)) := by
  rcases halpha with ⟨u, rfl⟩
  let B : ℝ := 4 * Real.sqrt (q : ℝ) * (1 + Real.log (q : ℝ))
  have hinner (y : ℕ) :
      ‖∑ x ∈ Finset.range L1,
          chi ((u : ZMod q) * ((x : ZMod q) + x0) +
            beta * ((y : ZMod q) + y0))‖ ≤ B := by
    let uinv : ZMod q := (↑(u⁻¹) : ZMod q)
    let c : ZMod q := x0 + uinv * beta * ((y : ZMod q) + y0)
    have harg (x : ℕ) :
        (u : ZMod q) * ((x : ZMod q) + x0) +
            beta * ((y : ZMod q) + y0) =
          (u : ZMod q) * ((x : ZMod q) + c) := by
      dsimp [c]
      have hu : (u : ZMod q) * uinv = 1 := by
        exact Units.mul_inv u
      calc
        (u : ZMod q) * ((x : ZMod q) + x0) +
              beta * ((y : ZMod q) + y0) =
            (u : ZMod q) * ((x : ZMod q) + x0) +
              ((u : ZMod q) * uinv) *
                (beta * ((y : ZMod q) + y0)) := by rw [hu, one_mul]
        _ = (u : ZMod q) *
              ((x : ZMod q) +
                (x0 + uinv * beta * ((y : ZMod q) + y0))) := by ring
    have hsum :
        (∑ x ∈ Finset.range L1,
            chi ((u : ZMod q) * ((x : ZMod q) + x0) +
              beta * ((y : ZMod q) + y0))) =
          chi (u : ZMod q) *
            ∑ x ∈ Finset.range L1, chi ((x : ZMod q) + c) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      rw [harg x, map_mul]
    rw [hsum, norm_mul]
    have hwindow := nonprincipalDirichletCharacter_shifted_range_norm_le
      chi hchi c L1
    change _ ≤ B at hwindow
    calc
      ‖chi (u : ZMod q)‖ *
          ‖∑ x ∈ Finset.range L1, chi ((x : ZMod q) + c)‖ ≤
          1 * ‖∑ x ∈ Finset.range L1,
            chi ((x : ZMod q) + c)‖ :=
        mul_le_mul_of_nonneg_right (chi.norm_le_one _) (norm_nonneg _)
      _ ≤ 1 * B := mul_le_mul_of_nonneg_left hwindow zero_le_one
      _ = B := one_mul B
  calc
    ‖∑ y ∈ Finset.range L2, ∑ x ∈ Finset.range L1,
        chi ((u : ZMod q) * ((x : ZMod q) + x0) +
          beta * ((y : ZMod q) + y0))‖ ≤
        ∑ y ∈ Finset.range L2,
          ‖∑ x ∈ Finset.range L1,
            chi ((u : ZMod q) * ((x : ZMod q) + x0) +
              beta * ((y : ZMod q) + y0))‖ := norm_sum_le _ _
    _ ≤ ∑ _y ∈ Finset.range L2, B := by
      apply Finset.sum_le_sum
      intro y hy
      exact hinner y
    _ = 4 * (L2 : ℝ) * Real.sqrt (q : ℝ) *
        (1 + Real.log (q : ℝ)) := by
      simp [B]
      ring

/-- A nonprincipal complex Dirichlet character, evaluated on a shifted
linear form with at least one unit coefficient, has square-root cancellation
on every literal range rectangle.  Empty rectangles, long windows, and
arbitrary residue offsets are included. -/
theorem nonprincipalDirichletCharacter_linear_shifted_rectangle_norm_le
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (alpha beta x0 y0 : ZMod q) (L1 L2 S : ℕ)
    (hunit : IsUnit alpha ∨ IsUnit beta)
    (hL1 : L1 ≤ S) (hL2 : L2 ≤ S) :
    ‖∑ x ∈ Finset.range L1, ∑ y ∈ Finset.range L2,
        chi (alpha * ((x : ZMod q) + x0) +
          beta * ((y : ZMod q) + y0))‖ ≤
      4 * (S : ℝ) * Real.sqrt (q : ℝ) *
        (1 + Real.log (q : ℝ)) := by
  have hq : (1 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast (NeZero.pos q)
  have hscale :
      0 ≤ 4 * Real.sqrt (q : ℝ) * (1 + Real.log (q : ℝ)) := by
    positivity
  rcases hunit with halpha | hbeta
  · rw [Finset.sum_comm]
    calc
      ‖∑ y ∈ Finset.range L2, ∑ x ∈ Finset.range L1,
          chi (alpha * ((x : ZMod q) + x0) +
            beta * ((y : ZMod q) + y0))‖ ≤
          4 * (L2 : ℝ) * Real.sqrt (q : ℝ) *
            (1 + Real.log (q : ℝ)) :=
        nonprincipalDirichletCharacter_linear_rectangle_norm_le_of_isUnit_first
          chi hchi alpha beta x0 y0 L1 L2 halpha
      _ ≤ 4 * (S : ℝ) * Real.sqrt (q : ℝ) *
          (1 + Real.log (q : ℝ)) := by
        have hcast : (L2 : ℝ) ≤ S := by exact_mod_cast hL2
        nlinarith
  · have hbound :=
      nonprincipalDirichletCharacter_linear_rectangle_norm_le_of_isUnit_first
        chi hchi beta alpha y0 x0 L2 L1 hbeta
    calc
      ‖∑ x ∈ Finset.range L1, ∑ y ∈ Finset.range L2,
          chi (alpha * ((x : ZMod q) + x0) +
            beta * ((y : ZMod q) + y0))‖ ≤
          4 * (L1 : ℝ) * Real.sqrt (q : ℝ) *
            (1 + Real.log (q : ℝ)) := by
        simpa only [add_comm] using hbound
      _ ≤ 4 * (S : ℝ) * Real.sqrt (q : ℝ) *
          (1 + Real.log (q : ℝ)) := by
        have hcast : (L1 : ℝ) ≤ S := by exact_mod_cast hL1
        nlinarith

end PellPaper
