import Pell.Definitions

/-!
# Elementary comparison of Pell solutions under square parts

This file formalizes Lemma `L:square-part-transfer` of the manuscript.  A positive
solution for the radicand `s ^ 2 * d` transports to the radicand `d` by replacing
its second coordinate `y` with `s * y`.  Minimality of the fundamental solution
then compares both coordinates, hence the corresponding real units.
-/

namespace PellPaper

/-- Transport a Pell solution for `s ^ 2 * d` to one for `d` by multiplying its
second coordinate by `s`. -/
def squarePartTransport {d : ℤ} (s : ℤ) (b : Pell.Solution₁ (s ^ 2 * d)) :
    Pell.Solution₁ d :=
  Pell.Solution₁.mk b.x (s * b.y) (by
    convert b.prop using 1
    ring)

@[simp]
theorem squarePartTransport_x {d : ℤ} (s : ℤ) (b : Pell.Solution₁ (s ^ 2 * d)) :
    (squarePartTransport s b).x = b.x :=
  rfl

@[simp]
theorem squarePartTransport_y {d : ℤ} (s : ℤ) (b : Pell.Solution₁ (s ^ 2 * d)) :
    (squarePartTransport s b).y = s * b.y :=
  rfl

/-- Transport by a nonnegative square part does not change the associated real
Pell unit. -/
theorem epsilon_squarePartTransport {d s : ℤ} (hs : 0 ≤ s)
    (b : Pell.Solution₁ (s ^ 2 * d)) :
    epsilon (squarePartTransport s b) = epsilon b := by
  have hsR : 0 ≤ (s : ℝ) := by exact_mod_cast hs
  simp only [epsilon, squarePartTransport_x, squarePartTransport_y, Int.cast_mul,
    Int.cast_pow, Real.sqrt_mul (sq_nonneg (s : ℝ)), Real.sqrt_sq hsR]
  ring

/-- The unit attached to a fundamental Pell solution is no greater than that
attached to any solution with positive coordinates.  This uses Mathlib's
minimality theorems for each coordinate. -/
theorem epsilon_le_of_isFundamental {d : ℤ} {a b : Pell.Solution₁ d}
    (ha : Pell.IsFundamental a) (hbx : 1 < b.x) (hby : 0 < b.y) :
    epsilon a ≤ epsilon b := by
  have hx : (a.x : ℝ) ≤ (b.x : ℝ) := by exact_mod_cast ha.x_le_x hbx
  have hy : (a.y : ℝ) ≤ (b.y : ℝ) := by exact_mod_cast ha.y_le_y hbx hby
  exact add_le_add hx (mul_le_mul_of_nonneg_right hy (Real.sqrt_nonneg _))

/-- A positive fundamental Pell unit is strictly larger than the square root of
its radicand. -/
theorem sqrt_lt_epsilon {d : ℤ} {a : Pell.Solution₁ d} (ha : Pell.IsFundamental a) :
    Real.sqrt (d : ℝ) < epsilon a := by
  have hx : 0 < (a.x : ℝ) := by exact_mod_cast ha.x_pos
  have hy : (1 : ℝ) ≤ (a.y : ℝ) := by exact_mod_cast ha.2.1
  calc
    Real.sqrt (d : ℝ) ≤ (a.y : ℝ) * Real.sqrt (d : ℝ) :=
      le_mul_of_one_le_left (Real.sqrt_nonneg _) hy
    _ < (a.x : ℝ) + (a.y : ℝ) * Real.sqrt (d : ℝ) := lt_add_of_pos_left _ hx
    _ = epsilon a := rfl

/-- Square-part transfer, in the stronger form allowing any positive solution
for the larger radicand, rather than requiring it to be fundamental. -/
theorem epsilon_le_square_part_solution {d s : ℤ} (hs : 0 < s)
    {a : Pell.Solution₁ d} {b : Pell.Solution₁ (s ^ 2 * d)}
    (ha : Pell.IsFundamental a) (hbx : 1 < b.x) (hby : 0 < b.y) :
    epsilon a ≤ epsilon b := by
  rw [← epsilon_squarePartTransport hs.le b]
  apply epsilon_le_of_isFundamental ha
  · simpa only [squarePartTransport_x] using hbx
  · simpa only [squarePartTransport_y] using mul_pos hs hby

/-- **Square-part transfer** (manuscript Lemma `L:square-part-transfer`): the
fundamental unit for `d` is at most the fundamental unit for `s ^ 2 * d`.

The positive nonsquare conditions on `d` follow already from `ha`; squarefreeness
is not needed for this elementary comparison. -/
theorem square_part_transfer_int {d s : ℤ} (hs : 0 < s)
    {a : Pell.Solution₁ d} {b : Pell.Solution₁ (s ^ 2 * d)}
    (ha : Pell.IsFundamental a) (hb : Pell.IsFundamental b) :
    epsilon a ≤ epsilon b :=
  epsilon_le_square_part_solution hs ha hb.1 hb.2.1

/-- The natural-number square-part formulation of manuscript
Lemma `L:square-part-transfer`. -/
theorem square_part_transfer {d : ℤ} {s : ℕ} (hs : 0 < s)
    {a : Pell.Solution₁ d} {b : Pell.Solution₁ ((s : ℤ) ^ 2 * d)}
    (ha : Pell.IsFundamental a) (hb : Pell.IsFundamental b) :
    epsilon a ≤ epsilon b :=
  square_part_transfer_int (by exact_mod_cast hs) ha hb

end PellPaper
