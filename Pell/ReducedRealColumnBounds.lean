import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Explicit coordinate bounds from reduced real columns

The columns need not be orthogonal or Euclidean-reduced. It suffices that
the first column has sup norm `mu`, one dominant coordinate of the second
column has absolute value at most `mu/2`, and `mu^2` is at most the positive
determinant. This is a real linear-algebra estimate; construction of the
columns from an integer slope lattice is a separate step.
-/

namespace PellPaper

/-- A determinant identity bounds the second coefficient of an actual
linear combination lying in a sup-norm square. No sign premise on the
radius is needed: the displayed coordinate bounds imply it. -/
theorem abs_second_coordinate_le_of_column_determinant
    (p q : Fin 2 → ℝ) (delta mu R lam eta : ℝ)
    (hdelta : 0 < delta)
    (hdet : p 0 * q 1 - p 1 * q 0 = delta)
    (hp : ∀ i, |p i| ≤ mu)
    (hx : ∀ i, |lam * p i + eta * q i| ≤ R) :
    |eta| ≤ 2 * mu * R / delta := by
  have hmu : 0 ≤ mu := (abs_nonneg (p 0)).trans (hp 0)
  have hR : 0 ≤ R := (abs_nonneg _).trans (hx 0)
  have hid : eta * delta =
      p 0 * (lam * p 1 + eta * q 1) -
        p 1 * (lam * p 0 + eta * q 0) := by
    rw [← hdet]
    ring
  apply (le_div_iff₀ hdelta).mpr
  calc
    |eta| * delta = |eta * delta| := by rw [abs_mul, abs_of_pos hdelta]
    _ = |p 0 * (lam * p 1 + eta * q 1) -
        p 1 * (lam * p 0 + eta * q 0)| := congrArg abs hid
    _ ≤ |p 0 * (lam * p 1 + eta * q 1)| +
        |p 1 * (lam * p 0 + eta * q 0)| := abs_sub _ _
    _ ≤ mu * R + mu * R := by
      simp only [abs_mul]
      exact add_le_add
        (mul_le_mul (hp 0) (hx 1) (abs_nonneg _) hmu)
        (mul_le_mul (hp 1) (hx 0) (abs_nonneg _) hmu)
    _ = 2 * mu * R := by ring

/-- Both coefficient halfwidths for a reduced pair of real columns, with
the same pair working for every actual vector and every real radius. -/
theorem abs_coordinates_le_of_reduced_columns
    (p q : Fin 2 → ℝ) (delta mu R lam eta : ℝ)
    (hdelta : 0 < delta) (hmu : 0 < mu)
    (hdet : p 0 * q 1 - p 1 * q 0 = delta)
    (hp : ∀ i, |p i| ≤ mu)
    (hdominant : ∃ i, |p i| = mu ∧ |q i| ≤ mu / 2)
    (hsq : mu ^ 2 ≤ delta)
    (hx : ∀ i, |lam * p i + eta * q i| ≤ R) :
    |lam| ≤ 2 * R / mu ∧ |eta| ≤ 2 * mu * R / delta := by
  have heta := abs_second_coordinate_le_of_column_determinant
    p q delta mu R lam eta hdelta hdet hp hx
  have hetad : |eta| * delta ≤ 2 * mu * R := (le_div_iff₀ hdelta).mp heta
  have hetam : |eta| * mu ≤ 2 * R := by
    apply (mul_le_mul_iff_of_pos_right hmu).mp
    have h := mul_le_mul_of_nonneg_left hsq (abs_nonneg eta)
    nlinarith
  obtain ⟨i, hpi, hqi⟩ := hdominant
  have hlam : |lam| * mu ≤ R + |eta| * (mu / 2) := by
    calc
      |lam| * mu = |lam * p i| := by rw [abs_mul, hpi]
      _ = |(lam * p i + eta * q i) - eta * q i| := by ring_nf
      _ ≤ |lam * p i + eta * q i| + |eta * q i| := abs_sub _ _
      _ ≤ R + |eta| * (mu / 2) := by
        rw [abs_mul]
        exact add_le_add (hx i) (mul_le_mul_of_nonneg_left hqi (abs_nonneg eta))
  exact ⟨(le_div_iff₀ hmu).mpr (by nlinarith), heta⟩

end PellPaper
