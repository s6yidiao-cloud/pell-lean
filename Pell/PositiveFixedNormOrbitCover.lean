import Pell.FixedNormResidueCover
import Pell.PositivePellTransform
import Pell.AuxiliaryCurveDegenerateCounting

/-!
# Positive fixed-norm solutions lie in at most four cyclic Pell orbits

The direct residue cover and positivity of real quadratic values turn full
signed-unit orbits into integer-power orbits of a fundamental Pell solution.
The final theorem applies to arbitrary sets of positive integer coordinate
pairs `(d,e)` at the four literal signed Pell differences. It does not bound
how many powers occur within a height interval.
-/

namespace PellPaper

/-- A subset of a nonzero norm level with positive real quadratic values is
covered by at most `|h|^2` cyclic orbits of a supplied fundamental solution.
Representatives lie in the original set; it need not itself be orbit-invariant. -/
theorem exists_positive_fixedNorm_pellPower_representatives
    (u v h : ℤ) (hh : h ≠ 0)
    {a : Pell.Solution₁ (u * v)} (ha : Pell.IsFundamental a)
    (S : Set (ℤ × ℤ))
    (hn : ∀ z ∈ S, v * z.2 ^ 2 - u * z.1 ^ 2 = h)
    (hpos : ∀ z ∈ S,
      0 < (v : ℝ) * z.2 + (z.1 : ℝ) * Real.sqrt ((u * v : ℤ) : ℝ)) :
    ∃ R : Finset (ℤ × ℤ), (↑R : Set (ℤ × ℤ)) ⊆ S ∧
      R.card ≤ h.natAbs ^ 2 ∧
      ∀ z ∈ S, ∃ r ∈ R, ∃ n : ℤ,
        z.2 = (a ^ n).x * r.2 + u * (a ^ n).y * r.1 ∧
        z.1 = v * (a ^ n).y * r.2 + (a ^ n).x * r.1 := by
  obtain ⟨R, hR, hcard, hcover⟩ :=
    exists_fixedNorm_pellOrbit_representatives u v h hh S hn
  refine ⟨R, hR, hcard, ?_⟩
  intro z hz
  obtain ⟨r, hr, q, hqe, hqd⟩ := hcover z hz
  obtain ⟨n, hq⟩ := exists_eq_zpow_of_positive_pell_transform
    u v r.1 r.2 z.1 z.2 ha q hqe hqd (hpos r (hR hr)) (hpos z hz)
  exact ⟨r, hr, n, by simpa [hq] using hqe, by simpa [hq] using hqd⟩

/-- For positive raw parameters and coordinates, a positive nonsquare
radicand and one of the four signed Pell differences, at most four cyclic
orbits suffice. The fundamental solution is constructed, not supplied as
an unproved arithmetic input. Coprimality and squarefreeness are unnecessary. -/
theorem exists_positive_fixedNorm_four_pellPower_orbits
    (u v h : ℤ) (hu : 0 < u) (hv : 0 < v)
    (hns : ¬ IsSquare (u * v)) (hh : IsSignedDyadicDifference h)
    (S : Set (ℤ × ℤ))
    (hn : ∀ z ∈ S, v * z.2 ^ 2 - u * z.1 ^ 2 = h)
    (hpos : ∀ z ∈ S, 0 < z.1 ∧ 0 < z.2) :
    ∃ a : Pell.Solution₁ (u * v), Pell.IsFundamental a ∧
      ∃ R : Finset (ℤ × ℤ), (↑R : Set (ℤ × ℤ)) ⊆ S ∧ R.card ≤ 4 ∧
        ∀ z ∈ S, ∃ r ∈ R, ∃ n : ℤ,
          z.2 = (a ^ n).x * r.2 + u * (a ^ n).y * r.1 ∧
          z.1 = v * (a ^ n).y * r.2 + (a ^ n).x * r.1 := by
  obtain ⟨a, ha⟩ := Pell.IsFundamental.exists_of_not_isSquare (mul_pos hu hv) hns
  have hα : ∀ z ∈ S,
      0 < (v : ℝ) * z.2 + (z.1 : ℝ) * Real.sqrt ((u * v : ℤ) : ℝ) := by
    intro z hz
    have hvR : (0 : ℝ) < v := by exact_mod_cast hv
    have hdR : (0 : ℝ) < z.1 := by exact_mod_cast (hpos z hz).1
    have heR : (0 : ℝ) < z.2 := by exact_mod_cast (hpos z hz).2
    exact add_pos_of_pos_of_nonneg (mul_pos hvR heR)
      (mul_nonneg hdR.le (Real.sqrt_nonneg _))
  obtain ⟨R, hR, hcard, hcover⟩ :=
    exists_positive_fixedNorm_pellPower_representatives u v h
      (isSignedDyadicDifference_ne_zero hh) ha S hn hα
  refine ⟨a, ha, R, hR, hcard.trans ?_, hcover⟩
  have habs := natAbs_le_two_of_isSignedDyadicDifference hh
  calc
    h.natAbs ^ 2 ≤ 2 ^ 2 := Nat.pow_le_pow_left habs 2
    _ = 4 := rfl

end PellPaper
