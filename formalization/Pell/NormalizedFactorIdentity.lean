import Pell.DyadicCountingReduction

/-!
# Normalized dyadic factor identities

The determinant argument for the fixed-height estimate studies the rational
points
`(d / e, v / u)` associated with a separated Pell factorization.  This file
records the exact normalized equation and the elementary closeness consequence
of the four possible differences.  No determinant or lattice estimate is used
here.
-/

namespace PellPaper

/-- Positivity of factor coordinates gives the nonvanishing denominators
used by the normalized coordinates. -/
theorem normalized_factor_denominators_ne_zero {e u : ℕ}
    (he : 0 < e) (hu : 0 < u) :
    (e : ℝ) ≠ 0 ∧ (u : ℝ) ≠ 0 ∧ ((e : ℝ) ^ 2 * (u : ℝ)) ≠ 0 := by
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  exact ⟨ne_of_gt heR, ne_of_gt huR,
    ne_of_gt (mul_pos (sq_pos_of_pos heR) huR)⟩

/-- A difference equation for positive factor coordinates becomes an exact
real normalized identity.  Positivity makes every displayed denominator
nonzero. -/
theorem normalized_factor_identity {d e u v : ℕ} {h : ℤ}
    (he : 0 < e) (hu : 0 < u)
    (hdiff : (e : ℤ) ^ 2 * v - (d : ℤ) ^ 2 * u = h) :
    (v : ℝ) / (u : ℝ) - ((d : ℝ) / (e : ℝ)) ^ 2 =
      (h : ℝ) / ((e : ℝ) ^ 2 * (u : ℝ)) := by
  obtain ⟨he0, hu0, _⟩ := normalized_factor_denominators_ne_zero he hu
  have hdiffR : (e : ℝ) ^ 2 * (v : ℝ) - (d : ℝ) ^ 2 * (u : ℝ) = (h : ℝ) := by
    exact_mod_cast hdiff
  field_simp [he0, hu0]
  nlinarith [hdiffR]

/-- The four alternative integral differences retained in
`DyadicFactorCondition`. -/
theorem dyadicFactorCondition_exists_difference {θ : ℝ} {Y d e u v : ℕ}
    (hcond : DyadicFactorCondition θ Y d e u v) :
    ∃ h : ℤ, (h = 1 ∨ h = -1 ∨ h = 2 ∨ h = -2) ∧
      (e : ℤ) ^ 2 * v - (d : ℤ) ^ 2 * u = h := by
  rcases hcond with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hdiff, _⟩
  rcases hdiff with hdiff | hdiff | hdiff | hdiff
  · exact ⟨1, Or.inl rfl, hdiff⟩
  · exact ⟨-1, Or.inr (Or.inl rfl), hdiff⟩
  · exact ⟨2, Or.inr (Or.inr (Or.inl rfl)), hdiff⟩
  · exact ⟨-2, Or.inr (Or.inr (Or.inr rfl)), hdiff⟩

/-- The normalized form of every tuple in the finite dyadic factor set. -/
theorem dyadicFactorCondition_normalized_factor_identity {θ : ℝ} {Y d e u v : ℕ}
    (hcond : DyadicFactorCondition θ Y d e u v) :
    ∃ h : ℤ, (h = 1 ∨ h = -1 ∨ h = 2 ∨ h = -2) ∧
      (v : ℝ) / (u : ℝ) - ((d : ℝ) / (e : ℝ)) ^ 2 =
        (h : ℝ) / ((e : ℝ) ^ 2 * (u : ℝ)) := by
  have hcond' := hcond
  rcases hcond with ⟨_, he, hu, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  obtain ⟨h, hh, hdiff⟩ := dyadicFactorCondition_exists_difference hcond'
  exact ⟨h, hh, normalized_factor_identity he hu hdiff⟩

/-- Absolute-value form of the normalized identity. -/
theorem abs_normalized_factor_identity {d e u v : ℕ} {h : ℤ}
    (he : 0 < e) (hu : 0 < u)
    (hdiff : (e : ℤ) ^ 2 * v - (d : ℤ) ^ 2 * u = h) :
    |(v : ℝ) / (u : ℝ) - ((d : ℝ) / (e : ℝ)) ^ 2| =
      |(h : ℝ)| / ((e : ℝ) ^ 2 * (u : ℝ)) := by
  rw [normalized_factor_identity he hu hdiff, abs_div]
  have hden : 0 ≤ (e : ℝ) ^ 2 * (u : ℝ) := by positivity
  rw [abs_of_nonneg hden]

/-- If the integral difference has real absolute value at most two, the
normalized point lies within `2 / u` of the parabola. -/
theorem abs_normalized_factor_deviation_le_two_div_u {d e u v : ℕ} {h : ℤ}
    (he : 0 < e) (hu : 0 < u)
    (hdiff : (e : ℤ) ^ 2 * v - (d : ℤ) ^ 2 * u = h)
    (hh : |(h : ℝ)| ≤ 2) :
    |(v : ℝ) / (u : ℝ) - ((d : ℝ) / (e : ℝ)) ^ 2| ≤ 2 / (u : ℝ) := by
  rw [abs_normalized_factor_identity he hu hdiff]
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hden : 0 < (e : ℝ) ^ 2 * (u : ℝ) :=
    mul_pos (sq_pos_of_pos heR) huR
  have hfirst : |(h : ℝ)| / ((e : ℝ) ^ 2 * (u : ℝ)) ≤
      2 / ((e : ℝ) ^ 2 * (u : ℝ)) :=
    div_le_div_of_nonneg_right hh hden.le
  have heoneNat : 1 ≤ e := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt he)
  have heone : (1 : ℝ) ≤ e := by exact_mod_cast heoneNat
  have hesq : (1 : ℝ) ≤ (e : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((e : ℝ) - 1)]
  have hden_lower : (u : ℝ) ≤ (e : ℝ) ^ 2 * (u : ℝ) := by
    calc
      (u : ℝ) = 1 * (u : ℝ) := by ring
      _ ≤ (e : ℝ) ^ 2 * (u : ℝ) := mul_le_mul_of_nonneg_right hesq huR.le
  have hsecond : 2 / ((e : ℝ) ^ 2 * (u : ℝ)) ≤ 2 / (u : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) huR hden_lower
  exact hfirst.trans hsecond

/-- The lower dyadic product bound and the orientation `v ≤ u` force the
larger squarefree coordinate to have square at least `Y`. -/
theorem dyadicFactorCondition_Y_le_u_sq {θ : ℝ} {Y d e u v : ℕ}
    (hcond : DyadicFactorCondition θ Y d e u v) : Y ≤ u ^ 2 := by
  rcases hcond with ⟨_, _, _, _, _, _, _, _, _, _, _, hprod, _, hvu, _, _, _⟩
  calc
    Y ≤ u * v := hprod
    _ ≤ u * u := Nat.mul_le_mul_left u hvu
    _ = u ^ 2 := (pow_two u).symm

/-- In particular, the real square root of the dyadic scale is no larger
than the oriented squarefree coordinate. -/
theorem dyadicFactorCondition_sqrt_scale_le_u {θ : ℝ} {Y d e u v : ℕ}
    (hcond : DyadicFactorCondition θ Y d e u v) :
    Real.sqrt (Y : ℝ) ≤ (u : ℝ) := by
  have huR : 0 ≤ (u : ℝ) := by positivity
  have hsq : (Y : ℝ) ≤ (u : ℝ) ^ 2 := by
    exact_mod_cast dyadicFactorCondition_Y_le_u_sq hcond
  exact (Real.sqrt_le_left huR).mpr hsq

/-- Every dyadic factor tuple is within `2 / √Y` of the local parabola in
the normalized coordinates.  This is the elementary geometric input before
the determinant counting estimate. -/
theorem dyadicFactorCondition_abs_normalized_factor_deviation_le_two_div_sqrt
    {θ : ℝ} {Y d e u v : ℕ} (hcond : DyadicFactorCondition θ Y d e u v) :
    |(v : ℝ) / (u : ℝ) - ((d : ℝ) / (e : ℝ)) ^ 2| ≤
      2 / Real.sqrt (Y : ℝ) := by
  have hcond' := hcond
  rcases hcond with ⟨_, he, hu, _, _, _, huY, _, _, _, _, _, _, _, _, _, _⟩
  obtain ⟨h, hh, hdiff⟩ := dyadicFactorCondition_exists_difference hcond'
  have habs : |(h : ℝ)| ≤ 2 := by
    rcases hh with rfl | rfl | rfl | rfl <;> norm_num
  have hbase := abs_normalized_factor_deviation_le_two_div_u he hu hdiff habs
  have hYpos : 0 < Y := by omega
  have hsqrtpos : 0 < Real.sqrt (Y : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hYpos)
  have hsqrtle := dyadicFactorCondition_sqrt_scale_le_u hcond'
  exact hbase.trans (div_le_div_of_nonneg_left (by norm_num) hsqrtpos hsqrtle)

end PellPaper
