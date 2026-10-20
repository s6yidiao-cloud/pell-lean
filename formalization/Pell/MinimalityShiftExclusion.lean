import Pell.ShiftedSquareReduction

/-!
# Fundamental minimality excludes the exceptional shifted square

In the odd branch of the separated Pell factorization, a value `v = 1`
would turn the original solution into the square of a strictly smaller
positive solution.  This is a statement about the *original* fundamental
solution and its un-oriented odd-branch factor data.  It is deliberately not
stated for a bare `DyadicFactorCondition`, which has forgotten that data.
-/

namespace PellPaper

/-- Odd-branch factor data with `v = 1` reconstruct the original Pell
solution as the square of the positive solution with coordinates `(e,d)`.
The hypotheses retain the original solution, its odd parity, and both
halved-factor identities. -/
theorem odd_factor_data_v_one_is_square
    {m d e u v : ℕ} (a : Pell.Solution₁ (m : ℤ))
    (hodd : Odd a.x) (hd : 0 < d) (he : 0 < e) (hu : 0 < u)
    (hminus : (a.x - 1) / 2 = (d : ℤ) ^ 2 * u)
    (hplus : (a.x + 1) / 2 = (e : ℤ) ^ 2 * v)
    (hy : a.y = 2 * (d : ℤ) * e) (huv : u * v = m) (hv : v = 1) :
    ∃ b : Pell.Solution₁ (m : ℤ), 1 < b.x ∧ 0 < b.y ∧ a = b ^ 2 := by
  have hu_eq_m : u = m := by
    rw [← huv, hv]
    simp
  have hmpos : 0 < m := by
    rw [← hu_eq_m]
    exact hu
  have hhalf := pell_half_factors_difference a
  rw [hplus, hminus, hv, hu_eq_m] at hhalf
  norm_num at hhalf
  have hpell : (e : ℤ) ^ 2 - (m : ℤ) * (d : ℤ) ^ 2 = 1 := by
    nlinarith [hhalf]
  have hmposZ : (0 : ℤ) < m := by exact_mod_cast hmpos
  have hdposZ : (0 : ℤ) < d := by exact_mod_cast hd
  have hmdsq : 0 < (m : ℤ) * (d : ℤ) ^ 2 :=
    mul_pos hmposZ (sq_pos_of_pos hdposZ)
  have hesq : (1 : ℤ) < (e : ℤ) ^ 2 := by
    nlinarith [hpell, hmdsq]
  have heposZ : (0 : ℤ) < e := by exact_mod_cast he
  have hegt : (1 : ℤ) < e := by
    by_contra h
    have hele : (e : ℤ) ≤ 1 := le_of_not_gt h
    have hbound : (e : ℤ) ^ 2 ≤ 1 := by
      have hnonneg : 0 ≤ (e : ℤ) * (1 - e) :=
        mul_nonneg heposZ.le (sub_nonneg.mpr hele)
      nlinarith
    exact (not_lt_of_ge hbound) hesq
  have hplusmul : (a.x + 1) / 2 * 2 = a.x + 1 :=
    Int.ediv_mul_cancel (even_iff_two_dvd.mp (even_add_one.mpr hodd))
  have hxplus : a.x + 1 = 2 * (e : ℤ) ^ 2 := by
    calc
      a.x + 1 = (a.x + 1) / 2 * 2 := hplusmul.symm
      _ = 2 * (e : ℤ) ^ 2 := by rw [hplus, hv]; ring
  have hx : a.x = (e : ℤ) ^ 2 + (m : ℤ) * (d : ℤ) ^ 2 := by
    nlinarith [hpell, hxplus]
  let b : Pell.Solution₁ (m : ℤ) :=
    Pell.Solution₁.mk (e : ℤ) (d : ℤ) hpell
  refine ⟨b, ?_, ?_, ?_⟩
  · simpa only [b, Pell.Solution₁.x_mk] using hegt
  · simpa only [b, Pell.Solution₁.y_mk] using hdposZ
  · apply Pell.Solution₁.ext
    · simp only [pow_two, Pell.Solution₁.x_mul, b, Pell.Solution₁.x_mk,
        Pell.Solution₁.y_mk]
      nlinarith [hx]
    · simp only [pow_two, Pell.Solution₁.y_mul, b, Pell.Solution₁.x_mk,
        Pell.Solution₁.y_mk]
      rw [hy]
      ring

/-- A fundamental odd-branch Pell solution cannot have `v = 1`: the previous
lemma would provide a smaller positive solution for the same radicand. -/
theorem odd_factor_data_v_ne_one_of_isFundamental
    {m d e u v : ℕ} (a : Pell.Solution₁ (m : ℤ))
    (ha : Pell.IsFundamental a) (hodd : Odd a.x)
    (hd : 0 < d) (he : 0 < e) (hu : 0 < u)
    (hminus : (a.x - 1) / 2 = (d : ℤ) ^ 2 * u)
    (hplus : (a.x + 1) / 2 = (e : ℤ) ^ 2 * v)
    (hy : a.y = 2 * (d : ℤ) * e) (huv : u * v = m) :
    v ≠ 1 := by
  intro hv
  obtain ⟨b, hbx, hby, hab⟩ := odd_factor_data_v_one_is_square a hodd hd he hu
    hminus hplus hy huv hv
  have hmpos : (0 : ℤ) < m := by
    have hmnat : 0 < m := by
      rw [← huv, hv]
      exact Nat.mul_pos hu (by simp)
    exact_mod_cast hmnat
  have hmulx : 0 < b.x * (b.x - 1) :=
    mul_pos (zero_lt_one.trans hbx) (sub_pos.mpr hbx)
  have hmuly : 0 < (m : ℤ) * (b.y * b.y) :=
    mul_pos hmpos (mul_pos hby hby)
  have hsq_lt : b.x < (b ^ 2).x := by
    simp only [pow_two, Pell.Solution₁.x_mul]
    nlinarith [hmulx, hmuly]
  have hmin : a.x ≤ b.x := ha.2.2 hbx
  rw [hab] at hmin
  exact (not_le_of_gt hsq_lt) hmin

/-- In the odd factorization branch, the shifted-square parameter
`shiftedSquareA 1 v = -v` cannot equal `-1` for a fundamental solution.
Unlike the generic dyadic statement, this uses the retained original solution
and factor identities to invoke fundamental minimality. -/
theorem odd_factor_data_shiftedSquareA_ne_neg_one_of_isFundamental
    {m d e u v : ℕ} (a : Pell.Solution₁ (m : ℤ))
    (ha : Pell.IsFundamental a) (hodd : Odd a.x)
    (hd : 0 < d) (he : 0 < e) (hu : 0 < u)
    (hminus : (a.x - 1) / 2 = (d : ℤ) ^ 2 * u)
    (hplus : (a.x + 1) / 2 = (e : ℤ) ^ 2 * v)
    (hy : a.y = 2 * (d : ℤ) * e) (huv : u * v = m) :
    shiftedSquareA 1 v ≠ -1 := by
  intro hshift
  have hv : v = 1 := by
    unfold shiftedSquareA at hshift
    have hvz : (v : ℤ) = 1 := by linarith
    exact_mod_cast hvz
  exact odd_factor_data_v_ne_one_of_isFundamental a ha hodd hd he hu
    hminus hplus hy huv hv

end PellPaper
