import Pell.PellFactorization
import Pell.SquareParts

/-!
# Separating coprime Pell factors

The two positive coprime factors in each parity branch of a squarefree Pell
solution split into a square and a squarefree factor.  Uniqueness of the
square-part decomposition identifies the product of the squarefree factors
with the original radicand.
-/

namespace PellPaper

/-- Coprime positive factors of a square times a squarefree number separate
into square parts and coprime squarefree parts.  The square roots multiply to
the given positive square root, and the squarefree parts multiply to the
given radicand. -/
theorem coprime_squarefree_factor_separation {A B m y : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hm : 0 < m) (hy : 0 < y)
    (hcop : A.Coprime B) (hsm : Squarefree m) (hprod : A * B = m * y ^ 2) :
    ∃ d e u v : ℕ,
      0 < d ∧ 0 < e ∧ 0 < u ∧ 0 < v ∧
      A = d ^ 2 * u ∧ B = e ^ 2 * v ∧
      Squarefree u ∧ Squarefree v ∧ u.Coprime v ∧
      u * v = m ∧ d * e = y := by
  obtain ⟨d, u, hd, hu, hAu, hsu⟩ := exists_square_part_decomposition hA
  obtain ⟨e, v, he, hv, hBv, hsv⟩ := exists_square_part_decomposition hB
  have hudvd : u ∣ A := hAu ▸ dvd_mul_left u (d ^ 2)
  have hvdvd : v ∣ B := hBv ▸ dvd_mul_left v (e ^ 2)
  have huv : u.Coprime v := hcop.of_dvd hudvd hvdvd
  have hsuv : Squarefree (u * v) := (Nat.squarefree_mul huv).mpr ⟨hsu, hsv⟩
  have hAB : A * B = (d * e) ^ 2 * (u * v) := by rw [hAu, hBv]; ring
  have hmy : A * B = y ^ 2 * m := by simpa only [mul_comm m] using hprod
  obtain ⟨hde, huv'⟩ := square_part_decomposition_unique
    (Nat.mul_pos hd he) (Nat.mul_pos hu hv) hy hm hAB hmy hsuv hsm
  exact ⟨d, e, u, v, hd, he, hu, hv, hAu, hBv, hsu, hsv, huv, huv', hde⟩

/-- The same factor separation for positive integer factors.  The witnesses
are natural numbers so that the later counting problem has positive integral
parameters without any sign choices. -/
theorem int_coprime_squarefree_factor_separation {A B z : ℤ} {m : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hz : 0 < z) (hm : 0 < m)
    (hcop : Int.gcd A B = 1) (hsm : Squarefree m)
    (hprod : A * B = (m : ℤ) * z ^ 2) :
    ∃ d e u v : ℕ,
      0 < d ∧ 0 < e ∧ 0 < u ∧ 0 < v ∧
      A = (d : ℤ) ^ 2 * u ∧ B = (e : ℤ) ^ 2 * v ∧
      Squarefree u ∧ Squarefree v ∧ u.Coprime v ∧
      u * v = m ∧ (d : ℤ) * e = z := by
  have hprod' : A.natAbs * B.natAbs = m * z.natAbs ^ 2 := by
    simpa only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] using
      congrArg Int.natAbs hprod
  obtain ⟨d, e, u, v, hd, he, hu, hv, hAu, hBv, hsu, hsv, huv, hmuv, hyde⟩ :=
    coprime_squarefree_factor_separation
      (Int.natAbs_pos.mpr (ne_of_gt hA)) (Int.natAbs_pos.mpr (ne_of_gt hB)) hm
      (Int.natAbs_pos.mpr (ne_of_gt hz)) hcop hsm hprod'
  refine ⟨d, e, u, v, hd, he, hu, hv, ?_, ?_, hsu, hsv, huv, hmuv, ?_⟩
  · have hh : (A.natAbs : ℤ) = (d : ℤ) ^ 2 * u := by exact_mod_cast hAu
    simpa only [Int.natCast_natAbs, abs_of_pos hA] using hh
  · have hh : (B.natAbs : ℤ) = (e : ℤ) ^ 2 * v := by exact_mod_cast hBv
    simpa only [Int.natCast_natAbs, abs_of_pos hB] using hh
  · have hh : (d : ℤ) * e = (z.natAbs : ℤ) := by exact_mod_cast hyde
    simpa only [Int.natCast_natAbs, abs_of_pos hz] using hh

/-- The even branch of the manuscript's dyadic factorization, with exact
coordinate identities and a difference of two. -/
theorem pell_factor_separation_of_even {m : ℕ} (a : Pell.Solution₁ (m : ℤ))
    (hm : 0 < m) (hsm : Squarefree m) (hx : 1 < a.x) (hy : 0 < a.y)
    (heven : Even a.x) :
    ∃ d e u v : ℕ,
      0 < d ∧ 0 < e ∧ 0 < u ∧ 0 < v ∧
      a.x - 1 = (d : ℤ) ^ 2 * u ∧ a.x + 1 = (e : ℤ) ^ 2 * v ∧
      Squarefree u ∧ Squarefree v ∧ u.Coprime v ∧ u * v = m ∧
      (e : ℤ) ^ 2 * v - (d : ℤ) ^ 2 * u = 2 ∧ a.y = (d : ℤ) * e := by
  obtain ⟨d, e, u, v, hd, he, hu, hv, hAu, hBv, hsu, hsv, huv, hmuv, hyde⟩ :=
    int_coprime_squarefree_factor_separation (by omega : 0 < a.x - 1)
      (by omega : 0 < a.x + 1) hy hm
      (pell_factors_gcd_eq_one_of_even a heven) hsm (pell_factorization a)
  refine ⟨d, e, u, v, hd, he, hu, hv, hAu, hBv, hsu, hsv, huv, hmuv, ?_, hyde.symm⟩
  rw [← hAu, ← hBv]
  ring

/-- The odd branch of the manuscript's dyadic factorization.  Halving the
consecutive Pell factors gives difference one and `y = 2de`. -/
theorem pell_factor_separation_of_odd {m : ℕ} (a : Pell.Solution₁ (m : ℤ))
    (hm : 0 < m) (hsm : Squarefree m) (hx : 1 < a.x) (hy : 0 < a.y)
    (hodd : Odd a.x) :
    ∃ d e u v : ℕ,
      0 < d ∧ 0 < e ∧ 0 < u ∧ 0 < v ∧
      (a.x - 1) / 2 = (d : ℤ) ^ 2 * u ∧ (a.x + 1) / 2 = (e : ℤ) ^ 2 * v ∧
      Squarefree u ∧ Squarefree v ∧ u.Coprime v ∧ u * v = m ∧
      (e : ℤ) ^ 2 * v - (d : ℤ) ^ 2 * u = 1 ∧ a.y = 2 * (d : ℤ) * e := by
  have hsm' : Squarefree (m : ℤ) := Int.squarefree_natCast.mpr hsm
  have hyeven := pell_even_y_of_odd_x_of_squarefree a hsm' hodd
  have hyhalf : a.y / 2 * 2 = a.y := Int.ediv_mul_cancel (even_iff_two_dvd.mp hyeven)
  have hyhalfpos : 0 < a.y / 2 := by omega
  obtain ⟨hA, hB⟩ := pell_half_factors_pos a hx hodd
  obtain ⟨d, e, u, v, hd, he, hu, hv, hAu, hBv, hsu, hsv, huv, hmuv, hyde⟩ :=
    int_coprime_squarefree_factor_separation hA hB hyhalfpos hm
      (pell_half_factors_gcd_eq_one a) hsm
      (pell_half_factorization_of_squarefree a hsm' hodd)
  refine ⟨d, e, u, v, hd, he, hu, hv, hAu, hBv, hsu, hsv, huv, hmuv, ?_, ?_⟩
  · rw [← hAu, ← hBv]
    exact pell_half_factors_difference a
  · rw [← hyde] at hyhalf
    nlinarith [hyhalf]

/-- Every positive squarefree Pell solution supplies positive coprime
squarefree factors for one of the two positive difference equations. -/
theorem pell_factor_separation {m : ℕ} (a : Pell.Solution₁ (m : ℤ))
    (hm : 0 < m) (hsm : Squarefree m) (hx : 1 < a.x) (hy : 0 < a.y) :
    ∃ (d e u v : ℕ) (h : ℤ),
      0 < d ∧ 0 < e ∧ 0 < u ∧ 0 < v ∧
      Squarefree u ∧ Squarefree v ∧ u.Coprime v ∧ u * v = m ∧
      (h = 1 ∨ h = 2) ∧ (e : ℤ) ^ 2 * v - (d : ℤ) ^ 2 * u = h ∧
      (a.y = (d : ℤ) * e ∨ a.y = 2 * (d : ℤ) * e) := by
  rcases Int.even_or_odd a.x with heven | hodd
  · obtain ⟨d, e, u, v, hd, he, hu, hv, _, _, hsu, hsv, huv, hmuv, hdiff, hyde⟩ :=
      pell_factor_separation_of_even a hm hsm hx hy heven
    exact ⟨d, e, u, v, 2, hd, he, hu, hv, hsu, hsv, huv, hmuv, Or.inr rfl,
      hdiff, Or.inl hyde⟩
  · obtain ⟨d, e, u, v, hd, he, hu, hv, _, _, hsu, hsv, huv, hmuv, hdiff, hyde⟩ :=
      pell_factor_separation_of_odd a hm hsm hx hy hodd
    exact ⟨d, e, u, v, 1, hd, he, hu, hv, hsu, hsv, huv, hmuv, Or.inl rfl,
      hdiff, Or.inr hyde⟩

/-- The factors can be oriented with the smaller squarefree factor on the
`v` side.  Exchanging the two sides accounts for the negative differences
in the manuscript's four equations. -/
theorem pell_factor_separation_oriented {m : ℕ} (a : Pell.Solution₁ (m : ℤ))
    (hm : 0 < m) (hsm : Squarefree m) (hx : 1 < a.x) (hy : 0 < a.y) :
    ∃ (d e u v : ℕ) (h : ℤ),
      0 < d ∧ 0 < e ∧ 0 < u ∧ 0 < v ∧
      Squarefree u ∧ Squarefree v ∧ u.Coprime v ∧ u * v = m ∧ v ≤ u ∧
      (h = 1 ∨ h = -1 ∨ h = 2 ∨ h = -2) ∧
      (e : ℤ) ^ 2 * v - (d : ℤ) ^ 2 * u = h ∧
      (a.y = (d : ℤ) * e ∨ a.y = 2 * (d : ℤ) * e) := by
  obtain ⟨d, e, u, v, h, hd, he, hu, hv, hsu, hsv, huv, hmuv, hh, hdiff, hyde⟩ :=
    pell_factor_separation a hm hsm hx hy
  rcases le_total v u with hvu | huv'
  · refine ⟨d, e, u, v, h, hd, he, hu, hv, hsu, hsv, huv, hmuv, hvu, ?_, hdiff, hyde⟩
    rcases hh with hh | hh
    · exact Or.inl hh
    · exact Or.inr (Or.inr (Or.inl hh))
  · refine ⟨e, d, v, u, -h, he, hd, hv, hu, hsv, hsu, huv.symm,
      by simpa only [mul_comm] using hmuv, huv', ?_, ?_, ?_⟩
    · rcases hh with rfl | rfl <;> norm_num
    · linarith [hdiff]
    · simpa only [mul_comm (d : ℤ) (e : ℤ), mul_assoc, mul_left_comm (d : ℤ)] using hyde

end PellPaper
