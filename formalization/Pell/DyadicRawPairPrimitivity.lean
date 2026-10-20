import Pell.ShiftedSquareReduction

/-!
# Primitivity of the literal raw source and target pairs

The source gcd is not a field of the dyadic factor condition. Its square
divides the actual signed weighted difference, whose absolute value is one
or two, and therefore that gcd is one. This argument needs no positivity
or squarefreeness premise. Target primitivity is supplied by the actual
condition, with the target coordinates in the order `(v,u)`.
-/

namespace PellPaper

/-- A natural source pair is coprime whenever its integer weighted-square
difference is one of the four signed dyadic levels. No source or weight
positivity, squarefreeness, or target coprimality is required. -/
theorem source_coprime_of_signed_weighted_difference {d e u v : ℕ}
    (hh : IsSignedDyadicDifference
      ((v : ℤ) * (e : ℤ) ^ 2 - (u : ℤ) * (d : ℤ) ^ 2)) :
    d.Coprime e := by
  let g := d.gcd e
  let h := (v : ℤ) * (e : ℤ) ^ 2 - (u : ℤ) * (d : ℤ) ^ 2
  have hd : (g : ℤ) ∣ (d : ℤ) :=
    Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left d e)
  have he : (g : ℤ) ∣ (e : ℤ) :=
    Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right d e)
  have hdiv : (g : ℤ) ^ 2 ∣ h :=
    dvd_sub (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd he 2) (v : ℤ))
      (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hd 2) (u : ℤ))
  have hnat : g ^ 2 ∣ h.natAbs := by
    exact_mod_cast (Int.dvd_natAbs.mpr hdiv)
  have hpos : 0 < h.natAbs :=
    Int.natAbs_pos.mpr (isSignedDyadicDifference_ne_zero hh)
  have hsmall : h.natAbs ≤ 2 := by
    rcases hh with hh | hh | hh | hh <;> change h = _ at hh <;>
      rw [hh] <;> norm_num
  have hgsq : g ^ 2 ≤ 2 := (Nat.le_of_dvd hpos hnat).trans hsmall
  have hgzero : g ≠ 0 := by
    intro hg
    have hz : h.natAbs = 0 := by simpa [hg] using hnat
    omega
  change g = 1
  have hgle : g ≤ 1 := by nlinarith
  omega

/-- The actual dyadic factor condition supplies primitive integer source
and target vectors in the literal coordinate order `((d,e),(v,u))`. -/
theorem dyadicFactorCondition_primitive_raw_pairs
    {θ : ℝ} {Y d e u v : ℕ}
    (hc : DyadicFactorCondition θ Y d e u v) :
    IsCoprime (d : ℤ) (e : ℤ) ∧ IsCoprime (v : ℤ) (u : ℤ) := by
  have hsigned : IsSignedDyadicDifference
      ((v : ℤ) * (e : ℤ) ^ 2 - (u : ℤ) * (d : ℤ) ^ 2) :=
    isSignedDyadicDifference_of_dyadicFactorCondition hc (by ring)
  have hsource := source_coprime_of_signed_weighted_difference hsigned
  rcases hc with ⟨_, _, _, _, _, _, _, _, _, _, htarget, _⟩
  exact ⟨hsource.isCoprime, htarget.symm.isCoprime⟩

end PellPaper
