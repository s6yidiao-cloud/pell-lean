import Pell.QuadraticKroneckerCharacterOddValues

/-!
# The selected character at all odd natural arguments

The existing numerator-side Jacobi identity at odd units extends to odd
nonunits because both characters vanish there.  No conductor or primitivity
claim is used.  The complex-valued statement is the literal scalar extension
of the already selected integral character.
-/

namespace PellPaper

open NumberTheorySymbols

noncomputable section

/-- The numerator-side Jacobi formula for every odd natural argument,
including arguments not coprime to the discriminant. -/
theorem kroneckerCharacterAtPositiveFundamentalDiscriminant_apply_eq_jacobi_of_odd
    (D n : ℕ) (hD : PositiveFundamentalDiscriminant D) (hnodd : Odd n) :
    kroneckerCharacterAtPositiveFundamentalDiscriminant D hD n = J((D : ℤ) | n) := by
  by_cases hn : n.Coprime D
  · exact kroneckerCharacterAtPositiveFundamentalDiscriminant_apply_eq_jacobi_of_odd_coprime
      D n hD hnodd hn
  · have hleft : kroneckerCharacterAtPositiveFundamentalDiscriminant D hD n = 0 := by
      apply MulChar.map_nonunit
      simpa only [ZMod.isUnit_iff_coprime] using hn
    have hright : J((D : ℤ) | n) = 0 := by
      apply jacobiSym.eq_zero_iff.mpr
      refine ⟨by obtain ⟨k, hk⟩ := hnodd; omega, ?_⟩
      simpa only [Int.gcd_natCast_natCast, Nat.gcd_comm, Nat.Coprime] using hn
    exact hleft.trans hright.symm

/-- The complex extension has the same all-odd Jacobi values. -/
theorem kroneckerCharacterAtPositiveFundamentalDiscriminantC_apply_eq_jacobi_of_odd
    (D n : ℕ) (hD : PositiveFundamentalDiscriminant D) (hnodd : Odd n) :
    kroneckerCharacterAtPositiveFundamentalDiscriminantC D hD n =
      (J((D : ℤ) | n) : ℂ) := by
  change (kroneckerCharacterAtPositiveFundamentalDiscriminant D hD n : ℂ) = _
  rw [kroneckerCharacterAtPositiveFundamentalDiscriminant_apply_eq_jacobi_of_odd D n hD hnodd]

end
end PellPaper
