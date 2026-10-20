import Pell.QuadraticKroneckerCharacterFullQuadraticity

/-!
# Numerator-side values of the selected character at odd units

The actual dependent branch selection agrees with `J(D | n)` whenever `n`
is odd and coprime to `D`. This assembles the existing branch reciprocity
lemmas and is the value statement needed at unramified odd primes. No
primitivity, conductor or even-argument value theorem is asserted here.
-/

namespace PellPaper

open NumberTheorySymbols

noncomputable section

private theorem apply_cast_level
    {m N : ℕ} (h : m = N) (χ : DirichletCharacter ℤ m) (n : ℕ) :
    (cast (congrArg (DirichletCharacter ℤ) h) χ) n = χ n := by
  subst N
  rfl

/-- The selected character has its numerator-side Jacobi value at every odd
argument coprime to the positive fundamental discriminant. -/
theorem kroneckerCharacterAtPositiveFundamentalDiscriminant_apply_eq_jacobi_of_odd_coprime
    (D n : ℕ) (hD : PositiveFundamentalDiscriminant D)
    (hnodd : Odd n) (hn : n.Coprime D) :
    kroneckerCharacterAtPositiveFundamentalDiscriminant D hD n = J((D : ℤ) | n) := by
  classical
  unfold kroneckerCharacterAtPositiveFundamentalDiscriminant
  by_cases hodd : Squarefree D ∧ D % 4 = 1
  · rw [dif_pos hodd]
    exact @jacobiDirichletCharacter_apply_eq_jacobi_numerator_of_odd
      D n ⟨hD.1⟩ hodd.2 hnodd
  · rw [dif_neg hodd]
    rcases hD.2.resolve_left hodd with ⟨d, hD_eq, hsq, hdmod⟩
    subst D
    have hdiv : 4 * d / 4 = d := by omega
    dsimp only
    simp only [hdiv]
    by_cases hd2 : d % 4 = 2
    · by_cases hd_eq_two : d = 2
      · simp [hd_eq_two]
        rw [apply_cast_level (by omega : 8 = 4 * d)]
        exact kroneckerCharacterEight_apply_eq_jacobi_numerator_of_coprime n
          (by simpa [hd_eq_two] using hn)
      · simp [hd2, hd_eq_two]
        rw [apply_cast_level (by omega : 4 * (4 * d / 4) = 4 * d)]
        have hfactor : 2 * (d / 2) = d :=
            two_mul_div_two_of_mod_four_two d hd2
        have hlevel : 8 * (4 * d / 4 / 2) = 4 * (4 * d / 4) := by
            rw [hdiv]
            omega
        have hegt : 1 < 4 * d / 4 / 2 := by
            simpa [hdiv] using (show 1 < d / 2 by omega)
        have hncoprime : n.Coprime (8 * (4 * d / 4 / 2)) := by
            rw [hlevel, hdiv]
            exact hn
        by_cases he1 : d / 2 % 4 = 1
        · simp [he1]
          rw [apply_cast_level hlevel]
          rw [@kroneckerCharacterEightMulOne_apply_eq_jacobi_numerator_of_coprime
            (4 * d / 4 / 2) n ⟨hegt⟩ (by simpa [hdiv] using he1) hncoprime]
          congr 1
          exact_mod_cast (show 8 * (4 * d / 4 / 2) = 4 * d by omega)
        · simp [he1]
          rw [apply_cast_level hlevel]
          have he3 : d / 2 % 4 = 3 :=
                (Nat.odd_mod_four_iff.mp (div_two_odd_of_mod_four_two d hd2)).resolve_left he1
          rw [@kroneckerCharacterEightMulThree_apply_eq_jacobi_numerator_of_coprime
            (4 * d / 4 / 2) n ⟨hegt⟩ (by simpa [hdiv] using he3) hncoprime]
          congr 1
          exact_mod_cast (show 8 * (4 * d / 4 / 2) = 4 * d by omega)
    · simp [hd2]
      rw [apply_cast_level (by omega : 4 * (4 * d / 4) = 4 * d)]
      have hd3 : d % 4 = 3 := hdmod.resolve_left hd2
      have hdgt : 1 < 4 * d / 4 := by omega
      simpa only [hdiv, Nat.cast_mul, Nat.cast_ofNat] using
        (@kroneckerCharacterFourMulThree_apply_eq_jacobi_numerator_of_coprime
          (4 * d / 4) n ⟨hdgt⟩ (by simpa [hdiv] using hd3)
          (by simpa [hdiv] using hn))

end
end PellPaper
