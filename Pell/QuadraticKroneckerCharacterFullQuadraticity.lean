import Pell.QuadraticKroneckerCharacterQuadraticity

/-!
# Quadraticity of the assembled positive-fundamental-discriminant character

This isolated slice attempts to discharge the branchwise assembly proof for
`kroneckerCharacterAtPositiveFundamentalDiscriminant`.  It uses only the
already-proved local quadraticity lemmas; it does not assert primitivity,
conductor, all-integer Kronecker agreement, or an `L`-function factorization.
-/

namespace PellPaper

noncomputable section

/-- Transporting a character across an equality of levels preserves its
three-valued quadraticity. -/
theorem dirichletCharacter_isQuadratic_cast_level
    {m n : ℕ} (h : m = n) (χ : DirichletCharacter ℤ m)
    (hχ : χ.IsQuadratic) :
    (cast (congrArg (DirichletCharacter ℤ) h) χ).IsQuadratic := by
  subst n
  exact hχ

theorem kroneckerCharacterAtPositiveFundamentalDiscriminant_isQuadratic
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) :
    (kroneckerCharacterAtPositiveFundamentalDiscriminant D hD).IsQuadratic := by
  classical
  unfold kroneckerCharacterAtPositiveFundamentalDiscriminant
  by_cases hodd : Squarefree D ∧ D % 4 = 1
  · rw [dif_pos hodd]
    exact @jacobiDirichletCharacter_isQuadratic D ⟨hD.1⟩
  · rw [dif_neg hodd]
    rcases hD.2.resolve_left hodd with ⟨d, hD_eq, hsq, hdmod⟩
    subst D
    have hdiv : 4 * d / 4 = d := by omega
    dsimp only
    simp only [hdiv]
    by_cases hd2 : d % 4 = 2
    · by_cases hd_eq_two : d = 2
      · simp [hd_eq_two]
        apply dirichletCharacter_isQuadratic_cast_level
        · omega
        · exact ZMod.isQuadratic_χ₈
      · simp [hd2, hd_eq_two]
        apply dirichletCharacter_isQuadratic_cast_level
        · omega
        · have hfactor : 2 * (d / 2) = d :=
            two_mul_div_two_of_mod_four_two d hd2
          by_cases he1 : d / 2 % 4 = 1
          · simp [he1]
            apply dirichletCharacter_isQuadratic_cast_level
            · calc
                8 * (4 * d / 4 / 2) = 8 * (d / 2) := by rw [hdiv]
                _ = 4 * (2 * (d / 2)) := by ring
                _ = 4 * d := by rw [hfactor]
                _ = 4 * (4 * d / 4) := by rw [hdiv]
            · have hegt : 1 < 4 * d / 4 / 2 := by
                simpa [hdiv] using (show 1 < d / 2 by omega)
              exact @kroneckerCharacterEightMulOne_isQuadratic
                (4 * d / 4 / 2) ⟨hegt⟩
          · simp [he1]
            apply dirichletCharacter_isQuadratic_cast_level
            · calc
                8 * (4 * d / 4 / 2) = 8 * (d / 2) := by rw [hdiv]
                _ = 4 * (2 * (d / 2)) := by ring
                _ = 4 * d := by rw [hfactor]
                _ = 4 * (4 * d / 4) := by rw [hdiv]
            · have hegt : 1 < 4 * d / 4 / 2 := by
                simpa [hdiv] using (show 1 < d / 2 by omega)
              exact @kroneckerCharacterEightMulThree_isQuadratic
                (4 * d / 4 / 2) ⟨hegt⟩
    · simp [hd2]
      apply dirichletCharacter_isQuadratic_cast_level
      · omega
      · have hd3 : d % 4 = 3 := hdmod.resolve_left hd2
        have hdgt : 1 < 4 * d / 4 := by omega
        exact @kroneckerCharacterFourMulThree_isQuadratic (4 * d / 4) ⟨hdgt⟩

end

end PellPaper
