import Pell.QuadraticIdealNormAtTwo
import Pell.QuadraticKroneckerCharacterComplexQuadraticity

/-!
# The selected character at two for odd fundamental discriminants

The odd branch of the selected character is the Jacobi character. Its
value at two is the supplementary quadratic character modulo eight.
Consequently the selected complex character is one precisely when an
actual ideal of norm two exists; it is minus one precisely when none does.
-/

namespace PellPaper

open NumberTheorySymbols

noncomputable section

local instance rationalQuadraticAlgebra_atTwoCharacter_numberField_instance (D : ℤ)
    [Fact (rationalQuadraticAlgebraNoRationalRoot D)] :
    NumberField (rationalQuadraticAlgebra D) :=
  rationalQuadraticAlgebra_numberField D

private theorem odd_fundamental_branch (D : ℕ)
    (hD : PositiveFundamentalDiscriminant D) (hodd : Odd D) :
    Squarefree D ∧ D % 4 = 1 := by
  rcases hD.2 with h | ⟨d, hDd, _, _⟩
  · exact h
  · have hodd' := Nat.odd_iff.mp hodd
    omega

/-- Evaluation of the actual selected integral character at two. -/
theorem kroneckerCharacterAtPositiveFundamentalDiscriminant_apply_two_of_odd
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) (hodd : Odd D) :
    kroneckerCharacterAtPositiveFundamentalDiscriminant D hD 2 =
      if D % 8 = 1 then 1 else -1 := by
  classical
  have hbranch := odd_fundamental_branch D hD hodd
  unfold kroneckerCharacterAtPositiveFundamentalDiscriminant
  rw [dif_pos hbranch]
  have hj := @jacobiDirichletCharacter_apply_natCast D 2 ⟨hD.1⟩
  simp only [Nat.cast_ofNat] at hj
  rw [hj, jacobiSym.at_two hodd, ZMod.χ₈_nat_eq_if_mod_eight]
  have hparity := Nat.odd_iff.mp hodd
  have hseven : D % 8 ≠ 7 := by omega
  simp [show D % 2 ≠ 0 by omega, hseven]

/-- At the prime two away from the discriminant, value one detects the
actual norm-two ideal fibre. -/
theorem kroneckerCharacterC_eq_one_iff_exists_ideal_absNorm_eq_two
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) (hodd : Odd D) :
    let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
      ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
    kroneckerCharacterAtPositiveFundamentalDiscriminantC D hD 2 = 1 ↔
      ∃ I : Ideal (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))),
        Ideal.absNorm I = 2 := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  dsimp only
  have hideal := rationalQuadraticAlgebra_exists_ideal_absNorm_eq_two_iff_mod_eight_one D hD hodd
  dsimp only at hideal
  rw [hideal]
  have heval := kroneckerCharacterAtPositiveFundamentalDiscriminant_apply_two_of_odd D hD hodd
  change (kroneckerCharacterAtPositiveFundamentalDiscriminant D hD 2 : ℂ) = 1 ↔ D % 8 = 1
  rw [heval]
  split_ifs with h <;> norm_num [h]

/-- At the prime two away from the discriminant, value minus one detects
the absence of actual ideals of norm two. -/
theorem kroneckerCharacterC_eq_neg_one_iff_not_exists_ideal_absNorm_eq_two
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) (hodd : Odd D) :
    let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
      ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
    kroneckerCharacterAtPositiveFundamentalDiscriminantC D hD 2 = -1 ↔
      ¬ ∃ I : Ideal (NumberField.RingOfIntegers (rationalQuadraticAlgebra (D : ℤ))),
        Ideal.absNorm I = 2 := by
  let _ : Fact (rationalQuadraticAlgebraNoRationalRoot (D : ℤ)) :=
    ⟨rationalQuadraticAlgebraNoRationalRoot_of_positiveFundamentalDiscriminant hD⟩
  dsimp only
  have hideal := rationalQuadraticAlgebra_exists_ideal_absNorm_eq_two_iff_mod_eight_one D hD hodd
  dsimp only at hideal
  rw [hideal]
  have heval := kroneckerCharacterAtPositiveFundamentalDiscriminant_apply_two_of_odd D hD hodd
  change (kroneckerCharacterAtPositiveFundamentalDiscriminant D hD 2 : ℂ) = -1 ↔ ¬ D % 8 = 1
  rw [heval]
  split_ifs with h <;> norm_num [h]

end
end PellPaper
