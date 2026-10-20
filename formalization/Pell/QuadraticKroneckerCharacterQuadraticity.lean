import Pell.QuadraticKroneckerCharacter

/-!
# Local quadraticity lemmas and a real complex extension

This module proves quadraticity for the explicit `4d` and `8e` character
factors, and supplies the complex-valued extension of the existing dependent
branchwise character.  That extension is pointwise real; its quadraticity
and square-one conclusion remain conditional on an explicitly supplied
quadraticity proof for the full dependent branchwise selection.

It does not prove that full assembled selection is quadratic, identify the
construction with an all-integer Kronecker symbol, prove primitivity or a
conductor formula, or establish a zeta-factorization.
-/

namespace PellPaper

noncomputable section

/-- Changing the level of a quadratic integral Dirichlet character preserves
its three-valued quadraticity. -/
theorem dirichletCharacter_isQuadratic_changeLevel
    {n m : ℕ} (hm : n ∣ m) (χ : DirichletCharacter ℤ n)
    (hχ : χ.IsQuadratic) :
    (DirichletCharacter.changeLevel hm χ).IsQuadratic := by
  intro a
  by_cases ha : IsUnit a
  · rw [← ha.unit_spec,
      DirichletCharacter.changeLevel_eq_cast_of_dvd χ hm ha.unit]
    exact hχ _
  · exact Or.inl (MulChar.map_nonunit _ ha)

/-- The product of two integral quadratic Dirichlet characters at one level
is again quadratic. -/
theorem dirichletCharacter_isQuadratic_mul
    {n : ℕ} (χ ψ : DirichletCharacter ℤ n)
    (hχ : χ.IsQuadratic) (hψ : ψ.IsQuadratic) :
    (χ * ψ).IsQuadratic := by
  intro a
  rcases hχ a with hχ | hχ | hχ <;>
    rcases hψ a with hψ | hψ | hψ <;>
    simp [hχ, hψ]

/-- The `4d` branch of the Kronecker construction is quadratic. -/
theorem kroneckerCharacterFourMulThree_isQuadratic
    (d : ℕ) [Fact (1 < d)] :
    (kroneckerCharacterFourMulThree d).IsQuadratic := by
  unfold kroneckerCharacterFourMulThree
  apply dirichletCharacter_isQuadratic_mul
  · exact dirichletCharacter_isQuadratic_changeLevel _ ZMod.χ₄ ZMod.isQuadratic_χ₄
  · exact dirichletCharacter_isQuadratic_changeLevel _ (jacobiDirichletCharacter d)
      (jacobiDirichletCharacter_isQuadratic d)

/-- The generic `8e` branch of the Kronecker construction is quadratic
whenever its mod-eight factor is quadratic. -/
theorem kroneckerCharacterEightMul_isQuadratic
    (eps : DirichletCharacter ℤ 8) (e : ℕ) [Fact (1 < e)]
    (heps : eps.IsQuadratic) :
    (kroneckerCharacterEightMul eps e).IsQuadratic := by
  unfold kroneckerCharacterEightMul
  apply dirichletCharacter_isQuadratic_mul
  · exact dirichletCharacter_isQuadratic_changeLevel _ eps heps
  · exact dirichletCharacter_isQuadratic_changeLevel _ (jacobiDirichletCharacter e)
      (jacobiDirichletCharacter_isQuadratic e)

theorem kroneckerCharacterEightMulOne_isQuadratic
    (e : ℕ) [Fact (1 < e)] :
    (kroneckerCharacterEightMulOne e).IsQuadratic := by
  exact kroneckerCharacterEightMul_isQuadratic ZMod.χ₈ e ZMod.isQuadratic_χ₈

theorem kroneckerCharacterEightMulThree_isQuadratic
    (e : ℕ) [Fact (1 < e)] :
    (kroneckerCharacterEightMulThree e).IsQuadratic := by
  exact kroneckerCharacterEightMul_isQuadratic ZMod.χ₈' e ZMod.isQuadratic_χ₈'

/-- The complex-valued extension used by Dirichlet-`L` interfaces. -/
noncomputable def kroneckerCharacterAtPositiveFundamentalDiscriminantC
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) : DirichletCharacter ℂ D :=
  (kroneckerCharacterAtPositiveFundamentalDiscriminant D hD).ringHomComp
    (Int.castRingHom ℂ)

theorem kroneckerCharacterAtPositiveFundamentalDiscriminantC_isQuadratic_of_integralQuadratic
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D)
    (hχ : (kroneckerCharacterAtPositiveFundamentalDiscriminant D hD).IsQuadratic) :
    (kroneckerCharacterAtPositiveFundamentalDiscriminantC D hD).IsQuadratic := by
  exact hχ.comp (Int.castRingHom ℂ)

theorem kroneckerCharacterAtPositiveFundamentalDiscriminantC_apply_im
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) (a : ZMod D) :
    (kroneckerCharacterAtPositiveFundamentalDiscriminantC D hD a).im = 0 := by
  simp [kroneckerCharacterAtPositiveFundamentalDiscriminantC]

theorem kroneckerCharacterAtPositiveFundamentalDiscriminantC_sq_eq_one_of_integralQuadratic
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D)
    (hχ : (kroneckerCharacterAtPositiveFundamentalDiscriminant D hD).IsQuadratic) :
    kroneckerCharacterAtPositiveFundamentalDiscriminantC D hD ^ 2 = 1 := by
  exact
    (kroneckerCharacterAtPositiveFundamentalDiscriminantC_isQuadratic_of_integralQuadratic
      D hD hχ).sq_eq_one

end

end PellPaper
