import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# A generic Jacobi-symbol Dirichlet character

This constructs the Jacobi-symbol Dirichlet character modulo an integer
`D > 1`, together with its complex-valued version. It is quadratic and
agrees with the Jacobi symbol on natural arguments.

It is only generic infrastructure: the manuscript's discriminant character
is the Kronecker symbol `(D / n)`, and for the `D = 4d` positive-fundamental
branch it need not agree with `J(n | D)`. Primitivity, a correct discriminant
character, and the factorization of the concrete quadratic field's Dedekind
zeta function remain separate work.
-/

namespace PellPaper

open NumberTheorySymbols

noncomputable section

/-- The integral-valued Dirichlet character induced by the Jacobi symbol
modulo `D`. -/
def jacobiDirichletCharacter (D : ℕ) [Fact (1 < D)] :
    DirichletCharacter ℤ D where
  toFun a := J((a.val : ℤ) | D)
  map_one' := by
    rw [ZMod.val_one]
    exact jacobiSym.one_left D
  map_mul' a b := by
    rw [ZMod.val_mul]
    calc
      J((↑(a.val * b.val % D) : ℤ) | D) = J((↑(a.val * b.val) : ℤ) | D) := by
        simpa using (jacobiSym.mod_left (↑(a.val * b.val) : ℤ) D).symm
      _ = J((a.val : ℤ) | D) * J((b.val : ℤ) | D) := by
        exact jacobiSym.mul_left (a.val : ℤ) (b.val : ℤ) D
  map_nonunit' a ha := by
    rw [jacobiSym.eq_zero_iff_not_coprime]
    rw [Int.gcd_eq_natAbs, Int.natAbs_natCast, Int.natAbs_natCast]
    intro hcoprime
    apply ha
    rw [← ZMod.natCast_zmod_val a]
    exact (ZMod.isUnit_iff_coprime a.val D).mpr hcoprime

/-- The character agrees with the Jacobi symbol on natural arguments. -/
theorem jacobiDirichletCharacter_apply_natCast (D n : ℕ) [Fact (1 < D)] :
    jacobiDirichletCharacter D (n : ZMod D) = J((n : ℤ) | D) := by
  unfold jacobiDirichletCharacter
  change J((↑((n : ZMod D).val) : ℤ) | D) = J((n : ℤ) | D)
  rw [ZMod.val_natCast]
  simpa using (jacobiSym.mod_left (n : ℤ) D).symm

/-- The Jacobi character takes only the quadratic values `0`, `1`, and
`-1`. -/
theorem jacobiDirichletCharacter_isQuadratic (D : ℕ) [Fact (1 < D)] :
    (jacobiDirichletCharacter D).IsQuadratic := by
  intro a
  exact jacobiSym.trichotomy (a.val : ℤ) D

/-- The complex-valued Jacobi character used by Mathlib's Dirichlet
`L`-function interfaces. -/
noncomputable def jacobiDirichletCharacterC (D : ℕ) [Fact (1 < D)] :
    DirichletCharacter ℂ D :=
  (jacobiDirichletCharacter D).ringHomComp (Int.castRingHom ℂ)

theorem jacobiDirichletCharacterC_apply_natCast (D n : ℕ) [Fact (1 < D)] :
    jacobiDirichletCharacterC D (n : ZMod D) = (J((n : ℤ) | D) : ℂ) := by
  rw [jacobiDirichletCharacterC, MulChar.ringHomComp_apply,
    jacobiDirichletCharacter_apply_natCast]
  rfl

theorem jacobiDirichletCharacterC_isQuadratic (D : ℕ) [Fact (1 < D)] :
    (jacobiDirichletCharacterC D).IsQuadratic :=
  (jacobiDirichletCharacter_isQuadratic D).comp (Int.castRingHom ℂ)

end

end PellPaper
