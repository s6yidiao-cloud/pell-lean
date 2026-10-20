import Pell.QuadraticDirichletCharacter
import Pell.FundamentalDiscriminantPellBridge
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LegendreSymbol.ZModChar

/-!
# Scratch construction of even discriminant quadratic characters

This file isolates the local character factors needed for the Kronecker
character of a positive fundamental discriminant.  It deliberately contains
no statement about primitivity, Dedekind zeta functions, or class numbers.
-/

namespace PellPaper

open NumberTheorySymbols

noncomputable section

/-- In the odd fundamental-discriminant branch, quadratic reciprocity turns
the existing denominator-side Jacobi character into the numerator-side value
on every odd argument. -/
theorem jacobiDirichletCharacter_apply_eq_jacobi_numerator_of_odd
    (D n : ℕ) [Fact (1 < D)] (hD : D % 4 = 1) (hnodd : Odd n) :
    jacobiDirichletCharacter D (n : ZMod D) = J((D : ℤ) | n) := by
  rw [jacobiDirichletCharacter_apply_natCast]
  exact (jacobiSym.quadratic_reciprocity_one_mod_four hD hnodd).symm

/-- The `4d` character for the branch `d ≡ 3 (mod 4)`: the sign factor
`χ₄` corrects the direction of quadratic reciprocity. -/
def kroneckerCharacterFourMulThree (d : ℕ) [Fact (1 < d)] :
    DirichletCharacter ℤ (4 * d) :=
  (DirichletCharacter.changeLevel (Nat.dvd_mul_right 4 d) ZMod.χ₄) *
    (DirichletCharacter.changeLevel (Nat.dvd_mul_left d 4)
      (jacobiDirichletCharacter d))

/-- The reciprocity sign in the `3 (mod 4)` branch is exactly `χ₄`. -/
theorem jacobi_numerator_eq_chiFour_mul_jacobi_denominator_of_mod_four_three
    (d n : ℕ) (hd : d % 4 = 3) (hnodd : Odd n) :
    J((d : ℤ) | n) = ZMod.χ₄ (n : ZMod 4) * J((n : ℤ) | d) := by
  have hdodd : d % 2 = 1 := Nat.odd_of_mod_four_eq_three hd
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hnodd) with hn1 | hn3
  · rw [ZMod.χ₄_nat_one_mod_four hn1]
    simpa [hd, hn1] using
      (jacobiSym.quadratic_reciprocity_if hdodd (Nat.odd_iff.mp hnodd)).symm
  · rw [ZMod.χ₄_nat_three_mod_four hn3]
    simpa [hd, hn3] using
      (jacobiSym.quadratic_reciprocity_if hdodd (Nat.odd_iff.mp hnodd)).symm

/-- The numerator-side Jacobi value of `8` on an odd denominator is `χ₈`. -/
theorem jacobi_eight_numerator_of_odd (n : ℕ) (hnodd : Odd n) :
    J((8 : ℤ) | n) = ZMod.χ₈ (n : ZMod 8) := by
  calc
    J((8 : ℤ) | n) = J((2 : ℤ) | n) * J((4 : ℤ) | n) := by
      simpa using (jacobiSym.mul_left (2 : ℤ) (4 : ℤ) n)
    _ = ZMod.χ₈ (n : ZMod 8) := by
      rw [jacobiSym.at_two hnodd, jacobiSym.at_four hnodd, mul_one]

/-- The exceptional `D = 8` member of the `4d`, `d ≡ 2 (mod 4)` branch. -/
def kroneckerCharacterEight : DirichletCharacter ℤ 8 := ZMod.χ₈

/-- The `D = 8` character has the numerator-side Jacobi value on units. -/
theorem kroneckerCharacterEight_apply_eq_jacobi_numerator_of_coprime
    (n : ℕ) (hn : n.Coprime 8) :
    kroneckerCharacterEight (n : ZMod 8) = J((8 : ℤ) | n) := by
  unfold kroneckerCharacterEight
  exact (jacobi_eight_numerator_of_odd n
    ((hn.of_dvd_right (by norm_num : 2 ∣ 8)).odd_of_right)).symm

/-- A `2 (mod 4)` integer is twice an odd integer. -/
theorem div_two_odd_of_mod_four_two (d : ℕ) (hd : d % 4 = 2) :
    (d / 2) % 2 = 1 := by
  omega

/-- The exact factorization of the `2 (mod 4)` branch. -/
theorem two_mul_div_two_of_mod_four_two (d : ℕ) (hd : d % 4 = 2) :
    2 * (d / 2) = d := by
  omega

/-- On units modulo `4d`, the two lifted factors evaluate to their expected
modulo-four and Jacobi values. -/
theorem kroneckerCharacterFourMulThree_apply_of_coprime
    (d n : ℕ) [Fact (1 < d)] (hn : n.Coprime (4 * d)) :
    kroneckerCharacterFourMulThree d (n : ZMod (4 * d)) =
      ZMod.χ₄ (n : ZMod 4) * J((n : ℤ) | d) := by
  unfold kroneckerCharacterFourMulThree
  have hfour := DirichletCharacter.changeLevel_eq_cast_of_dvd ZMod.χ₄
    (Nat.dvd_mul_right 4 d) (ZMod.unitOfCoprime n hn)
  have hd := DirichletCharacter.changeLevel_eq_cast_of_dvd
    (jacobiDirichletCharacter d) (Nat.dvd_mul_left d 4)
      (ZMod.unitOfCoprime n hn)
  simp only [ZMod.coe_unitOfCoprime] at hfour hd
  have hfour' :
      (DirichletCharacter.changeLevel (Nat.dvd_mul_right 4 d) ZMod.χ₄)
          (n : ZMod (4 * d)) = ZMod.χ₄ (n : ZMod 4) := by
    simpa using hfour
  have hd' :
      (DirichletCharacter.changeLevel (Nat.dvd_mul_left d 4)
          (jacobiDirichletCharacter d)) (n : ZMod (4 * d)) =
        jacobiDirichletCharacter d (n : ZMod d) := by
    simpa using hd
  change
    (DirichletCharacter.changeLevel (Nat.dvd_mul_right 4 d) ZMod.χ₄)
        (n : ZMod (4 * d)) *
      (DirichletCharacter.changeLevel (Nat.dvd_mul_left d 4)
        (jacobiDirichletCharacter d)) (n : ZMod (4 * d)) = _
  rw [hfour', hd', jacobiDirichletCharacter_apply_natCast]

/-- On a unit modulo `4d`, the `d ≡ 3 (mod 4)` branch has the intended
numerator-side Jacobi value.  Since the denominator is a unit modulo `4d`,
it is odd, so this is the usual Kronecker value `(4d / n)` on that unit. -/
theorem kroneckerCharacterFourMulThree_apply_eq_jacobi_numerator_of_coprime
    (d n : ℕ) [Fact (1 < d)] (hd : d % 4 = 3)
    (hn : n.Coprime (4 * d)) :
    kroneckerCharacterFourMulThree d (n : ZMod (4 * d)) =
      J(((4 * d : ℕ) : ℤ) | n) := by
  rw [kroneckerCharacterFourMulThree_apply_of_coprime d n hn]
  have hnfour : n.Coprime 4 :=
    (Nat.coprime_mul_iff_right.mp hn).1
  have hnodd : Odd n :=
    (hnfour.of_dvd_right (by norm_num : 2 ∣ 4)).odd_of_right
  calc
    ZMod.χ₄ (n : ZMod 4) * J((n : ℤ) | d) = J((d : ℤ) | n) :=
      (jacobi_numerator_eq_chiFour_mul_jacobi_denominator_of_mod_four_three
        d n hd hnodd).symm
    _ = J((4 : ℤ) | n) * J((d : ℤ) | n) := by
      rw [jacobiSym.at_four hnodd, one_mul]
    _ = J(((4 * d : ℕ) : ℤ) | n) := by
      simpa using (jacobiSym.mul_left (4 : ℤ) (d : ℤ) n).symm

/-- A lifted mod-eight factor times an odd Jacobi factor.  Specializing the
first argument to `χ₈` or `χ₈'` gives the two `8e` Kronecker branches. -/
def kroneckerCharacterEightMul (eps : DirichletCharacter ℤ 8)
    (e : ℕ) [Fact (1 < e)] : DirichletCharacter ℤ (8 * e) :=
  (DirichletCharacter.changeLevel (Nat.dvd_mul_right 8 e) eps) *
    (DirichletCharacter.changeLevel (Nat.dvd_mul_left e 8)
      (jacobiDirichletCharacter e))

/-- The `8e` branch for `e ≡ 1 (mod 4)`. -/
def kroneckerCharacterEightMulOne (e : ℕ) [Fact (1 < e)] :
    DirichletCharacter ℤ (8 * e) :=
  kroneckerCharacterEightMul ZMod.χ₈ e

/-- The `8e` branch for `e ≡ 3 (mod 4)`. -/
def kroneckerCharacterEightMulThree (e : ℕ) [Fact (1 < e)] :
    DirichletCharacter ℤ (8 * e) :=
  kroneckerCharacterEightMul ZMod.χ₈' e

/-- Evaluation of the generic lifted mod-eight/Jacobi product on a unit. -/
theorem kroneckerCharacterEightMul_apply_of_coprime
    (eps : DirichletCharacter ℤ 8) (e n : ℕ) [Fact (1 < e)]
    (hn : n.Coprime (8 * e)) :
    kroneckerCharacterEightMul eps e (n : ZMod (8 * e)) =
      eps (n : ZMod 8) * J((n : ℤ) | e) := by
  unfold kroneckerCharacterEightMul
  have height := DirichletCharacter.changeLevel_eq_cast_of_dvd eps
    (Nat.dvd_mul_right 8 e) (ZMod.unitOfCoprime n hn)
  have he := DirichletCharacter.changeLevel_eq_cast_of_dvd
    (jacobiDirichletCharacter e) (Nat.dvd_mul_left e 8)
      (ZMod.unitOfCoprime n hn)
  simp only [ZMod.coe_unitOfCoprime] at height he
  have height' :
      (DirichletCharacter.changeLevel (Nat.dvd_mul_right 8 e) eps)
          (n : ZMod (8 * e)) = eps (n : ZMod 8) := by
    simpa using height
  have he' :
      (DirichletCharacter.changeLevel (Nat.dvd_mul_left e 8)
          (jacobiDirichletCharacter e)) (n : ZMod (8 * e)) =
        jacobiDirichletCharacter e (n : ZMod e) := by
    simpa using he
  change
    (DirichletCharacter.changeLevel (Nat.dvd_mul_right 8 e) eps)
        (n : ZMod (8 * e)) *
      (DirichletCharacter.changeLevel (Nat.dvd_mul_left e 8)
        (jacobiDirichletCharacter e)) (n : ZMod (8 * e)) = _
  rw [height', he', jacobiDirichletCharacter_apply_natCast]

/-- The `e ≡ 1 (mod 4)` lifted branch has the numerator-side Jacobi value
on every unit modulo `8e`. -/
theorem kroneckerCharacterEightMulOne_apply_eq_jacobi_numerator_of_coprime
    (e n : ℕ) [Fact (1 < e)] (he : e % 4 = 1)
    (hn : n.Coprime (8 * e)) :
    kroneckerCharacterEightMulOne e (n : ZMod (8 * e)) =
      J(((8 * e : ℕ) : ℤ) | n) := by
  rw [kroneckerCharacterEightMulOne,
    kroneckerCharacterEightMul_apply_of_coprime ZMod.χ₈ e n hn]
  have hneight : n.Coprime 8 :=
    (Nat.coprime_mul_iff_right.mp hn).1
  have hnodd : Odd n :=
    (hneight.of_dvd_right (by norm_num : 2 ∣ 8)).odd_of_right
  have hrec : J((e : ℤ) | n) = J((n : ℤ) | e) :=
    jacobiSym.quadratic_reciprocity_one_mod_four he hnodd
  calc
    ZMod.χ₈ (n : ZMod 8) * J((n : ℤ) | e) =
        ZMod.χ₈ (n : ZMod 8) * J((e : ℤ) | n) := by rw [hrec]
    _ = J((8 : ℤ) | n) * J((e : ℤ) | n) := by
      rw [jacobi_eight_numerator_of_odd n hnodd]
    _ = J(((8 * e : ℕ) : ℤ) | n) := by
      simpa using (jacobiSym.mul_left (8 : ℤ) (e : ℤ) n).symm

/-- The `e ≡ 3 (mod 4)` lifted branch has the numerator-side Jacobi value
on every unit modulo `8e`. -/
theorem kroneckerCharacterEightMulThree_apply_eq_jacobi_numerator_of_coprime
    (e n : ℕ) [Fact (1 < e)] (he : e % 4 = 3)
    (hn : n.Coprime (8 * e)) :
    kroneckerCharacterEightMulThree e (n : ZMod (8 * e)) =
      J(((8 * e : ℕ) : ℤ) | n) := by
  rw [kroneckerCharacterEightMulThree,
    kroneckerCharacterEightMul_apply_of_coprime ZMod.χ₈' e n hn]
  have hneight : n.Coprime 8 :=
    (Nat.coprime_mul_iff_right.mp hn).1
  have hnodd : Odd n :=
    (hneight.of_dvd_right (by norm_num : 2 ∣ 8)).odd_of_right
  have hchi : ZMod.χ₈' (n : ZMod 8) =
      ZMod.χ₄ (n : ZMod 4) * ZMod.χ₈ (n : ZMod 8) := by
    simpa using ZMod.χ₈'_int_eq_χ₄_mul_χ₈ (n : ℤ)
  calc
    ZMod.χ₈' (n : ZMod 8) * J((n : ℤ) | e) =
        (ZMod.χ₄ (n : ZMod 4) * ZMod.χ₈ (n : ZMod 8)) *
          J((n : ℤ) | e) := by
      rw [hchi]
    _ = ZMod.χ₈ (n : ZMod 8) * J((e : ℤ) | n) := by
      rw [jacobi_numerator_eq_chiFour_mul_jacobi_denominator_of_mod_four_three
        e n he hnodd]
      ring
    _ = J((8 : ℤ) | n) * J((e : ℤ) | n) := by
      rw [jacobi_eight_numerator_of_odd n hnodd]
    _ = J(((8 * e : ℕ) : ℤ) | n) := by
      simpa using (jacobiSym.mul_left (8 : ℤ) (e : ℤ) n).symm

/-- The branchwise real quadratic character attached to the project's
positive fundamental-discriminant predicate.  The odd branch is the Jacobi
character.  In the `4d` branch it inserts the required `χ₄`, `χ₈`, or
`χ₈'` reciprocity factor; `D = 8` is handled separately.  This construction
does not assert primitivity or a zeta-factorization. -/
noncomputable def kroneckerCharacterAtPositiveFundamentalDiscriminant
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) : DirichletCharacter ℤ D := by
  classical
  by_cases hodd : Squarefree D ∧ D % 4 = 1
  · letI : Fact (1 < D) := ⟨hD.1⟩
    exact jacobiDirichletCharacter D
  · let d := D / 4
    have hfour : D = 4 * d ∧ Squarefree d ∧
        (d % 4 = 2 ∨ d % 4 = 3) := by
      rcases hD.2 with hodd' | hfour'
      · exact (hodd hodd').elim
      · obtain ⟨d', hD', hsq, hmod⟩ := hfour'
        subst D
        simpa [d] using ⟨hsq, hmod⟩
    rw [hfour.1]
    change DirichletCharacter ℤ (4 * d)
    by_cases hd2 : d % 4 = 2
    · by_cases hd_eq_two : d = 2
      · have hlevel8 : 4 * d = 8 := by omega
        rw [hlevel8]
        exact kroneckerCharacterEight
      · let e := d / 2
        have hegt : 1 < e := by
          dsimp [e]
          omega
        letI : Fact (1 < e) := ⟨hegt⟩
        have heodd : e % 2 = 1 := by
          dsimp [e]
          exact div_two_odd_of_mod_four_two d hd2
        have hfactor : 2 * (d / 2) = d :=
          two_mul_div_two_of_mod_four_two d hd2
        have hlevel : 4 * d = 8 * e := by
          dsimp [e]
          omega
        by_cases he1 : e % 4 = 1
        · rw [hlevel]
          exact kroneckerCharacterEightMulOne e
        · have he3 : e % 4 = 3 :=
            (Nat.odd_mod_four_iff.mp heodd).resolve_left he1
          rw [hlevel]
          exact kroneckerCharacterEightMulThree e
    · have hd3 : d % 4 = 3 := hfour.2.2.resolve_left hd2
      letI : Fact (1 < d) := ⟨by omega⟩
      exact kroneckerCharacterFourMulThree d

end

end PellPaper
