import Pell.QuadraticSelectedLValueTruncation

/-!
# The four quadratic-character branches used in the manuscript

For odd `n`, quadratic reciprocity rewrites the selected Kronecker
coefficient for a positive fundamental discriminant of shape `m`, `4 * m`,
or `8 * m` as a fixed character of modulus eight times `J(n | m)`.  This
module records those four pointwise identities, including non-coprime odd
arguments, and their exact finite reciprocal-polynomial consequences.

There is no analytic estimate, infinite-series rearrangement, conductor
claim, or `L`-function identity here.  The positive-fundamental-discriminant
hypotheses merely identify the selected project character; the reciprocity
formulas themselves use only the displayed congruence and oddness data.
-/

namespace PellPaper

open NumberTheorySymbols
open scoped BigOperators

noncomputable section

/-- The character `chi_4`, viewed as a character modulo eight. -/
def main4ChiFourModuloEight : DirichletCharacter ℤ 8 :=
  DirichletCharacter.changeLevel (by norm_num : 4 ∣ 8) ZMod.χ₄

/-- The finite reciprocal polynomial appearing after the manuscript
reciprocity step, for one fixed character `rho` modulo eight. -/
def main4TwistedOddJacobiReciprocalPolynomial
    (rho : DirichletCharacter ℤ 8) (m N : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 N).filter Odd,
    (rho (n : ZMod 8) : ℝ) * (J((n : ℤ) | m) : ℝ) / (n : ℝ)

/-- The same twisted reciprocal polynomial written over all positive
indices.  This is the literal finite shape used by a character-sum theorem;
the modulus-eight character itself kills every even index. -/
def main4TwistedJacobiReciprocalPolynomial
    (rho : DirichletCharacter ℤ 8) (m N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N,
    (rho (n : ZMod 8) : ℝ) * (J((n : ℤ) | m) : ℝ) / (n : ℝ)

/-- An odd integer is a unit modulo eight. -/
theorem coprime_eight_of_odd {n : ℕ} (hn : Odd n) : n.Coprime 8 := by
  have h : n.Coprime (2 ^ 3) := Nat.Coprime.pow_right 3 hn.coprime_two_right
  norm_num at h ⊢
  exact h

/-- A modulus-eight Dirichlet character vanishes at every even natural
argument. -/
theorem dirichletCharacter_mod_eight_apply_eq_zero_of_even
    (rho : DirichletCharacter ℤ 8) (n : ℕ) (hn : Even n) :
    rho (n : ZMod 8) = 0 := by
  apply MulChar.map_nonunit
  rw [ZMod.isUnit_iff_coprime]
  intro hcop
  have htwo : n.Coprime 2 :=
    Nat.Coprime.of_dvd_right (by norm_num : 2 ∣ 8) hcop
  exact (Nat.not_odd_iff_even.mpr hn) htwo.odd_of_right

/-- The all-index and explicitly odd-index versions of the finite twist
polynomial agree exactly. -/
theorem main4TwistedJacobiReciprocalPolynomial_eq_odd
    (rho : DirichletCharacter ℤ 8) (m N : ℕ) :
    main4TwistedJacobiReciprocalPolynomial rho m N =
      main4TwistedOddJacobiReciprocalPolynomial rho m N := by
  unfold main4TwistedJacobiReciprocalPolynomial
    main4TwistedOddJacobiReciprocalPolynomial
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : Odd n
  · simp only [hn, if_true]
  · have hneven : Even n := Nat.not_odd_iff_even.mp hn
    rw [if_neg hn,
      dirichletCharacter_mod_eight_apply_eq_zero_of_even rho n hneven]
    norm_num

/-- The trivial character modulo eight is one at every odd argument. -/
theorem main4TrivialModuloEight_apply_of_odd (n : ℕ) (hn : Odd n) :
    (1 : DirichletCharacter ℤ 8) (n : ZMod 8) = 1 := by
  apply MulChar.one_apply
  simpa only [ZMod.isUnit_iff_coprime] using coprime_eight_of_odd hn

/-- The level-eight lift of `chi_4` has the expected value on odd
arguments. -/
theorem main4ChiFourModuloEight_apply_of_odd (n : ℕ) (hn : Odd n) :
    main4ChiFourModuloEight (n : ZMod 8) = ZMod.χ₄ (n : ZMod 4) := by
  have h := DirichletCharacter.changeLevel_eq_cast_of_dvd ZMod.χ₄
    (by norm_num : 4 ∣ 8) (ZMod.unitOfCoprime n (coprime_eight_of_odd hn))
  simp only [ZMod.coe_unitOfCoprime] at h
  rw [ZMod.cast_natCast (by norm_num : 4 ∣ 8) n] at h
  simpa only [main4ChiFourModuloEight] using h

/-- Reciprocity in the `D = m`, `m = 1 (mod 4)` branch. -/
theorem jacobi_main4OddBranch_of_odd
    (m n : ℕ) (hm : m % 4 = 1) (hn : Odd n) :
    J((m : ℤ) | n) = J((n : ℤ) | m) :=
  jacobiSym.quadratic_reciprocity_one_mod_four hm hn

/-- Reciprocity in the `D = 4m`, `m = 3 (mod 4)` branch. -/
theorem jacobi_main4FourBranch_of_odd
    (m n : ℕ) (hm : m % 4 = 3) (hn : Odd n) :
    J(((4 * m : ℕ) : ℤ) | n) =
      main4ChiFourModuloEight (n : ZMod 8) * J((n : ℤ) | m) := by
  calc
    J(((4 * m : ℕ) : ℤ) | n) = J((4 : ℤ) | n) * J((m : ℤ) | n) := by
      simpa using (jacobiSym.mul_left (4 : ℤ) (m : ℤ) n)
    _ = ZMod.χ₄ (n : ZMod 4) * J((n : ℤ) | m) := by
      rw [jacobiSym.at_four hn, one_mul,
        jacobi_numerator_eq_chiFour_mul_jacobi_denominator_of_mod_four_three
          m n hm hn]
    _ = main4ChiFourModuloEight (n : ZMod 8) * J((n : ℤ) | m) := by
      rw [main4ChiFourModuloEight_apply_of_odd n hn]

/-- Reciprocity in the `D = 8m`, `m = 1 (mod 4)` branch. -/
theorem jacobi_main4EightOneBranch_of_odd
    (m n : ℕ) (hm : m % 4 = 1) (hn : Odd n) :
    J(((8 * m : ℕ) : ℤ) | n) =
      ZMod.χ₈ (n : ZMod 8) * J((n : ℤ) | m) := by
  calc
    J(((8 * m : ℕ) : ℤ) | n) = J((8 : ℤ) | n) * J((m : ℤ) | n) := by
      simpa using (jacobiSym.mul_left (8 : ℤ) (m : ℤ) n)
    _ = ZMod.χ₈ (n : ZMod 8) * J((n : ℤ) | m) := by
      rw [jacobi_eight_numerator_of_odd n hn,
        jacobi_main4OddBranch_of_odd m n hm hn]

/-- Reciprocity in the `D = 8m`, `m = 3 (mod 4)` branch. -/
theorem jacobi_main4EightThreeBranch_of_odd
    (m n : ℕ) (hm : m % 4 = 3) (hn : Odd n) :
    J(((8 * m : ℕ) : ℤ) | n) =
      ZMod.χ₈' (n : ZMod 8) * J((n : ℤ) | m) := by
  have hchi : ZMod.χ₈' (n : ZMod 8) =
      ZMod.χ₄ (n : ZMod 4) * ZMod.χ₈ (n : ZMod 8) := by
    simpa using ZMod.χ₈'_int_eq_χ₄_mul_χ₈ (n : ℤ)
  calc
    J(((8 * m : ℕ) : ℤ) | n) = J((8 : ℤ) | n) * J((m : ℤ) | n) := by
      simpa using (jacobiSym.mul_left (8 : ℤ) (m : ℤ) n)
    _ = ZMod.χ₈ (n : ZMod 8) *
        (ZMod.χ₄ (n : ZMod 4) * J((n : ℤ) | m)) := by
      rw [jacobi_eight_numerator_of_odd n hn,
        jacobi_numerator_eq_chiFour_mul_jacobi_denominator_of_mod_four_three
          m n hm hn]
    _ = ZMod.χ₈' (n : ZMod 8) * J((n : ℤ) | m) := by
      rw [hchi]
      ring

/-- The selected integral character in the `D = m` branch is the trivial
mod-eight twist of `J(n | m)` at every odd argument, including nonunits. -/
theorem kroneckerCharacter_main4OddBranch_apply_of_odd
    (m n : ℕ) (hD : PositiveFundamentalDiscriminant m)
    (hm : m % 4 = 1) (hn : Odd n) :
    kroneckerCharacterAtPositiveFundamentalDiscriminant m hD n =
      (1 : DirichletCharacter ℤ 8) (n : ZMod 8) * J((n : ℤ) | m) := by
  rw [kroneckerCharacterAtPositiveFundamentalDiscriminant_apply_eq_jacobi_of_odd
    m n hD hn, jacobi_main4OddBranch_of_odd m n hm hn,
    main4TrivialModuloEight_apply_of_odd n hn, one_mul]

/-- The selected integral character in the `D = 4m` branch is the lifted
`chi_4` twist of `J(n | m)` at every odd argument, including nonunits. -/
theorem kroneckerCharacter_main4FourBranch_apply_of_odd
    (m n : ℕ) (hD : PositiveFundamentalDiscriminant (4 * m))
    (hm : m % 4 = 3) (hn : Odd n) :
    kroneckerCharacterAtPositiveFundamentalDiscriminant (4 * m) hD n =
      main4ChiFourModuloEight (n : ZMod 8) * J((n : ℤ) | m) := by
  rw [kroneckerCharacterAtPositiveFundamentalDiscriminant_apply_eq_jacobi_of_odd
    (4 * m) n hD hn]
  exact jacobi_main4FourBranch_of_odd m n hm hn

/-- The selected integral character in the first `D = 8m` branch is the
`chi_8` twist of `J(n | m)` at every odd argument, including nonunits. -/
theorem kroneckerCharacter_main4EightOneBranch_apply_of_odd
    (m n : ℕ) (hD : PositiveFundamentalDiscriminant (8 * m))
    (hm : m % 4 = 1) (hn : Odd n) :
    kroneckerCharacterAtPositiveFundamentalDiscriminant (8 * m) hD n =
      ZMod.χ₈ (n : ZMod 8) * J((n : ℤ) | m) := by
  rw [kroneckerCharacterAtPositiveFundamentalDiscriminant_apply_eq_jacobi_of_odd
    (8 * m) n hD hn]
  exact jacobi_main4EightOneBranch_of_odd m n hm hn

/-- The selected integral character in the second `D = 8m` branch is the
`chi_8'` twist of `J(n | m)` at every odd argument, including nonunits. -/
theorem kroneckerCharacter_main4EightThreeBranch_apply_of_odd
    (m n : ℕ) (hD : PositiveFundamentalDiscriminant (8 * m))
    (hm : m % 4 = 3) (hn : Odd n) :
    kroneckerCharacterAtPositiveFundamentalDiscriminant (8 * m) hD n =
      ZMod.χ₈' (n : ZMod 8) * J((n : ℤ) | m) := by
  rw [kroneckerCharacterAtPositiveFundamentalDiscriminant_apply_eq_jacobi_of_odd
    (8 * m) n hD hn]
  exact jacobi_main4EightThreeBranch_of_odd m n hm hn

/-- Exact reciprocal-polynomial rewrite for `D = m`. -/
theorem oddJacobiReciprocalPolynomial_main4OddBranch
    (m N : ℕ) (hm : m % 4 = 1) :
    oddJacobiReciprocalPolynomial m N =
      main4TwistedOddJacobiReciprocalPolynomial 1 m N := by
  unfold oddJacobiReciprocalPolynomial
    main4TwistedOddJacobiReciprocalPolynomial
  apply Finset.sum_congr rfl
  intro n hnmem
  have hn : Odd n := (Finset.mem_filter.mp hnmem).2
  rw [jacobi_main4OddBranch_of_odd m n hm hn,
    main4TrivialModuloEight_apply_of_odd n hn]
  norm_num

/-- Exact reciprocal-polynomial rewrite for `D = 4m`. -/
theorem oddJacobiReciprocalPolynomial_main4FourBranch
    (m N : ℕ) (hm : m % 4 = 3) :
    oddJacobiReciprocalPolynomial (4 * m) N =
      main4TwistedOddJacobiReciprocalPolynomial main4ChiFourModuloEight m N := by
  unfold oddJacobiReciprocalPolynomial
    main4TwistedOddJacobiReciprocalPolynomial
  apply Finset.sum_congr rfl
  intro n hnmem
  have hn : Odd n := (Finset.mem_filter.mp hnmem).2
  rw [jacobi_main4FourBranch_of_odd m n hm hn, Int.cast_mul]

/-- Exact reciprocal-polynomial rewrite for `D = 8m`, `m = 1 (mod 4)`. -/
theorem oddJacobiReciprocalPolynomial_main4EightOneBranch
    (m N : ℕ) (hm : m % 4 = 1) :
    oddJacobiReciprocalPolynomial (8 * m) N =
      main4TwistedOddJacobiReciprocalPolynomial ZMod.χ₈ m N := by
  unfold oddJacobiReciprocalPolynomial
    main4TwistedOddJacobiReciprocalPolynomial
  apply Finset.sum_congr rfl
  intro n hnmem
  have hn : Odd n := (Finset.mem_filter.mp hnmem).2
  rw [jacobi_main4EightOneBranch_of_odd m n hm hn, Int.cast_mul]

/-- Exact reciprocal-polynomial rewrite for `D = 8m`, `m = 3 (mod 4)`. -/
theorem oddJacobiReciprocalPolynomial_main4EightThreeBranch
    (m N : ℕ) (hm : m % 4 = 3) :
    oddJacobiReciprocalPolynomial (8 * m) N =
      main4TwistedOddJacobiReciprocalPolynomial ZMod.χ₈' m N := by
  unfold oddJacobiReciprocalPolynomial
    main4TwistedOddJacobiReciprocalPolynomial
  apply Finset.sum_congr rfl
  intro n hnmem
  have hn : Odd n := (Finset.mem_filter.mp hnmem).2
  rw [jacobi_main4EightThreeBranch_of_odd m n hm hn, Int.cast_mul]

/-- All-index form of the exact `D = m` reciprocal-polynomial rewrite. -/
theorem oddJacobiReciprocalPolynomial_eq_main4TwistedOddBranch
    (m N : ℕ) (hm : m % 4 = 1) :
    oddJacobiReciprocalPolynomial m N =
      main4TwistedJacobiReciprocalPolynomial 1 m N :=
  (oddJacobiReciprocalPolynomial_main4OddBranch m N hm).trans
    (main4TwistedJacobiReciprocalPolynomial_eq_odd 1 m N).symm

/-- All-index form of the exact `D = 4m` reciprocal-polynomial rewrite. -/
theorem oddJacobiReciprocalPolynomial_eq_main4TwistedFourBranch
    (m N : ℕ) (hm : m % 4 = 3) :
    oddJacobiReciprocalPolynomial (4 * m) N =
      main4TwistedJacobiReciprocalPolynomial main4ChiFourModuloEight m N :=
  (oddJacobiReciprocalPolynomial_main4FourBranch m N hm).trans
    (main4TwistedJacobiReciprocalPolynomial_eq_odd main4ChiFourModuloEight m N).symm

/-- All-index form of the exact `D = 8m`, `m = 1 (mod 4)` rewrite. -/
theorem oddJacobiReciprocalPolynomial_eq_main4TwistedEightOneBranch
    (m N : ℕ) (hm : m % 4 = 1) :
    oddJacobiReciprocalPolynomial (8 * m) N =
      main4TwistedJacobiReciprocalPolynomial ZMod.χ₈ m N :=
  (oddJacobiReciprocalPolynomial_main4EightOneBranch m N hm).trans
    (main4TwistedJacobiReciprocalPolynomial_eq_odd ZMod.χ₈ m N).symm

/-- All-index form of the exact `D = 8m`, `m = 3 (mod 4)` rewrite. -/
theorem oddJacobiReciprocalPolynomial_eq_main4TwistedEightThreeBranch
    (m N : ℕ) (hm : m % 4 = 3) :
    oddJacobiReciprocalPolynomial (8 * m) N =
      main4TwistedJacobiReciprocalPolynomial ZMod.χ₈' m N :=
  (oddJacobiReciprocalPolynomial_main4EightThreeBranch m N hm).trans
    (main4TwistedJacobiReciprocalPolynomial_eq_odd ZMod.χ₈' m N).symm

/-- The actual oddified selected-character prefix in the `D = m` branch is
exactly the trivial-twist reciprocal polynomial. -/
theorem oddifiedKroneckerCharacter_reciprocalPrefix_eq_main4OddBranch
    (m N : ℕ) (hD : PositiveFundamentalDiscriminant m)
    (hm : m % 4 = 1) :
    (∑ n ∈ Finset.Icc 1 N,
      oddifiedKroneckerCharacterAtPositiveFundamentalDiscriminant m hD
        (n : ZMod (2 * m)) / (n : ℂ)) =
      (main4TwistedOddJacobiReciprocalPolynomial 1 m N : ℂ) := by
  rw [oddifiedKroneckerCharacter_reciprocalPrefix_eq_polynomial,
    oddJacobiReciprocalPolynomial_main4OddBranch m N hm]

/-- The actual oddified selected-character prefix in the `D = 4m` branch is
exactly the lifted-`chi_4` reciprocal polynomial. -/
theorem oddifiedKroneckerCharacter_reciprocalPrefix_eq_main4FourBranch
    (m N : ℕ) (hD : PositiveFundamentalDiscriminant (4 * m))
    (hm : m % 4 = 3) :
    (∑ n ∈ Finset.Icc 1 N,
      oddifiedKroneckerCharacterAtPositiveFundamentalDiscriminant (4 * m) hD
        (n : ZMod (2 * (4 * m))) / (n : ℂ)) =
      (main4TwistedOddJacobiReciprocalPolynomial main4ChiFourModuloEight m N : ℂ) := by
  rw [oddifiedKroneckerCharacter_reciprocalPrefix_eq_polynomial,
    oddJacobiReciprocalPolynomial_main4FourBranch m N hm]

/-- The actual oddified selected-character prefix in the `D = 8m`,
`m = 1 (mod 4)` branch is exactly the `chi_8` reciprocal polynomial. -/
theorem oddifiedKroneckerCharacter_reciprocalPrefix_eq_main4EightOneBranch
    (m N : ℕ) (hD : PositiveFundamentalDiscriminant (8 * m))
    (hm : m % 4 = 1) :
    (∑ n ∈ Finset.Icc 1 N,
      oddifiedKroneckerCharacterAtPositiveFundamentalDiscriminant (8 * m) hD
        (n : ZMod (2 * (8 * m))) / (n : ℂ)) =
      (main4TwistedOddJacobiReciprocalPolynomial ZMod.χ₈ m N : ℂ) := by
  rw [oddifiedKroneckerCharacter_reciprocalPrefix_eq_polynomial,
    oddJacobiReciprocalPolynomial_main4EightOneBranch m N hm]

/-- The actual oddified selected-character prefix in the `D = 8m`,
`m = 3 (mod 4)` branch is exactly the `chi_8'` reciprocal polynomial. -/
theorem oddifiedKroneckerCharacter_reciprocalPrefix_eq_main4EightThreeBranch
    (m N : ℕ) (hD : PositiveFundamentalDiscriminant (8 * m))
    (hm : m % 4 = 3) :
    (∑ n ∈ Finset.Icc 1 N,
      oddifiedKroneckerCharacterAtPositiveFundamentalDiscriminant (8 * m) hD
        (n : ZMod (2 * (8 * m))) / (n : ℂ)) =
      (main4TwistedOddJacobiReciprocalPolynomial ZMod.χ₈' m N : ℂ) := by
  rw [oddifiedKroneckerCharacter_reciprocalPrefix_eq_polynomial,
    oddJacobiReciprocalPolynomial_main4EightThreeBranch m N hm]

/-- The oddified complex coefficient in the `D = m` branch is the same
trivial-twist expression. -/
theorem oddifiedKroneckerCharacter_main4OddBranch_apply_of_odd
    (m n : ℕ) (hD : PositiveFundamentalDiscriminant m)
    (hm : m % 4 = 1) (hn : Odd n) :
    oddifiedKroneckerCharacterAtPositiveFundamentalDiscriminant m hD n =
      ((1 : DirichletCharacter ℤ 8) (n : ZMod 8) : ℂ) *
        (J((n : ℤ) | m) : ℂ) := by
  rw [oddifiedKroneckerCharacterAtPositiveFundamentalDiscriminant_apply_eq_jacobi_of_odd
    m n hD hn, jacobi_main4OddBranch_of_odd m n hm hn,
    main4TrivialModuloEight_apply_of_odd n hn]
  norm_num

/-- The oddified complex coefficient in the `D = 4m` branch is the same
lifted-`chi_4` expression. -/
theorem oddifiedKroneckerCharacter_main4FourBranch_apply_of_odd
    (m n : ℕ) (hD : PositiveFundamentalDiscriminant (4 * m))
    (hm : m % 4 = 3) (hn : Odd n) :
    oddifiedKroneckerCharacterAtPositiveFundamentalDiscriminant (4 * m) hD n =
      (main4ChiFourModuloEight (n : ZMod 8) : ℂ) *
        (J((n : ℤ) | m) : ℂ) := by
  rw [oddifiedKroneckerCharacterAtPositiveFundamentalDiscriminant_apply_eq_jacobi_of_odd
    (4 * m) n hD hn, jacobi_main4FourBranch_of_odd m n hm hn, Int.cast_mul]

/-- The oddified complex coefficient in the first `D = 8m` branch is the
same `chi_8` expression. -/
theorem oddifiedKroneckerCharacter_main4EightOneBranch_apply_of_odd
    (m n : ℕ) (hD : PositiveFundamentalDiscriminant (8 * m))
    (hm : m % 4 = 1) (hn : Odd n) :
    oddifiedKroneckerCharacterAtPositiveFundamentalDiscriminant (8 * m) hD n =
      (ZMod.χ₈ (n : ZMod 8) : ℂ) * (J((n : ℤ) | m) : ℂ) := by
  rw [oddifiedKroneckerCharacterAtPositiveFundamentalDiscriminant_apply_eq_jacobi_of_odd
    (8 * m) n hD hn, jacobi_main4EightOneBranch_of_odd m n hm hn, Int.cast_mul]

/-- The oddified complex coefficient in the second `D = 8m` branch is the
same `chi_8'` expression. -/
theorem oddifiedKroneckerCharacter_main4EightThreeBranch_apply_of_odd
    (m n : ℕ) (hD : PositiveFundamentalDiscriminant (8 * m))
    (hm : m % 4 = 3) (hn : Odd n) :
    oddifiedKroneckerCharacterAtPositiveFundamentalDiscriminant (8 * m) hD n =
      (ZMod.χ₈' (n : ZMod 8) : ℂ) * (J((n : ℤ) | m) : ℂ) := by
  rw [oddifiedKroneckerCharacterAtPositiveFundamentalDiscriminant_apply_eq_jacobi_of_odd
    (8 * m) n hD hn, jacobi_main4EightThreeBranch_of_odd m n hm hn, Int.cast_mul]

end

end PellPaper
