import Pell.QuadraticKroneckerCharacterScratch
import Pell.JacobiDirichletCharacterNonprincipal
import Pell.NonprincipalDirichletPolyaVinogradov

/-!
# Cancellation for denominator-variable Jacobi prefixes

For a positive odd nonsquare `q`, the function `k ↦ (q / k)` on odd
arguments is obtained from an actual Dirichlet character modulo `4q`.  If
`q ≡ 1 (mod 4)`, this is the Jacobi character modulo `q`, lifted to `4q`.
If `q ≡ 3 (mod 4)`, the extra `χ₄` factor corrects quadratic
reciprocity.  The modulus `4q` also makes every even argument a nonunit, so a
full character prefix is exactly the desired odd prefix.

No primitivity claim is needed: the all-nonprincipal Pólya--Vinogradov bound
applies directly, including when `q` has repeated prime factors.
-/

open scoped BigOperators

namespace PellPaper

open NumberTheorySymbols

noncomputable section

/-- The quadratic character modulo `4q` whose odd values are `(q / ·)`. -/
def jacobiDenominatorCharacter (q : ℕ) [Fact (1 < q)] :
    DirichletCharacter ℤ (4 * q) :=
  if q % 4 = 1 then
    DirichletCharacter.changeLevel (Nat.dvd_mul_left q 4)
      (jacobiDirichletCharacter q)
  else
    kroneckerCharacterFourMulThree q

/-- Complex scalar extension of `jacobiDenominatorCharacter`. -/
def jacobiDenominatorCharacterC (q : ℕ) [Fact (1 < q)] :
    DirichletCharacter ℂ (4 * q) :=
  (jacobiDenominatorCharacter q).ringHomComp (Int.castRingHom ℂ)

/-- On every odd natural argument, including nonunits, the character has the
numerator-side Jacobi value `(q / k)`. -/
theorem jacobiDenominatorCharacter_apply_of_odd
    (q k : ℕ) [Fact (1 < q)] (hqodd : Odd q) (hkodd : Odd k) :
    jacobiDenominatorCharacter q (k : ZMod (4 * q)) = J((q : ℤ) | k) := by
  have hk4 : k.Coprime 4 := by
    have hk2 : k.Coprime 2 := Nat.coprime_two_right.mpr hkodd
    simpa using hk2.pow_right 2
  by_cases hq1 : q % 4 = 1
  · rw [jacobiDenominatorCharacter, if_pos hq1]
    by_cases hkq : k.Coprime q
    · have hk4q : k.Coprime (4 * q) := hk4.mul_right hkq
      have hchange := DirichletCharacter.changeLevel_eq_cast_of_dvd
        (jacobiDirichletCharacter q) (Nat.dvd_mul_left q 4)
          (ZMod.unitOfCoprime k hk4q)
      simp only [ZMod.coe_unitOfCoprime] at hchange
      calc
        (DirichletCharacter.changeLevel (Nat.dvd_mul_left q 4)
            (jacobiDirichletCharacter q)) (k : ZMod (4 * q)) =
            jacobiDirichletCharacter q (k : ZMod q) := by
              simpa using hchange
        _ = J((q : ℤ) | k) :=
          jacobiDirichletCharacter_apply_eq_jacobi_numerator_of_odd
            q k hq1 hkodd
    · have hk4q : ¬k.Coprime (4 * q) := by
        intro h
        exact hkq (Nat.coprime_mul_iff_right.mp h).2
      have hleft :
          (DirichletCharacter.changeLevel (Nat.dvd_mul_left q 4)
            (jacobiDirichletCharacter q)) (k : ZMod (4 * q)) = 0 := by
        apply MulChar.map_nonunit
        simpa only [ZMod.isUnit_iff_coprime] using hk4q
      have hright : J((q : ℤ) | k) = 0 := by
        apply jacobiSym.eq_zero_iff.mpr
        refine ⟨by obtain ⟨t, ht⟩ := hkodd; omega, ?_⟩
        simpa only [Int.gcd_natCast_natCast, Nat.gcd_comm, Nat.Coprime] using hkq
      exact hleft.trans hright.symm
  · have hq3 : q % 4 = 3 :=
      (Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hqodd)).resolve_left hq1
    rw [jacobiDenominatorCharacter, if_neg hq1]
    by_cases hkq : k.Coprime q
    · have hk4q : k.Coprime (4 * q) := hk4.mul_right hkq
      exact (kroneckerCharacterFourMulThree_apply_of_coprime q k hk4q).trans
        (jacobi_numerator_eq_chiFour_mul_jacobi_denominator_of_mod_four_three
          q k hq3 hkodd).symm
    · have hk4q : ¬k.Coprime (4 * q) := by
        intro h
        exact hkq (Nat.coprime_mul_iff_right.mp h).2
      have hleft : kroneckerCharacterFourMulThree q
          (k : ZMod (4 * q)) = 0 := by
        apply MulChar.map_nonunit
        simpa only [ZMod.isUnit_iff_coprime] using hk4q
      have hright : J((q : ℤ) | k) = 0 := by
        apply jacobiSym.eq_zero_iff.mpr
        refine ⟨by obtain ⟨t, ht⟩ := hkodd; omega, ?_⟩
        simpa only [Int.gcd_natCast_natCast, Nat.gcd_comm, Nat.Coprime] using hkq
      exact hleft.trans hright.symm

/-- The complex character has the same value on every odd argument. -/
theorem jacobiDenominatorCharacterC_apply_of_odd
    (q k : ℕ) [Fact (1 < q)] (hqodd : Odd q) (hkodd : Odd k) :
    jacobiDenominatorCharacterC q (k : ZMod (4 * q)) =
      (J((q : ℤ) | k) : ℂ) := by
  change (jacobiDenominatorCharacter q (k : ZMod (4 * q)) : ℂ) = _
  rw [jacobiDenominatorCharacter_apply_of_odd q k hqodd hkodd]

private theorem one_lt_of_pos_not_square
    (q : ℕ) (hq : 0 < q) (hns : ¬IsSquare q) : 1 < q := by
  have hq1 : q ≠ 1 := by
    intro h
    exact hns (h ▸ IsSquare.one)
  omega

/-- For odd nonsquare `q`, the denominator-variable quadratic character is
nonprincipal. -/
theorem jacobiDenominatorCharacterC_ne_one_of_odd_not_isSquare
    (q : ℕ) (hq : 0 < q) (hqodd : Odd q) (hns : ¬IsSquare q) :
    let _ : Fact (1 < q) := ⟨one_lt_of_pos_not_square q hq hns⟩
    jacobiDenominatorCharacterC q ≠ 1 := by
  let _ : Fact (1 < q) := ⟨one_lt_of_pos_not_square q hq hns⟩
  dsimp only
  obtain ⟨a, ha⟩ :=
    exists_nat_jacobiSym_eq_neg_one_of_odd_not_isSquare q hq hqodd hns
  have hq4 : q.Coprime 4 := by
    have hq2 : q.Coprime 2 := Nat.coprime_two_right.mpr hqodd
    simpa using hq2.pow_right 2
  obtain ⟨k, hkq, hk4⟩ := Nat.chineseRemainder hq4 a 1
  have hk4eq : k % 4 = 1 := by
    simpa [Nat.ModEq] using hk4
  have hkodd : Odd k :=
    Nat.odd_iff.mpr (Nat.odd_of_mod_four_eq_one hk4eq)
  have hjmod : J((k : ℤ) | q) = J((a : ℤ) | q) := by
    apply jacobiSym.mod_left'
    exact_mod_cast hkq
  have hjneg : J((q : ℤ) | k) = -1 := by
    calc
      J((q : ℤ) | k) = J((k : ℤ) | q) :=
        jacobiSym.quadratic_reciprocity_one_mod_four' hqodd hk4eq
      _ = J((a : ℤ) | q) := hjmod
      _ = -1 := ha
  have hval : jacobiDenominatorCharacterC q (k : ZMod (4 * q)) = -1 := by
    rw [jacobiDenominatorCharacterC_apply_of_odd q k hqodd hkodd, hjneg]
    norm_num
  have hunit : IsUnit (k : ZMod (4 * q)) :=
    MulChar.apply_ne_zero_iff.mp (by rw [hval]; norm_num)
  intro h
  rw [h, MulChar.one_apply hunit] at hval
  norm_num at hval

/-- Pólya--Vinogradov cancellation for the odd denominator prefix of `(q/k)`.
The even terms of the character modulo `4q` vanish, so filtering to odd `k`
does not lose any part of the character sum. -/
theorem abs_sum_jacobiSym_denominator_odd_le
    (q X : ℕ) (hq : 0 < q) (hqodd : Odd q) (hns : ¬IsSquare q) :
    |∑ k ∈ (Finset.Icc 1 X).filter Odd,
        (J((q : ℤ) | k) : ℝ)| ≤
      2 * Real.sqrt (4 * (q : ℝ)) *
        (1 + Real.log (4 * (q : ℝ))) := by
  let _ : Fact (1 < q) := ⟨one_lt_of_pos_not_square q hq hns⟩
  let _ : NeZero (4 * q) := ⟨Nat.mul_ne_zero (by norm_num) hq.ne'⟩
  have hchi : jacobiDenominatorCharacterC q ≠ 1 :=
    jacobiDenominatorCharacterC_ne_one_of_odd_not_isSquare q hq hqodd hns
  have hpv := nonprincipalDirichletCharacter_prefix_norm_le
    (jacobiDenominatorCharacterC q) hchi X
  have hterm (k : ℕ) :
      jacobiDenominatorCharacterC q (k : ZMod (4 * q)) =
        if Odd k then ((J((q : ℤ) | k) : ℝ) : ℂ) else 0 := by
    by_cases hkodd : Odd k
    · rw [if_pos hkodd,
        jacobiDenominatorCharacterC_apply_of_odd q k hqodd hkodd]
      norm_num
    · rw [if_neg hkodd]
      apply MulChar.map_nonunit
      simp only [ZMod.isUnit_iff_coprime]
      intro hk
      have hk4 : k.Coprime 4 := (Nat.coprime_mul_iff_right.mp hk).1
      exact hkodd ((hk4.of_dvd_right (by norm_num : 2 ∣ 4)).odd_of_right)
  have hsum :
      (∑ k ∈ Finset.Icc 1 X,
          jacobiDenominatorCharacterC q (k : ZMod (4 * q))) =
        Complex.ofReal
          (∑ k ∈ (Finset.Icc 1 X).filter Odd,
            (J((q : ℤ) | k) : ℝ)) := by
    calc
      (∑ k ∈ Finset.Icc 1 X,
          jacobiDenominatorCharacterC q (k : ZMod (4 * q))) =
          ∑ k ∈ Finset.Icc 1 X,
            if Odd k then ((J((q : ℤ) | k) : ℝ) : ℂ) else 0 := by
              apply Finset.sum_congr rfl
              intro k hk
              exact hterm k
      _ = ∑ k ∈ (Finset.Icc 1 X).filter Odd,
          ((J((q : ℤ) | k) : ℝ) : ℂ) := by
            rw [Finset.sum_filter]
      _ = Complex.ofReal
          (∑ k ∈ (Finset.Icc 1 X).filter Odd,
            (J((q : ℤ) | k) : ℝ)) := by
            rw [Complex.ofReal_sum]
  rw [hsum, Complex.norm_real, Real.norm_eq_abs] at hpv
  norm_num [Nat.cast_mul] at hpv ⊢
  exact hpv

end
end PellPaper
