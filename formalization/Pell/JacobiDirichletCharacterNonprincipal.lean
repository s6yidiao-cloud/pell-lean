import Pell.QuadraticDirichletCharacter
import Mathlib.Data.Nat.Squarefree

/-!
# Nonprincipality of the numerator-Jacobi character

For a positive odd nonsquare modulus, an odd-exponent prime factor supplies
a quadratic nonresidue.  Binary Chinese remaindering makes the numerator
equal to that residue at this prime and equal to one at the complementary
factor.  The resulting Jacobi value is minus one, so the existing actual
complex numerator-Jacobi character is nonprincipal.  No primitivity claim
is made; the modulus may have repeated prime factors.
-/

namespace PellPaper

open NumberTheorySymbols

noncomputable section

private theorem exists_odd_prime_odd_factorization
    (n : ℕ) (hn : 0 < n) (hodd : Odd n) (hns : ¬IsSquare n) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ Odd (n.factorization p) := by
  obtain ⟨w, s, hw, hs, hmul, hsf⟩ := Nat.sq_mul_squarefree_of_pos hn
  have hw1 : w ≠ 1 := by
    intro h
    apply hns
    rw [← hmul, h, mul_one]
    exact IsSquare.sq s
  let p := w.minFac
  have hp : p.Prime := Nat.minFac_prime hw1
  have hpw : p ∣ w := Nat.minFac_dvd w
  have hpn : p ∣ n := by
    rw [← hmul]
    exact dvd_mul_of_dvd_right hpw (s ^ 2)
  have hp2 : p ≠ 2 := by
    intro h
    exact hodd.not_two_dvd_nat (h ▸ hpn)
  refine ⟨p, hp, hp2, s.factorization p, ?_⟩
  rw [← hmul, Nat.factorization_mul (pow_ne_zero 2 hs.ne') hw.ne',
    Nat.factorization_pow, Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul,
    Nat.factorization_eq_one_of_squarefree hsf hp hpw]
  norm_num

private theorem jacobiSym_nat_modEq {a b m : ℕ} (h : a ≡ b [MOD m]) :
    J((a : ℤ) | m) = J((b : ℤ) | m) := by
  apply jacobiSym.mod_left'
  exact_mod_cast h

/-- Every positive odd nonsquare modulus admits a natural numerator whose
actual Jacobi symbol is minus one. -/
theorem exists_nat_jacobiSym_eq_neg_one_of_odd_not_isSquare
    (n : ℕ) (hn : 0 < n) (hodd : Odd n) (hns : ¬IsSquare n) :
    ∃ a : ℕ, J((a : ℤ) | n) = -1 := by
  obtain ⟨p, hp, hp2, hkodd⟩ := exists_odd_prime_odd_factorization n hn hodd hns
  let _ : Fact p.Prime := ⟨hp⟩
  obtain ⟨r, hr⟩ := quadraticChar_exists_neg_one (F := ZMod p)
    (by simpa only [ZMod.ringChar_zmod_n] using hp2)
  have hrj : J((r.val : ℤ) | p) = -1 := by
    rw [← jacobiSym.legendreSym.to_jacobiSym]
    simpa only [legendreSym, Int.cast_natCast, ZMod.natCast_zmod_val] using hr
  let m := ordCompl[p] n
  have hm : m ≠ 0 := (Nat.ordCompl_pos p hn.ne').ne'
  have hcop : p.Coprime m := Nat.coprime_ordCompl hp hn.ne'
  obtain ⟨a, hap, ham⟩ := Nat.chineseRemainder hcop r.val 1
  have haj : J((a : ℤ) | p) = -1 := (jacobiSym_nat_modEq hap).trans hrj
  have hamj : J((a : ℤ) | m) = 1 := by
    rw [jacobiSym_nat_modEq ham]
    exact jacobiSym.one_left m
  refine ⟨a, ?_⟩
  calc
    J((a : ℤ) | n) = J((a : ℤ) | p ^ n.factorization p * m) := by
      rw [Nat.ordProj_mul_ordCompl_eq_self]
    _ = J((a : ℤ) | p) ^ n.factorization p * J((a : ℤ) | m) := by
      rw [jacobiSym.mul_right' _ (pow_ne_zero _ hp.ne_zero) hm, jacobiSym.pow_right]
    _ = -1 := by rw [haj, hamj, mul_one, hkodd.neg_one_pow]

private theorem one_lt_of_pos_not_isSquare
    (n : ℕ) (hn : 0 < n) (hns : ¬IsSquare n) : 1 < n := by
  have hn1 : n ≠ 1 := by
    intro h
    exact hns (h ▸ IsSquare.one)
  omega

/-- The actual complex numerator-Jacobi Dirichlet character of a positive
odd nonsquare modulus is nonprincipal.  Its required level instance is
derived internally, not an additional hypothesis. -/
theorem jacobiDirichletCharacterC_ne_one_of_odd_not_isSquare
    (n : ℕ) (hn : 0 < n) (hodd : Odd n) (hns : ¬IsSquare n) :
    let _ : Fact (1 < n) := ⟨one_lt_of_pos_not_isSquare n hn hns⟩
    jacobiDirichletCharacterC n ≠ 1 := by
  let _ : Fact (1 < n) := ⟨one_lt_of_pos_not_isSquare n hn hns⟩
  dsimp only
  obtain ⟨a, ha⟩ := exists_nat_jacobiSym_eq_neg_one_of_odd_not_isSquare n hn hodd hns
  have hval : jacobiDirichletCharacterC n (a : ZMod n) = -1 := by
    rw [jacobiDirichletCharacterC_apply_natCast, ha]
    norm_num
  have hunit : IsUnit (a : ZMod n) := MulChar.apply_ne_zero_iff.mp (by rw [hval]; norm_num)
  intro h
  rw [h, MulChar.one_apply hunit] at hval
  norm_num at hval

end
end PellPaper
