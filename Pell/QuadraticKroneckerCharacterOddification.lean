import Pell.QuadraticKroneckerCharacterAllOddValues
import Pell.QuadraticSelectedLValueNormalizedRegulator
import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-!
# The actual odd part of the selected quadratic character

Changing the selected complex character from level `D` to level `2 * D`
removes its even coefficients.  Analytic continuation's change-level formula
gives the exact Euler factor at one, without any conditionally convergent
`LSeries` identification.  Character nonprincipality and the final real
L-value bound are proved, not assumed.  No primitivity or moment estimate is
asserted here.
-/

namespace PellPaper

open NumberTheorySymbols
open scoped BigOperators

noncomputable section

/-- The literal change of level to `2 * D`, with all even coefficients zero. -/
def oddifiedKroneckerCharacterAtPositiveFundamentalDiscriminant
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) : DirichletCharacter ℂ (2 * D) :=
  DirichletCharacter.changeLevel (D.dvd_mul_left 2)
    (kroneckerCharacterAtPositiveFundamentalDiscriminantC D hD)

/-- Oddification preserves nonprincipality of the actual selected character. -/
theorem oddifiedKroneckerCharacterAtPositiveFundamentalDiscriminant_ne_one
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) :
    oddifiedKroneckerCharacterAtPositiveFundamentalDiscriminant D hD ≠ 1 := by
  let _ : NeZero (2 * D) := ⟨by have := hD.1; omega⟩
  intro h
  exact kroneckerCharacterAtPositiveFundamentalDiscriminantC_ne_one D hD
    ((DirichletCharacter.changeLevel_eq_one_iff (D.dvd_mul_left 2)).mp h)

private theorem changeLevel_two_mul_apply_of_odd
    (D n : ℕ) (χ : DirichletCharacter ℂ D) (hnodd : Odd n) :
    DirichletCharacter.changeLevel (D.dvd_mul_left 2) χ n = χ n := by
  by_cases hn : n.Coprime D
  · have hcop : n.Coprime (2 * D) := hnodd.coprime_two_right.mul_right hn
    have h := DirichletCharacter.changeLevel_eq_cast_of_dvd χ (D.dvd_mul_left 2)
      (ZMod.unitOfCoprime n hcop)
    simpa only [ZMod.coe_unitOfCoprime, ZMod.cast_natCast (D.dvd_mul_left 2)] using h
  · have hnlarge : ¬n.Coprime (2 * D) := fun h =>
      hn (Nat.Coprime.of_dvd_right (D.dvd_mul_left 2) h)
    rw [MulChar.map_nonunit _ (by simpa only [ZMod.isUnit_iff_coprime] using hnlarge),
      MulChar.map_nonunit _ (by simpa only [ZMod.isUnit_iff_coprime] using hn)]

/-- Every odd coefficient is the numerator-side Jacobi symbol, without a
coprimality restriction. -/
theorem oddifiedKroneckerCharacterAtPositiveFundamentalDiscriminant_apply_eq_jacobi_of_odd
    (D n : ℕ) (hD : PositiveFundamentalDiscriminant D) (hnodd : Odd n) :
    oddifiedKroneckerCharacterAtPositiveFundamentalDiscriminant D hD n =
      (J((D : ℤ) | n) : ℂ) := by
  unfold oddifiedKroneckerCharacterAtPositiveFundamentalDiscriminant
  rw [changeLevel_two_mul_apply_of_odd D n _ hnodd]
  exact kroneckerCharacterAtPositiveFundamentalDiscriminantC_apply_eq_jacobi_of_odd
    D n hD hnodd

/-- Every even coefficient, including the zeroth, is zero. -/
theorem oddifiedKroneckerCharacterAtPositiveFundamentalDiscriminant_apply_eq_zero_of_even
    (D n : ℕ) (hD : PositiveFundamentalDiscriminant D) (hneven : Even n) :
    oddifiedKroneckerCharacterAtPositiveFundamentalDiscriminant D hD n = 0 := by
  apply MulChar.map_nonunit
  rw [ZMod.isUnit_iff_coprime]
  intro hn
  have hcop : n.Coprime 2 := Nat.Coprime.of_dvd_right (dvd_mul_right 2 D) hn
  exact (Nat.not_odd_iff_even.mpr hneven) hcop.odd_of_right

/-- A single coefficient formula for the actual oddified character. -/
theorem oddifiedKroneckerCharacterAtPositiveFundamentalDiscriminant_apply_natCast
    (D n : ℕ) (hD : PositiveFundamentalDiscriminant D) :
    oddifiedKroneckerCharacterAtPositiveFundamentalDiscriminant D hD n =
      if Odd n then (J((D : ℤ) | n) : ℂ) else 0 := by
  by_cases hn : Odd n
  · rw [if_pos hn]
    exact oddifiedKroneckerCharacterAtPositiveFundamentalDiscriminant_apply_eq_jacobi_of_odd
      D n hD hn
  · rw [if_neg hn]
    exact oddifiedKroneckerCharacterAtPositiveFundamentalDiscriminant_apply_eq_zero_of_even
      D n hD (Nat.not_odd_iff_even.mp hn)

private theorem changeLevel_two_mul_eulerFactor_one
    (D : ℕ) [NeZero D] (χ : DirichletCharacter ℂ D) :
    (∏ p ∈ (2 * D).primeFactors, (1 - χ p * (p : ℂ) ^ (-(1 : ℂ)))) =
      1 - χ 2 / 2 := by
  have htwo : 2 ∈ (2 * D).primeFactors :=
    Nat.prime_two.mem_primeFactors (dvd_mul_right 2 D)
      (mul_ne_zero (by norm_num) (NeZero.ne D))
  calc
    (∏ p ∈ (2 * D).primeFactors, (1 - χ p * (p : ℂ) ^ (-(1 : ℂ)))) =
        1 - χ 2 * (2 : ℂ) ^ (-(1 : ℂ)) := by
      apply Finset.prod_eq_single 2
      · intro p hp hpne
        have hpprime := Nat.prime_of_mem_primeFactors hp
        have hpdiv : p ∣ D := (hpprime.dvd_mul.mp (Nat.dvd_of_mem_primeFactors hp)).resolve_left
          (fun h => hpne ((Nat.prime_dvd_prime_iff_eq hpprime Nat.prime_two).mp h))
        rw [dirichletCharacter_apply_prime_eq_zero_of_dvd_level χ hpprime hpdiv]
        simp only [zero_mul, sub_zero]
      · exact fun h => (h htwo).elim
    _ = 1 - χ 2 / 2 := by rw [Complex.cpow_neg_one, div_eq_mul_inv]

/-- The exact odd Euler-factor identity for the actual analytic L-functions
at one.  Nonprincipality is supplied by the selected character theorem. -/
theorem oddifiedKroneckerCharacterAtPositiveFundamentalDiscriminant_LFunction_one
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) :
    let _ : NeZero D := ⟨by have := hD.1; omega⟩
    let _ : NeZero (2 * D) := ⟨by have := hD.1; omega⟩
    DirichletCharacter.LFunction
        (oddifiedKroneckerCharacterAtPositiveFundamentalDiscriminant D hD) 1 =
      (1 - kroneckerCharacterAtPositiveFundamentalDiscriminantC D hD 2 / 2) *
        DirichletCharacter.LFunction
          (kroneckerCharacterAtPositiveFundamentalDiscriminantC D hD) 1 := by
  let _ : NeZero D := ⟨by have := hD.1; omega⟩
  let _ : NeZero (2 * D) := ⟨by have := hD.1; omega⟩
  dsimp only
  unfold oddifiedKroneckerCharacterAtPositiveFundamentalDiscriminant
  rw [DirichletCharacter.LFunction_changeLevel _ _
    (.inl (kroneckerCharacterAtPositiveFundamentalDiscriminantC_ne_one D hD)),
    changeLevel_two_mul_eulerFactor_one, mul_comm]

/-- The selected real L-value is controlled by twice the absolute real part
of its actual oddified analytic L-value. -/
theorem selectedKroneckerLValue_le_two_mul_abs_re_oddifiedLFunction_one
    (D : ℕ) (hD : PositiveFundamentalDiscriminant D) :
    let _ : NeZero (2 * D) := ⟨by have := hD.1; omega⟩
    selectedKroneckerLValue D ≤
      2 * |(DirichletCharacter.LFunction
        (oddifiedKroneckerCharacterAtPositiveFundamentalDiscriminant D hD) 1).re| := by
  let _ : NeZero D := ⟨by have := hD.1; omega⟩
  let _ : NeZero (2 * D) := ⟨by have := hD.1; omega⟩
  dsimp only
  have hid := congrArg Complex.re
    (oddifiedKroneckerCharacterAtPositiveFundamentalDiscriminant_LFunction_one D hD)
  have him := kroneckerCharacterAtPositiveFundamentalDiscriminantC_apply_im D hD 2
  have hnorm := (kroneckerCharacterAtPositiveFundamentalDiscriminantC D hD).norm_le_one 2
  have hre := Complex.re_le_norm
    (kroneckerCharacterAtPositiveFundamentalDiscriminantC D hD 2)
  have hpos := (selectedKroneckerLValue_pos D hD).le
  have hval : selectedKroneckerLValue D = (DirichletCharacter.LFunction
      (kroneckerCharacterAtPositiveFundamentalDiscriminantC D hD) 1).re := by
    simp only [selectedKroneckerLValue, dif_pos hD]
  simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.sub_im,
    Complex.one_im, Complex.div_ofNat_re, Complex.div_ofNat_im, him,
    zero_div, sub_self, zero_mul, sub_zero] at hid
  rw [← hval] at hid
  have habs := le_abs_self ((DirichletCharacter.LFunction
    (oddifiedKroneckerCharacterAtPositiveFundamentalDiscriminant D hD) 1).re)
  nlinarith [mul_nonneg hpos (sub_nonneg.mpr (hre.trans hnorm))]

end
end PellPaper
