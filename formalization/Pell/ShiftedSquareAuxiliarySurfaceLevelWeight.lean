import Pell.Main3LargeAnalyticCellCoordinatePointImage
import Pell.ShiftedSquareAuxiliaryKeyCount
import Pell.DivisorCountSubpower
import Mathlib.Tactic

/-!
# Weighted divisor bound for shifted-square auxiliary surface levels

Exact membership in the scalar auxiliary-key gate forces the surface-level
numerator and denominator to be positive natural numbers, with the latter
dividing the former.  The quotient is therefore positive, and its absolute
value is at most `2 R^2`.  Pointwise divisor subpower and the existing
subpower count for the key gate then bound the sum of divisor weights.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- The surface level of a key in the exact scalar gate is positive, and its
absolute value is at most twice the square of the gate radius. -/
theorem shiftedSquareAuxiliaryKeySurfaceLevel_pos_and_natAbs_le
    {R : ℕ} {key : ShiftedSquareAuxiliaryKey}
    (hkey : key ∈ shiftedSquareAuxiliaryKeys R) :
    0 < shiftedSquareAuxiliaryKeySurfaceLevel key ∧
      (shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs ≤ 2 * R ^ 2 := by
  simp only [shiftedSquareAuxiliaryKeys, Finset.mem_biUnion,
    Finset.mem_image] at hkey
  obtain ⟨C₀, hC₀, bζ, hbζ, p, hp, rfl⟩ := hkey
  rcases p with ⟨r, ell⟩
  have hC₀range := Finset.mem_Icc.mp hC₀
  have hbζCases : bζ = 1 ∨ bζ = 2 :=
    mem_shiftedSquareBζValues.mp hbζ
  have hbζPos : 0 < bζ := by
    rcases hbζCases with rfl | rfl <;> norm_num
  have hbζAbsLe : bζ.natAbs ≤ 2 := by
    rcases hbζCases with rfl | rfl <;> norm_num
  have hnumPos : 0 < C₀ ^ 2 * bζ.natAbs :=
    Nat.mul_pos (pow_pos (by omega) 2) (Int.natAbs_pos.mpr hbζPos.ne')
  have hpData :=
    (mem_specialParabolaDenominatorPairs_iff hnumPos.ne').mp hp
  have hrPos : 0 < r := hpData.1
  have hellPos : 0 < ell := hpData.2.1
  have hdenomPos : 0 < r ^ 2 * ell :=
    Nat.mul_pos (pow_pos hrPos 2) hellPos
  have hdiv : r ^ 2 * ell ∣ C₀ ^ 2 * bζ.natAbs := hpData.2.2
  have hquotientPos : 0 < (C₀ ^ 2 * bζ.natAbs) / (r ^ 2 * ell) :=
    Nat.div_pos (Nat.le_of_dvd hnumPos hdiv) hdenomPos
  have hnumLe : C₀ ^ 2 * bζ.natAbs ≤ 2 * R ^ 2 := by
    have hC₀pow : C₀ ^ 2 ≤ R ^ 2 := Nat.pow_le_pow_left hC₀range.2 2
    nlinarith
  have hquotientLe :
      (C₀ ^ 2 * bζ.natAbs) / (r ^ 2 * ell) ≤ 2 * R ^ 2 :=
    (Nat.div_le_self _ _).trans hnumLe
  have hnumCast :
      ((C₀ ^ 2 * bζ.natAbs : ℕ) : ℤ) = (C₀ : ℤ) ^ 2 * bζ := by
    push_cast
    rw [abs_of_pos hbζPos]
  have hdenomCast :
      ((r ^ 2 * ell : ℕ) : ℤ) = (r : ℤ) ^ 2 * (ell : ℤ) := by
    push_cast
    rfl
  have hlevel :
      shiftedSquareAuxiliaryKeySurfaceLevel ⟨C₀, r, ell, bζ⟩ =
        (((C₀ ^ 2 * bζ.natAbs) / (r ^ 2 * ell) : ℕ) : ℤ) := by
    unfold shiftedSquareAuxiliaryKeySurfaceLevel
    rw [← hnumCast, ← hdenomCast, ← Int.natCast_div]
  rw [hlevel]
  constructor
  · exact_mod_cast hquotientPos
  · simpa only [Int.natAbs_natCast] using hquotientLe

/-- The sum of divisor weights of all exact auxiliary surface levels has the
same genuine linear `R` factor as the key gate and otherwise costs only an
arbitrarily small power. -/
theorem exists_pos_sum_card_divisors_shiftedSquareAuxiliaryKeySurfaceLevel_le_rpow
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℕ, 1 ≤ R →
      ∑ key ∈ shiftedSquareAuxiliaryKeys R,
          (((shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs.divisors.card : ℕ) : ℝ) ≤
        C * (R : ℝ) * ((2 * R ^ 2 : ℕ) : ℝ) ^ (2 * ε) := by
  obtain ⟨Cdiv, hCdiv, hdivisor⟩ :=
    exists_pos_card_divisors_le_rpow ε hε
  obtain ⟨Ckey, hCkey, hkeys⟩ :=
    exists_pos_card_shiftedSquareAuxiliaryKeys_le_rpow ε hε
  refine ⟨2 * Cdiv * Ckey, by positivity, ?_⟩
  intro R hR
  let Z : ℝ := ((2 * R ^ 2 : ℕ) : ℝ)
  have hZpos : 0 < Z := by
    dsimp only [Z]
    exact_mod_cast (show 0 < 2 * R ^ 2 by positivity)
  have hpoint (key : ShiftedSquareAuxiliaryKey)
      (hkey : key ∈ shiftedSquareAuxiliaryKeys R) :
      (((shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs.divisors.card : ℕ) : ℝ) ≤
        Cdiv * Z ^ ε := by
    have hlevel :=
      shiftedSquareAuxiliaryKeySurfaceLevel_pos_and_natAbs_le hkey
    have hnPos : 0 < (shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs :=
      Int.natAbs_pos.mpr hlevel.1.ne'
    have hcast :
        ((shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs : ℝ) ≤ Z := by
      dsimp only [Z]
      exact_mod_cast hlevel.2
    calc
      (((shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs.divisors.card : ℕ) : ℝ) ≤
          Cdiv *
            ((shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs : ℝ) ^ ε :=
        hdivisor _ hnPos
      _ ≤ Cdiv * Z ^ ε :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by positivity) hcast hε.le) hCdiv.le
  have hweightNonneg : 0 ≤ Cdiv * Z ^ ε := by positivity
  calc
    ∑ key ∈ shiftedSquareAuxiliaryKeys R,
        (((shiftedSquareAuxiliaryKeySurfaceLevel key).natAbs.divisors.card : ℕ) : ℝ) ≤
        ∑ _key ∈ shiftedSquareAuxiliaryKeys R, Cdiv * Z ^ ε := by
      exact Finset.sum_le_sum fun key hkey => hpoint key hkey
    _ = ((shiftedSquareAuxiliaryKeys R).card : ℝ) * (Cdiv * Z ^ ε) := by
      simp
    _ ≤ (2 * Ckey * (R : ℝ) * Z ^ ε) * (Cdiv * Z ^ ε) := by
      exact mul_le_mul_of_nonneg_right (hkeys R hR) hweightNonneg
    _ = (2 * Cdiv * Ckey) * (R : ℝ) * Z ^ (2 * ε) := by
      rw [show 2 * ε = ε + ε by ring, Real.rpow_add hZpos]
      ring

end

end PellPaper
