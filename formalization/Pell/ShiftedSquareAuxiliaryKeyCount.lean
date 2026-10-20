import Pell.AuxiliaryParabolaDivisorSubpower
import Pell.ShiftedSquareContentScaleBounds
import Mathlib.Tactic

/-!
# Finite divisor gate for shifted-square auxiliary indices

For a fixed Minkowski index `C₀` and coefficient `bζ ∈ {1,2}`, the
normalization contents satisfy `r^2 * ell ∣ C₀^2 * |bζ|`.  This module
packages those four scalar parameters in one literal finite set and proves
both the package-membership theorem and a subpower cardinality bound.

This is scalar bookkeeping only.  It does not choose coordinate packages,
localize embedding ratios, or count shifted-square points.
-/

namespace PellPaper

noncomputable section

/-- The scalar parameters retained before the coordinate-cell decomposition. -/
structure ShiftedSquareAuxiliaryKey where
  C₀ : ℕ
  r : ℕ
  ell : ℕ
  bζ : ℤ
deriving DecidableEq

/-- The only two coefficient values produced by the parity normalization. -/
def shiftedSquareBζValues : Finset ℤ := {1, 2}

/-- All scalar keys with `1 ≤ C₀ ≤ R` and the exact divisor restriction. -/
def shiftedSquareAuxiliaryKeys (R : ℕ) : Finset ShiftedSquareAuxiliaryKey :=
  (Finset.Icc 1 R).biUnion fun C₀ =>
    shiftedSquareBζValues.biUnion fun bζ =>
      (specialParabolaDenominatorPairs (C₀ ^ 2 * bζ.natAbs)).image fun p =>
        ⟨C₀, p.1, p.2, bζ⟩

@[simp] theorem mem_shiftedSquareBζValues {bζ : ℤ} :
    bζ ∈ shiftedSquareBζValues ↔ bζ = 1 ∨ bζ = 2 := by
  simp [shiftedSquareBζValues]

/-- Every simultaneous normalized package whose Minkowski index is at most
`R` supplies a member of the literal scalar gate. -/
theorem shiftedSquareAuxiliaryKey_mem
    {a : ℤ} {d w n R : ℕ}
    [Fact (rationalQuadraticAlgebraNoRationalRoot (-a))]
    {heq : (d : ℤ) ^ 2 * (w : ℤ) = (n : ℤ) ^ 2 + a}
    (P : ShiftedSquareSimultaneousNormalizedCoordinatePackage heq)
    (hC₀ : P.minkowski.C₀ ≤ R) :
    (⟨P.minkowski.C₀, P.r, P.ell, P.bζ⟩ : ShiftedSquareAuxiliaryKey) ∈
      shiftedSquareAuxiliaryKeys R := by
  apply Finset.mem_biUnion.mpr
  refine ⟨P.minkowski.C₀, Finset.mem_Icc.mpr ⟨P.minkowski.C₀_pos, hC₀⟩, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨P.bζ, mem_shiftedSquareBζValues.mpr P.bζ_eq_one_or_two, ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨(P.r, P.ell), ?_, rfl⟩
  have hright : 0 < P.minkowski.C₀ ^ 2 * P.bζ.natAbs :=
    Nat.mul_pos (pow_pos P.minkowski.C₀_pos 2)
      (Int.natAbs_pos.mpr P.bζ_ne_zero)
  exact (mem_specialParabolaDenominatorPairs_iff hright.ne').mpr
    ⟨P.r_pos, P.ell_pos, shiftedSquare_contentProduct_dvd P⟩

/-- Union subadditivity exposes the exact divisor-pair sum controlling the
number of scalar keys. -/
theorem card_shiftedSquareAuxiliaryKeys_le_divisorPairSum (R : ℕ) :
    (shiftedSquareAuxiliaryKeys R).card ≤
      ∑ C₀ ∈ Finset.Icc 1 R, ∑ bζ ∈ shiftedSquareBζValues,
        (specialParabolaDenominatorPairs (C₀ ^ 2 * bζ.natAbs)).card := by
  unfold shiftedSquareAuxiliaryKeys
  refine (Finset.card_biUnion_le).trans ?_
  apply Finset.sum_le_sum
  intro C₀ hC₀
  refine (Finset.card_biUnion_le).trans ?_
  apply Finset.sum_le_sum
  intro bζ hbζ
  exact Finset.card_image_le

/-- A uniform positive-power bound for the scalar gate.  The leading factor
`R` is the genuine range of `C₀`; the remaining divisor choices cost only an
arbitrarily small positive power of `2 R^2`. -/
theorem exists_pos_card_shiftedSquareAuxiliaryKeys_le_rpow
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℕ, 1 ≤ R →
      ((shiftedSquareAuxiliaryKeys R).card : ℝ) ≤
        2 * C * (R : ℝ) * ((2 * R ^ 2 : ℕ) : ℝ) ^ ε := by
  obtain ⟨C, hC, hpair⟩ :=
    exists_pos_card_specialParabolaDenominatorPairs_le_rpow ε hε
  refine ⟨C, hC, ?_⟩
  intro R hR
  have hsumNat := card_shiftedSquareAuxiliaryKeys_le_divisorPairSum R
  have hsum : ((shiftedSquareAuxiliaryKeys R).card : ℝ) ≤
      ∑ C₀ ∈ Finset.Icc 1 R, ∑ bζ ∈ shiftedSquareBζValues,
        ((specialParabolaDenominatorPairs
          (C₀ ^ 2 * bζ.natAbs)).card : ℝ) := by
    exact_mod_cast hsumNat
  have hterm (C₀ : ℕ) (hC₀ : C₀ ∈ Finset.Icc 1 R)
      (bζ : ℤ) (hbζ : bζ ∈ shiftedSquareBζValues) :
      ((specialParabolaDenominatorPairs
          (C₀ ^ 2 * bζ.natAbs)).card : ℝ) ≤
        C * ((2 * R ^ 2 : ℕ) : ℝ) ^ ε := by
    have hC₀pos : 0 < C₀ := (Finset.mem_Icc.mp hC₀).1
    have hb : bζ = 1 ∨ bζ = 2 := mem_shiftedSquareBζValues.mp hbζ
    have hbpos : 0 < bζ.natAbs := by rcases hb with rfl | rfl <;> norm_num
    have hnpos : 0 < C₀ ^ 2 * bζ.natAbs :=
      Nat.mul_pos (pow_pos hC₀pos 2) hbpos
    have hC₀R : C₀ ≤ R := (Finset.mem_Icc.mp hC₀).2
    have hbTwo : bζ.natAbs ≤ 2 := by rcases hb with rfl | rfl <;> norm_num
    have hnle : C₀ ^ 2 * bζ.natAbs ≤ 2 * R ^ 2 := by
      nlinarith [Nat.pow_le_pow_left hC₀R 2]
    have hcast : ((C₀ ^ 2 * bζ.natAbs : ℕ) : ℝ) ≤
        ((2 * R ^ 2 : ℕ) : ℝ) := by exact_mod_cast hnle
    exact (hpair _ hnpos).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) hcast hε.le) hC.le)
  calc
    ((shiftedSquareAuxiliaryKeys R).card : ℝ) ≤
        ∑ C₀ ∈ Finset.Icc 1 R, ∑ bζ ∈ shiftedSquareBζValues,
          ((specialParabolaDenominatorPairs
            (C₀ ^ 2 * bζ.natAbs)).card : ℝ) := hsum
    _ ≤ ∑ _C₀ ∈ Finset.Icc 1 R, ∑ _bζ ∈ shiftedSquareBζValues,
          C * ((2 * R ^ 2 : ℕ) : ℝ) ^ ε := by
      apply Finset.sum_le_sum
      intro C₀ hC₀
      apply Finset.sum_le_sum
      intro bζ hbζ
      exact hterm C₀ hC₀ bζ hbζ
    _ = 2 * C * (R : ℝ) * ((2 * R ^ 2 : ℕ) : ℝ) ^ ε := by
      rw [Finset.sum_const, Finset.sum_const]
      simp [shiftedSquareBζValues, Nat.card_Icc]
      ring

end

end PellPaper
