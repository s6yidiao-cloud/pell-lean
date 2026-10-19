import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

/-!
# Exact symmetric integer rectangles

The interval and rectangle describe literal integer points bounded by real
absolute values. Exact cardinalities retain the floor and the added unit.
Only the subsequent multiplicative estimates require halfwidths at least one.
-/

namespace PellPaper

noncomputable section

/-- The integer interval with real halfwidth `t`, empty when `t < 0`. -/
def integerSymmetricInterval (t : ℝ) : Finset ℤ :=
  Finset.Icc (-⌊t⌋) ⌊t⌋

/-- Membership is the literal absolute-value bound, for every real halfwidth. -/
theorem mem_integerSymmetricInterval (t : ℝ) (z : ℤ) :
    z ∈ integerSymmetricInterval t ↔ |(z : ℝ)| ≤ t := by
  rw [integerSymmetricInterval, Finset.mem_Icc, abs_le]
  constructor
  · rintro ⟨hlo, hhi⟩
    have hn : (-(z : ℝ)) ≤ t := by
      simpa only [Int.cast_neg] using
        (Int.le_floor.mp (show -z ≤ ⌊t⌋ by omega))
    exact ⟨by linarith, Int.le_floor.mp hhi⟩
  · rintro ⟨hlo, hhi⟩
    have hn : -z ≤ ⌊t⌋ := Int.le_floor.mpr (by
      simpa only [Int.cast_neg] using (show -(z : ℝ) ≤ t by linarith))
    exact ⟨by omega, Int.le_floor.mpr hhi⟩

/-- The exact cardinality, including empty negative-halfwidth intervals. -/
theorem card_integerSymmetricInterval (t : ℝ) :
    (integerSymmetricInterval t).card = (2 * ⌊t⌋ + 1).toNat := by
  rw [integerSymmetricInterval, Int.card_Icc]
  congr 1
  omega

/-- The interval is exactly a translated finite natural range, with no
discarded floor error or implicit change of endpoints. -/
theorem integerSymmetricInterval_eq_map_range (t : ℝ) :
    integerSymmetricInterval t =
      (Finset.range (2 * ⌊t⌋ + 1).toNat).map
        (Nat.castEmbedding.trans (addLeftEmbedding (-⌊t⌋))) := by
  rw [integerSymmetricInterval, Int.Icc_eq_finset_map]
  congr 2
  omega

/-- Literal integer coordinate vectors in a symmetric real rectangle. -/
def integerSymmetricRectangle (A B : ℝ) : Finset (Fin 2 → ℤ) :=
  ((integerSymmetricInterval A).product (integerSymmetricInterval B)).map
    (finTwoArrowEquiv ℤ).symm.toEmbedding

/-- Both closed coordinate bounds are exact, even for zero or negative widths. -/
theorem mem_integerSymmetricRectangle (A B : ℝ) (v : Fin 2 → ℤ) :
    v ∈ integerSymmetricRectangle A B ↔
      |(v 0 : ℝ)| ≤ A ∧ |(v 1 : ℝ)| ≤ B := by
  simp [integerSymmetricRectangle, Finset.mem_map_equiv,
    mem_integerSymmetricInterval, finTwoArrowEquiv]

/-- The exact product of the two integer interval lengths. -/
theorem card_integerSymmetricRectangle (A B : ℝ) :
    (integerSymmetricRectangle A B).card =
      (2 * ⌊A⌋ + 1).toNat * (2 * ⌊B⌋ + 1).toNat := by
  simp [integerSymmetricRectangle, card_integerSymmetricInterval]

/-- The extra integer endpoint costs at most a factor three when `t ≥ 1`. -/
theorem card_integerSymmetricInterval_le_three_mul {t : ℝ} (ht : 1 ≤ t) :
    ((integerSymmetricInterval t).card : ℝ) ≤ 3 * t := by
  have hf : 0 ≤ ⌊t⌋ := Int.floor_nonneg.mpr (by linarith)
  have hlen : 0 ≤ 2 * ⌊t⌋ + 1 := by omega
  rw [card_integerSymmetricInterval]
  have hcast : (((2 * ⌊t⌋ + 1).toNat : ℤ) : ℝ) = ((2 * ⌊t⌋ + 1 : ℤ) : ℝ) :=
    congrArg (fun z : ℤ => (z : ℝ)) (Int.toNat_of_nonneg hlen)
  rw [Int.cast_natCast] at hcast
  rw [hcast]
  push_cast
  have hfloor := Int.floor_le t
  linarith

/-- The literal integer rectangle has at most nine times its halfwidth product
when both halfwidths are at least one. -/
theorem card_integerSymmetricRectangle_le_nine_mul {A B : ℝ}
    (hA : 1 ≤ A) (hB : 1 ≤ B) :
    ((integerSymmetricRectangle A B).card : ℝ) ≤ 9 * A * B := by
  have ha := card_integerSymmetricInterval_le_three_mul hA
  have hb := card_integerSymmetricInterval_le_three_mul hB
  have hprod := mul_le_mul ha hb (Nat.cast_nonneg _) (by linarith : 0 ≤ 3 * A)
  calc
    ((integerSymmetricRectangle A B).card : ℝ) =
        ((integerSymmetricInterval A).card : ℝ) *
          ((integerSymmetricInterval B).card : ℝ) := by
      simp [integerSymmetricRectangle]
    _ ≤ (3 * A) * (3 * B) := hprod
    _ = 9 * A * B := by ring

end

end PellPaper
