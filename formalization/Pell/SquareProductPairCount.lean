import Pell.SquareProductReciprocalDiagonal
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Counting pairs with square product

This is the elementary diagonal count in the proof of the
Friedlander--Iwaniec bilinear Jacobi-symbol estimate (Lemma 2, Section 9,
p. 112 of *Ternary quadratic forms with rational zeros*, JTNB 22 (2010),
DOI 10.5802/jtnb.706).  A pair of positive
integers whose product is a square has a common squarefree part, hence is
covered by triples `(s,a,b)` with `s*a^2` and `s*b^2` in the original box.
For each fixed `s`, there are at most `N / s` choices of `(a,b)`, and summing
over `s` gives the sharp `N (1 + log N)` envelope used in the paper.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- Positive pairs in the square box whose product is a square. -/
def squareProductPairsUpTo (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter
    (fun p ↦ IsSquare (p.1 * p.2))

private def commonSquarePartMap (t : ℕ × ℕ × ℕ) : ℕ × ℕ :=
  (t.1 * t.2.1 ^ 2, t.1 * t.2.2 ^ 2)

private def commonSquarePartBox (N : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.Icc 1 N).product
    ((Finset.Icc 1 N).product (Finset.Icc 1 N))).filter
      (fun t ↦ t.1 * t.2.1 ^ 2 ≤ N ∧ t.1 * t.2.2 ^ 2 ≤ N)

private theorem card_commonSquarePartBox_eq (N : ℕ) :
    (commonSquarePartBox N).card =
      ∑ s ∈ Finset.Icc 1 N,
        ((Finset.Icc 1 N).filter (fun a ↦ s * a ^ 2 ≤ N)).card ^ 2 := by
  classical
  unfold commonSquarePartBox
  simp only [Finset.card_filter, Finset.product_eq_sprod, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro s hs
  simp only [pow_two, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hsa : s * a ^ 2 ≤ N <;>
    by_cases hsb : s * b ^ 2 ≤ N <;>
      simp only [pow_two] at hsa hsb ⊢ <;> simp [hsa, hsb]

private theorem filtered_commonSquarePart_card_sq_le_div
    (N s : ℕ) (hs : s ∈ Finset.Icc 1 N) :
    ((Finset.Icc 1 N).filter (fun a ↦ s * a ^ 2 ≤ N)).card ^ 2 ≤
      N / s := by
  obtain ⟨hs0, _hsN⟩ := Finset.mem_Icc.mp hs
  have hset :
      (Finset.Icc 1 N).filter (fun a ↦ s * a ^ 2 ≤ N) =
        Finset.Icc 1 (Nat.sqrt (N / s)) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_Icc]
    have hsqrtN : Nat.sqrt (N / s) ≤ N :=
      (Nat.sqrt_le_self (N / s)).trans (Nat.div_le_self N s)
    constructor
    · rintro ⟨⟨ha0, _haN⟩, hsa⟩
      refine ⟨ha0, Nat.le_sqrt'.2 ?_⟩
      exact (Nat.le_div_iff_mul_le hs0).2
        (by simpa [Nat.mul_comm] using hsa)
    · rintro ⟨ha0, hasqrt⟩
      refine ⟨⟨ha0, hasqrt.trans hsqrtN⟩, ?_⟩
      have haDiv : a ^ 2 ≤ N / s := Nat.le_sqrt'.1 hasqrt
      simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hs0).1 haDiv
  rw [hset]
  simp
  exact Nat.sqrt_le' (N / s)

private theorem card_commonSquarePartBox_cast_le (N : ℕ) :
    ((commonSquarePartBox N).card : ℝ) ≤
      (N : ℝ) * (1 + Real.log (N : ℝ)) := by
  rw [card_commonSquarePartBox_eq, Nat.cast_sum]
  calc
    ∑ s ∈ Finset.Icc 1 N,
        ((((Finset.Icc 1 N).filter
          (fun a ↦ s * a ^ 2 ≤ N)).card ^ 2 : ℕ) : ℝ) ≤
        ∑ s ∈ Finset.Icc 1 N, ((N / s : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro s hs
      exact_mod_cast filtered_commonSquarePart_card_sq_le_div N s hs
    _ ≤ ∑ s ∈ Finset.Icc 1 N, (N : ℝ) / (s : ℝ) := by
      gcongr with s hs
      exact (Nat.cast_div_le : ((N / s : ℕ) : ℝ) ≤ (N : ℝ) / (s : ℝ))
    _ = (N : ℝ) * (harmonic N : ℝ) := by
      rw [harmonic_eq_sum_Icc]
      simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
        Finset.mul_sum, div_eq_mul_inv]
    _ ≤ (N : ℝ) * (1 + Real.log (N : ℝ)) := by
      exact mul_le_mul_of_nonneg_left (harmonic_le_one_add_log N)
        (Nat.cast_nonneg N)

/-- The square-product diagonal in `[1,N]^2` has the correct-order explicit
uniform bound
`N (1 + log N)`.  This is the diagonal count used in the
Friedlander--Iwaniec bilinear Jacobi-symbol estimate. -/
theorem card_squareProductPairsUpTo_cast_le (N : ℕ) :
    ((squareProductPairsUpTo N).card : ℝ) ≤
      (N : ℝ) * (1 + Real.log (N : ℝ)) := by
  classical
  have hcover : squareProductPairsUpTo N ⊆
      (commonSquarePartBox N).image commonSquarePartMap := by
    intro p hp
    obtain ⟨hpbox, hsq⟩ := Finset.mem_filter.mp hp
    obtain ⟨hnmem, hmmem⟩ := Finset.mem_product.mp hpbox
    obtain ⟨hn, hnN⟩ := Finset.mem_Icc.mp hnmem
    obtain ⟨hm, hmN⟩ := Finset.mem_Icc.mp hmmem
    obtain ⟨s, a, b, hs, ha, hb, _hsfree, hna, hmb⟩ :=
      exists_common_squarefree_part_of_isSquare_mul p.1 p.2 hn hm hsq
    have hsLeN : s ≤ N := by
      exact (Nat.le_of_dvd hn ⟨a ^ 2, hna⟩).trans hnN
    have haDvd : a ∣ p.1 := by
      refine ⟨s * a, ?_⟩
      rw [hna]
      ring
    have hbDvd : b ∣ p.2 := by
      refine ⟨s * b, ?_⟩
      rw [hmb]
      ring
    have haLeN : a ≤ N := (Nat.le_of_dvd hn haDvd).trans hnN
    have hbLeN : b ≤ N := (Nat.le_of_dvd hm hbDvd).trans hmN
    apply Finset.mem_image.mpr
    refine ⟨(s, a, b), ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨
        Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hs, hsLeN⟩,
          Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨ha, haLeN⟩,
            Finset.mem_Icc.mpr ⟨hb, hbLeN⟩⟩⟩,
        ⟨hna ▸ hnN, hmb ▸ hmN⟩⟩
    · exact Prod.ext hna.symm hmb.symm
  have hcardNat : (squareProductPairsUpTo N).card ≤
      (commonSquarePartBox N).card := by
    exact (Finset.card_le_card hcover).trans (Finset.card_image_le)
  have hcardReal : ((squareProductPairsUpTo N).card : ℝ) ≤
      ((commonSquarePartBox N).card : ℝ) := by
    exact_mod_cast hcardNat
  exact hcardReal.trans (card_commonSquarePartBox_cast_le N)

end

end PellPaper
