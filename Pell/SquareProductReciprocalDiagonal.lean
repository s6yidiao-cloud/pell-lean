import Mathlib.Data.Nat.Squarefree
import Mathlib.Analysis.PSeries

/-!
# A uniform reciprocal bound on the square-product diagonal

Two positive naturals with square product share a squarefree part.  Their
representations by this common part and two positive square roots cover the
actual finite square-product diagonal by a positive triple box.  Enlarging
to this box bounds its reciprocal sum by three inverse-square sums, hence
by eight, uniformly even at the empty cutoff zero.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- A square product forces the same squarefree part in both positive
factors.  The representation is proved from their actual factorizations. -/
theorem exists_common_squarefree_part_of_isSquare_mul
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (hsq : IsSquare (n * m)) :
    ∃ s a b : ℕ, 0 < s ∧ 0 < a ∧ 0 < b ∧ Squarefree s ∧
      n = s * a ^ 2 ∧ m = s * b ^ 2 := by
  obtain ⟨s, a, hs, ha, hna, hsf⟩ := Nat.sq_mul_squarefree_of_pos hn
  obtain ⟨t, b, ht, hb, hmb, htf⟩ := Nat.sq_mul_squarefree_of_pos hm
  obtain ⟨k, hk⟩ := hsq.exists_sq
  have hst : s = t := by
    apply Nat.eq_of_factorization_eq hs.ne' ht.ne'
    intro p
    have hnf : n.factorization p = 2 * a.factorization p + s.factorization p := by
      rw [← hna, Nat.factorization_mul (pow_ne_zero 2 ha.ne') hs.ne',
        Nat.factorization_pow, Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul]
      norm_num
    have hmf : m.factorization p = 2 * b.factorization p + t.factorization p := by
      rw [← hmb, Nat.factorization_mul (pow_ne_zero 2 hb.ne') ht.ne',
        Nat.factorization_pow, Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul]
      norm_num
    have heq := congrArg (fun u : ℕ => u.factorization p) hk
    simp only [Nat.factorization_mul hn.ne' hm.ne', Nat.factorization_pow,
      Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul] at heq
    rw [hnf, hmf] at heq
    norm_num at heq
    have hsbound := hsf.natFactorization_le_one p
    have htbound := htf.natFactorization_le_one p
    omega
  subst t
  exact ⟨s, a, b, hs, ha, hb, hsf,
    hna.symm.trans (mul_comm _ _), hmb.symm.trans (mul_comm _ _)⟩

private theorem coordinates_le_mul_sq
    {s a : ℕ} (hs : 0 < s) (ha : 0 < a) : s ≤ s * a ^ 2 ∧ a ≤ s * a ^ 2 := by
  have haone : 1 ≤ a := ha
  have hsone : 1 ≤ s := hs
  have hasq : a ≤ a ^ 2 := le_self_pow haone (by decide : 2 ≠ 0)
  constructor
  · simpa only [mul_one] using Nat.mul_le_mul_left s (haone.trans hasq)
  · exact hasq.trans (by simpa only [one_mul] using Nat.mul_le_mul_right (a ^ 2) hsone)

private theorem sum_Icc_inv_sq_le_two (N : ℕ) :
    (∑ k ∈ Finset.Icc 1 N, ((k : ℝ) ^ 2)⁻¹) ≤ 2 := by
  have hset : Finset.Icc 1 N = Finset.Ioo 0 (N + 1) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ioo]
    omega
  rw [hset]
  simpa using (sum_Ioo_inv_sq_le (α := ℝ) 0 (N + 1))

/-- The actual square-product reciprocal diagonal has an absolute bound
eight for every natural cutoff, including zero. -/
theorem sum_reciprocal_mul_filter_isSquare_le_eight (N : ℕ) :
    (∑ nm ∈ ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter
        (fun nm => IsSquare (nm.1 * nm.2)),
      1 / ((nm.1 : ℝ) * nm.2)) ≤ 8 := by
  classical
  let I := Finset.Icc 1 N
  let A := (I.product I).filter (fun nm => IsSquare (nm.1 * nm.2))
  let B := I.product (I.product I)
  let F : ℕ × ℕ × ℕ → ℕ × ℕ := fun t => (t.1 * t.2.1 ^ 2, t.1 * t.2.2 ^ 2)
  let w : ℕ × ℕ → ℝ := fun nm => 1 / ((nm.1 : ℝ) * nm.2)
  have hcover : A ⊆ B.image F := by
    intro nm hnm
    obtain ⟨hnm, hsq⟩ := Finset.mem_filter.mp hnm
    obtain ⟨hn, hm⟩ := Finset.mem_product.mp hnm
    obtain ⟨hnpos, hnN⟩ := Finset.mem_Icc.mp hn
    obtain ⟨hmpos, hmN⟩ := Finset.mem_Icc.mp hm
    obtain ⟨s, a, b, hs, ha, hb, _hsf, hna, hmb⟩ :=
      exists_common_squarefree_part_of_isSquare_mul nm.1 nm.2 hnpos hmpos hsq
    have hsa := coordinates_le_mul_sq hs ha
    have hsb := coordinates_le_mul_sq hs hb
    have hsN : s ≤ N := hsa.1.trans (hna ▸ hnN)
    have haN : a ≤ N := hsa.2.trans (hna ▸ hnN)
    have hbN : b ≤ N := hsb.2.trans (hmb ▸ hmN)
    apply Finset.mem_image.mpr
    refine ⟨(s, a, b), ?_, ?_⟩
    · exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hs, hsN⟩,
        Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨ha, haN⟩,
          Finset.mem_Icc.mpr ⟨hb, hbN⟩⟩⟩
    · exact Prod.ext hna.symm hmb.symm
  have hweight (t : ℕ × ℕ × ℕ) : w (F t) =
      ((t.1 : ℝ) ^ 2)⁻¹ * ((t.2.1 : ℝ) ^ 2)⁻¹ * ((t.2.2 : ℝ) ^ 2)⁻¹ := by
    dsimp only [w, F]
    simp only [Nat.cast_mul, one_div, pow_two, mul_inv_rev]
    ring
  have htriple : (∑ t ∈ B, w (F t)) =
      (∑ k ∈ I, ((k : ℝ) ^ 2)⁻¹) ^ 3 := by
    simp_rw [hweight]
    simp only [B, Finset.product_eq_sprod, Finset.sum_product]
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  change (∑ nm ∈ A, w nm) ≤ 8
  calc
    (∑ nm ∈ A, w nm) ≤ ∑ nm ∈ B.image F, w nm :=
      Finset.sum_le_sum_of_subset_of_nonneg hcover (fun nm _ _ => by dsimp [w]; positivity)
    _ ≤ ∑ t ∈ B, w (F t) :=
      Finset.sum_image_le_of_nonneg (fun nm _ => by dsimp [w]; positivity)
    _ = (∑ k ∈ I, ((k : ℝ) ^ 2)⁻¹) ^ 3 := htriple
    _ ≤ (2 : ℝ) ^ 3 := by
      apply pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => by positivity))
      exact sum_Icc_inv_sq_le_two N
    _ = 8 := by norm_num

end
end PellPaper
