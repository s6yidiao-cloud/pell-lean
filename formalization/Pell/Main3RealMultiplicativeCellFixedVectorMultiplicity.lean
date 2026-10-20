import Pell.RealSquareMapCellPairCover
import Pell.SeparatedRealCenterCounting
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Workspace: fixed-vector multiplicity for real multiplicative cells

This file isolates the scalar packing argument behind the real-place
short-vector incidence estimate.  Squaring and multiplying the actual
multiplicative mesh centers by `M` produces a uniformly separated family.
-/

namespace PellPaper

noncomputable section

/-- The squared multiplicative mesh center in the normalization where
successive indices have absolute separation bounded below independently of
`M`. -/
def realMultiplicativeSquaredNormalizedCenter (M k : ℕ) : ℝ :=
  (M : ℝ) * localRatioMeshStep M ^ (2 * k)

private theorem localRatioMeshStep_one_le (M : ℕ) :
    1 ≤ localRatioMeshStep M := by
  unfold localRatioMeshStep
  have h : (0 : ℝ) ≤ 1 / (M : ℝ) := by positivity
  linarith

theorem localRatioMeshStep_pow_le_nine_of_lt_two_mul
    {M k : ℕ} (_hM : 0 < M) (hk : k < 2 * M) :
    localRatioMeshStep M ^ k ≤ 9 := by
  have hstep : 1 ≤ localRatioMeshStep M := localRatioMeshStep_one_le M
  have hk' : k ≤ 2 * M := by omega
  have hpowMono : localRatioMeshStep M ^ k ≤
      localRatioMeshStep M ^ (2 * M) :=
    pow_le_pow_right₀ hstep hk'
  have hbase : localRatioMeshStep M ^ M ≤ Real.exp 1 := by
    simpa only [localRatioMeshStep, one_div, Nat.cast_ofNat] using
      (Real.one_add_inv_pow_le_exp (n := M))
  have hbaseNonneg : 0 ≤ localRatioMeshStep M ^ M := by positivity
  have hexpNonneg : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  have hsq : (localRatioMeshStep M ^ M) ^ 2 ≤ (Real.exp 1) ^ 2 :=
    pow_le_pow_left₀ hbaseNonneg hbase 2
  have hexpThree : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
  have hexpSq : (Real.exp 1) ^ 2 ≤ (3 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hexpNonneg hexpThree 2
  calc
    localRatioMeshStep M ^ k ≤
        localRatioMeshStep M ^ (2 * M) := hpowMono
    _ = (localRatioMeshStep M ^ M) ^ 2 := by
      rw [show 2 * M = M + M by omega, pow_add, pow_two]
    _ ≤ (Real.exp 1) ^ 2 := hsq
    _ ≤ (3 : ℝ) ^ 2 := hexpSq
    _ = 9 := by norm_num

/-- Distinct natural mesh indices have separation at least two after the
squared normalization. -/
theorem realMultiplicativeSquaredNormalizedCenter_separated
    {M : ℕ} (hM : 0 < M) {k l : ℕ} (hkl : k ≠ l) :
    (2 : ℝ) ≤
      |realMultiplicativeSquaredNormalizedCenter M k -
        realMultiplicativeSquaredNormalizedCenter M l| := by
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  have hMne : (M : ℝ) ≠ 0 := hMreal.ne'
  let t := localRatioMeshStep M
  have ht : 1 ≤ t := by simpa only [t] using localRatioMeshStep_one_le M
  have htpos : 0 < t := zero_lt_one.trans_le ht
  have hmono : Monotone (fun n : ℕ =>
      realMultiplicativeSquaredNormalizedCenter M n) := by
    intro m n hmn
    unfold realMultiplicativeSquaredNormalizedCenter
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ ht (Nat.mul_le_mul_left 2 hmn)) hMreal.le
  have hsucc (n : ℕ) :
      realMultiplicativeSquaredNormalizedCenter M (n + 1) -
          realMultiplicativeSquaredNormalizedCenter M n =
        t ^ (2 * n) * (2 + 1 / (M : ℝ)) := by
    unfold realMultiplicativeSquaredNormalizedCenter
    rw [show 2 * (n + 1) = 2 * n + 2 by omega, pow_add]
    dsimp only [t, localRatioMeshStep]
    field_simp [hMne]
    ring
  have hsuccTwo (n : ℕ) :
      (2 : ℝ) ≤
        realMultiplicativeSquaredNormalizedCenter M (n + 1) -
          realMultiplicativeSquaredNormalizedCenter M n := by
    rw [hsucc]
    have hpow : (1 : ℝ) ≤ t ^ (2 * n) := one_le_pow₀ ht
    have hinv : (0 : ℝ) ≤ 1 / (M : ℝ) :=
      (one_div_pos.mpr hMreal).le
    have hfactor : (2 : ℝ) ≤ 2 + 1 / (M : ℝ) := by linarith
    have hmul := mul_le_mul hpow hfactor
      (by norm_num : (0 : ℝ) ≤ 2)
      (by positivity : (0 : ℝ) ≤ t ^ (2 * n))
    nlinarith
  rcases lt_or_gt_of_ne hkl with hlt | hgt
  · have hstep := hsuccTwo k
    have hrest := hmono (Nat.succ_le_of_lt hlt)
    have hdiff : (2 : ℝ) ≤
        realMultiplicativeSquaredNormalizedCenter M l -
          realMultiplicativeSquaredNormalizedCenter M k := by linarith
    rw [abs_sub_comm]
    exact hdiff.trans (le_abs_self _)
  · have hstep := hsuccTwo l
    have hrest := hmono (Nat.succ_le_of_lt hgt)
    have hdiff : (2 : ℝ) ≤
        realMultiplicativeSquaredNormalizedCenter M k -
          realMultiplicativeSquaredNormalizedCenter M l := by linarith
    exact hdiff.trans (le_abs_self _)

/-- A fixed nonzero vector can satisfy the real-cell linearized target
condition for only `O(1 + H/r)` multiplicative mesh positions.  The bound is
uniform in the mesh size `M`; `A` and `B` are the two components of the
vector at the left endpoint of one annular dyadic scale. -/
theorem card_realMultiplicativeMeshIndices_of_fixedVector_le
    {M : ℕ} (hM : 0 < M) {A B H tau : ℝ}
    (hH : 0 ≤ H) (htauLower : (1 / 2 : ℝ) ≤ tau)
    (htauUpper : tau ≤ 3)
    (hr : 0 < max |A| |B|)
    (J : Finset ℕ) (hJ : J ⊆ Finset.range (2 * M))
    (hnear : ∀ k ∈ J,
      |tau * (localRatioMeshStep M ^ k * A) -
          B / localRatioMeshStep M ^ k| ≤ H / (M : ℝ)) :
    (J.card : ℝ) ≤ 1 + 9000 * H / max |A| |B| := by
  classical
  let t : ℝ := localRatioMeshStep M
  let r : ℝ := max |A| |B|
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  have hMne : (M : ℝ) ≠ 0 := hMreal.ne'
  have ht : 1 ≤ t := by simpa only [t] using localRatioMeshStep_one_le M
  have htpos : 0 < t := zero_lt_one.trans_le ht
  have hrpos : 0 < r := by simpa only [r] using hr
  have htauPos : 0 < tau := (by norm_num : (0 : ℝ) < 1 / 2).trans_le htauLower
  have hscaledNear : ∀ k ∈ J,
      |tau * A * t ^ (2 * k) - B| ≤ 9 * H / (M : ℝ) := by
    intro k hk
    have hkRange : k < 2 * M := Finset.mem_range.mp (hJ hk)
    have htu : t ^ k ≤ 9 := by
      simpa only [t] using
        localRatioMeshStep_pow_le_nine_of_lt_two_mul hM hkRange
    have htku : 0 ≤ t ^ k := by positivity
    have hn := hnear k hk
    have hid :
        |tau * A * t ^ (2 * k) - B| =
          t ^ k *
            |tau * (t ^ k * A) - B / t ^ k| := by
      rw [show 2 * k = k + k by omega, pow_add]
      calc
        |tau * A * (t ^ k * t ^ k) - B| =
            |t ^ k * (tau * (t ^ k * A) - B / t ^ k)| := by
          congr 1
          field_simp [ne_of_gt (pow_pos htpos k)]
        _ = |t ^ k| * |tau * (t ^ k * A) - B / t ^ k| :=
          abs_mul _ _
        _ = t ^ k * |tau * (t ^ k * A) - B / t ^ k| := by
          rw [abs_of_nonneg htku]
    rw [hid]
    calc
      t ^ k * |tau * (t ^ k * A) - B / t ^ k| ≤
          t ^ k * (H / (M : ℝ)) :=
        mul_le_mul_of_nonneg_left (by simpa only [t] using hn) htku
      _ ≤ 9 * (H / (M : ℝ)) := by
        exact mul_le_mul_of_nonneg_right htu (div_nonneg hH hMreal.le)
      _ = 9 * H / (M : ℝ) := by ring
  by_cases hlarge : r ≤ 500 * |A|
  · have hApos : 0 < |A| := by
      by_contra hnot
      have hAzero : |A| = 0 := le_antisymm (le_of_not_gt hnot) (abs_nonneg A)
      rw [hAzero, mul_zero] at hlarge
      exact (not_lt_of_ge hlarge) hrpos
    let z : ℕ → ℝ := fun k => tau * A * t ^ (2 * k)
    let sep : ℝ := |A| / (M : ℝ)
    have hsep : 0 < sep := div_pos hApos hMreal
    have hbounds : ∀ k ∈ J,
        B - 9 * H / (M : ℝ) ≤ z k ∧
          z k ≤ B + 9 * H / (M : ℝ) := by
      intro k hk
      have hkNear := hscaledNear k hk
      rw [abs_le] at hkNear
      dsimp only [z]
      constructor <;> linarith
    have hseparated : ∀ k ∈ J, ∀ l ∈ J, k ≠ l →
        sep ≤ |z k - z l| := by
      intro k _hk l _hl hkl
      have hnormSep :=
        realMultiplicativeSquaredNormalizedCenter_separated hM hkl
      have hcenterEq (n : ℕ) :
          z n = (tau * A / (M : ℝ)) *
            realMultiplicativeSquaredNormalizedCenter M n := by
        dsimp only [z, realMultiplicativeSquaredNormalizedCenter]
        field_simp [hMne]
        ring
      rw [hcenterEq k, hcenterEq l, ← mul_sub, abs_mul]
      have hcoeff :
          |tau * A / (M : ℝ)| ≥ |A| / (2 * (M : ℝ)) := by
        rw [abs_div, abs_mul, abs_of_pos hMreal,
          abs_of_pos htauPos]
        rw [ge_iff_le]
        apply (le_div_iff₀ hMreal).2
        field_simp [hMne]
        nlinarith [abs_nonneg A]
      calc
        sep = (|A| / (2 * (M : ℝ))) * 2 := by
          dsimp only [sep]
          field_simp [hMne]
        _ ≤ |tau * A / (M : ℝ)| *
            |realMultiplicativeSquaredNormalizedCenter M k -
              realMultiplicativeSquaredNormalizedCenter M l| :=
          mul_le_mul hcoeff hnormSep (by norm_num)
            (abs_nonneg _)
    have hpack := card_le_one_add_div_of_separated_real_centers
      J z (B - 9 * H / (M : ℝ)) (B + 9 * H / (M : ℝ)) sep
      hsep (by
        have hx : 0 ≤ 9 * H / (M : ℝ) := by positivity
        linarith) hbounds hseparated
    have hratio : 18 * H / |A| ≤ 9000 * H / r := by
      have hden : 0 < 500 * |A| := mul_pos (by norm_num) hApos
      apply (div_le_div_iff₀ hApos hrpos).2
      have hrle : r ≤ 500 * |A| := hlarge
      nlinarith
    calc
      (J.card : ℝ) ≤
          1 + ((B + 9 * H / (M : ℝ)) -
            (B - 9 * H / (M : ℝ))) / sep := hpack
      _ = 1 + 18 * H / |A| := by
        dsimp only [sep]
        field_simp [hMne, ne_of_gt hApos]
        ring
      _ ≤ 1 + 9000 * H / r := by
        simpa only [add_comm] using add_le_add_left hratio 1
      _ = 1 + 9000 * H / max |A| |B| := by rfl
  · have hsmall : 500 * |A| < r := lt_of_not_ge hlarge
    have hAB : |A| < |B| := by
      by_contra hnot
      have hBA : |B| ≤ |A| := le_of_not_gt hnot
      have hrEq : r = |A| := by
        dsimp only [r]
        exact max_eq_left hBA
      rw [hrEq] at hsmall
      nlinarith [abs_nonneg A]
    have hrEq : r = |B| := by
      dsimp only [r]
      exact max_eq_right hAB.le
    by_cases hJempty : J = ∅
    · subst J
      simp only [Finset.card_empty, Nat.cast_zero]
      positivity
    · obtain ⟨k, hk⟩ := Finset.nonempty_iff_ne_empty.mpr hJempty
      have hkRange : k < 2 * M := Finset.mem_range.mp (hJ hk)
      have htu : t ^ k ≤ 9 := by
        simpa only [t] using
          localRatioMeshStep_pow_le_nine_of_lt_two_mul hM hkRange
      have htku : 0 ≤ t ^ k := by positivity
      have htkuSq : t ^ (2 * k) ≤ 81 := by
        rw [show 2 * k = k + k by omega, pow_add]
        nlinarith [sq_nonneg (t ^ k - 9)]
      have hterm : |tau * A * t ^ (2 * k)| ≤ 243 * |A| := by
        rw [abs_mul, abs_mul, abs_of_pos htauPos,
          abs_of_nonneg (by positivity : 0 ≤ t ^ (2 * k))]
        have hprod : tau * t ^ (2 * k) ≤ 3 * 81 :=
          mul_le_mul htauUpper htkuSq
            (by positivity : 0 ≤ t ^ (2 * k)) (by norm_num)
        calc
          tau * |A| * t ^ (2 * k) =
              (tau * t ^ (2 * k)) * |A| := by ring
          _ ≤ (3 * 81) * |A| :=
            mul_le_mul_of_nonneg_right hprod (abs_nonneg A)
          _ = 243 * |A| := by ring
      have hBbound : |B| ≤ 243 * |A| + 9 * H / (M : ℝ) := by
        calc
          |B| = |(B - tau * A * t ^ (2 * k)) +
              tau * A * t ^ (2 * k)| := by
            congr 1
            ring
          _ ≤ |B - tau * A * t ^ (2 * k)| +
              |tau * A * t ^ (2 * k)| := abs_add_le _ _
          _ = |tau * A * t ^ (2 * k) - B| +
              |tau * A * t ^ (2 * k)| := by rw [abs_sub_comm]
          _ ≤ 9 * H / (M : ℝ) + 243 * |A| :=
            add_le_add (hscaledNear k hk) hterm
          _ = 243 * |A| + 9 * H / (M : ℝ) := by ring
      have hrSmall : r ≤ 18 * H / (M : ℝ) := by
        rw [← hrEq] at hBbound
        rw [show 9 * H / (M : ℝ) = 9 * (H / (M : ℝ)) by ring]
          at hBbound
        rw [show 18 * H / (M : ℝ) = 18 * (H / (M : ℝ)) by ring]
        have hAupper : |A| < r / 500 := by
          exact (lt_div_iff₀ (by norm_num : (0 : ℝ) < 500)).2 (by
            simpa only [mul_comm] using hsmall)
        nlinarith
      have hcardNat : J.card ≤ 2 * M := by
        simpa using Finset.card_le_card hJ
      have hcard : (J.card : ℝ) ≤ 2 * (M : ℝ) := by exact_mod_cast hcardNat
      have hMle : (M : ℝ) ≤ 18 * H / r := by
        apply (le_div_iff₀ hrpos).2
        calc
          (M : ℝ) * r ≤ (M : ℝ) * (18 * H / (M : ℝ)) :=
            mul_le_mul_of_nonneg_left hrSmall hMreal.le
          _ = 18 * H := by field_simp [hMne]
      calc
        (J.card : ℝ) ≤ 2 * (M : ℝ) := hcard
        _ ≤ 36 * H / r := by
          calc
            2 * (M : ℝ) ≤ 2 * (18 * H / r) := by gcongr
            _ = 36 * H / r := by ring
        _ ≤ 1 + 9000 * H / r := by
          have hdiv : 0 ≤ H / r := div_nonneg hH hrpos.le
          rw [show 36 * H / r = 36 * (H / r) by ring,
            show 9000 * H / r = 9000 * (H / r) by ring]
          nlinarith
        _ = 1 + 9000 * H / max |A| |B| := by rfl

/-- A real square-map target cell is within one normalized mesh step of its
literal right endpoint. -/
theorem abs_sub_realSquareMapTargetCell_rightEndpoint_mul_sq_le
    {M s p : ℝ} {o : ℤ} (hM : 0 < M) (hs : 0 < s)
    (hp : realSquareMapTargetCell M s o p) :
    |p - (1 + (o : ℝ) / M) * s ^ 2| ≤ s ^ 2 / M := by
  have hsSq : 0 < s ^ 2 := sq_pos_of_pos hs
  have hnormalizedUpper : p / s ^ 2 ≤ 1 + (o : ℝ) / M := by
    have hquot : p / s ^ 2 - 1 ≤ (o : ℝ) / M := by
      apply (le_div_iff₀ hM).2
      nlinarith [hp.2]
    linarith
  have hnormalizedLower :
      1 + (o : ℝ) / M - 1 / M ≤ p / s ^ 2 := by
    have hstrict : 1 + ((o : ℝ) - 1) / M < p / s ^ 2 := by
      have hquot : ((o : ℝ) - 1) / M < p / s ^ 2 - 1 := by
        apply (div_lt_iff₀ hM).2
        nlinarith [hp.1]
      linarith
    have hid : 1 + ((o : ℝ) - 1) / M =
        1 + (o : ℝ) / M - 1 / M := by ring
    rw [← hid]
    exact hstrict.le
  have hnormalized :
      |p / s ^ 2 - (1 + (o : ℝ) / M)| ≤ 1 / M := by
    rw [abs_le]
    constructor <;> linarith
  have hrewrite : p - (1 + (o : ℝ) / M) * s ^ 2 =
      s ^ 2 * (p / s ^ 2 - (1 + (o : ℝ) / M)) := by
    field_simp [hs.ne']
  rw [hrewrite, abs_mul, abs_of_pos hsSq]
  calc
    s ^ 2 * |p / s ^ 2 - (1 + (o : ℝ) / M)| ≤
        s ^ 2 * (1 / M) :=
      mul_le_mul_of_nonneg_left hnormalized hsSq.le
    _ = s ^ 2 / M := by ring

/-- At one fixed annular dyadic scale, the preceding scalar estimate applies
separately to the two source signs and the nine target offsets.  Consequently
the number of literal real square-map cells satisfying the same fixed-vector
near-relation is independent of the mesh size `M`. -/
theorem card_realSquareMapCellPairs_fixedVectorNear_at_scale_le
    {F : ℝ} {M j : ℕ} (hM : 6 ≤ M) {A B H : ℝ}
    (hH : 0 ≤ H) (hr : 0 < max |A| |B|)
    (J : Finset RealSquareMapCellPairIndex)
    (hJ : J ⊆ realSquareMapCellPairIndices F M)
    (hscale : ∀ cell ∈ J, cell.1.2.1 = j)
    (hnear : ∀ cell ∈ J,
      |(1 + (cell.2 : ℝ) / (M : ℝ)) *
          (localRatioMeshStep M ^ cell.1.2.2 * A) -
        B / localRatioMeshStep M ^ cell.1.2.2| ≤ H / (M : ℝ)) :
    (J.card : ℝ) ≤ 18 + 162000 * H / max |A| |B| := by
  classical
  let group : RealSquareMapCellPairIndex → ℤ × ℤ :=
    fun cell ↦ (cell.1.1, cell.2)
  let mesh : RealSquareMapCellPairIndex → ℕ :=
    fun cell ↦ cell.1.2.2
  have hMpos : 0 < M := lt_of_lt_of_le (by omega) hM
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hMne : (M : ℝ) ≠ 0 := hMreal.ne'
  have hgroupSubset : J.image group ⊆
      annularSigns.product realSquareMapTargetOffsets := by
    intro g hg
    obtain ⟨cell, hcell, rfl⟩ := Finset.mem_image.mp hg
    have hambient := hJ hcell
    exact Finset.mem_product.mpr
      ⟨(mem_annularMultiplicativeCellIndices.mp
          (Finset.mem_product.mp hambient).1).1,
        (Finset.mem_product.mp hambient).2⟩
  have hgroupCard : (J.image group).card ≤ 18 := by
    calc
      (J.image group).card ≤
          (annularSigns.product realSquareMapTargetOffsets).card :=
        Finset.card_le_card hgroupSubset
      _ = 18 := by simp
  have hgroupCardReal : ((J.image group).card : ℝ) ≤ 18 := by
    exact_mod_cast hgroupCard
  have hconstantNonneg :
      0 ≤ 1 + 9000 * H / max |A| |B| := by
    have hrle : 0 ≤ max |A| |B| := hr.le
    positivity
  have hfiber : ∀ g ∈ J.image group,
      (((J.filter fun cell ↦ group cell = g).card : ℕ) : ℝ) ≤
        1 + 9000 * H / max |A| |B| := by
    intro g hg
    let fiber : Finset RealSquareMapCellPairIndex :=
      J.filter fun cell ↦ group cell = g
    let K : Finset ℕ := fiber.image mesh
    have hoffset : g.2 ∈ realSquareMapTargetOffsets :=
      (Finset.mem_product.mp (hgroupSubset hg)).2
    have hoffsetBounds : (-1 : ℤ) ≤ g.2 ∧ g.2 ≤ 7 := by
      simpa only [realSquareMapTargetOffsets] using
        (Finset.mem_Icc.mp hoffset)
    have htauLower : (1 / 2 : ℝ) ≤
        1 + (g.2 : ℝ) / (M : ℝ) := by
      have hlowReal : (-1 : ℝ) ≤ (g.2 : ℝ) := by
        exact_mod_cast hoffsetBounds.1
      have hMge : (6 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      rw [show 1 + (g.2 : ℝ) / (M : ℝ) =
          ((M : ℝ) + (g.2 : ℝ)) / (M : ℝ) by
        field_simp [hMne]]
      apply (le_div_iff₀ hMreal).2
      nlinarith
    have htauUpper : 1 + (g.2 : ℝ) / (M : ℝ) ≤ 3 := by
      have huppReal : (g.2 : ℝ) ≤ 7 := by
        exact_mod_cast hoffsetBounds.2
      have hMge : (6 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      rw [show 1 + (g.2 : ℝ) / (M : ℝ) =
          ((M : ℝ) + (g.2 : ℝ)) / (M : ℝ) by
        field_simp [hMne]]
      apply (div_le_iff₀ hMreal).2
      nlinarith
    have hmeshInj : Set.InjOn mesh fiber := by
      intro cell hcell cell' hcell' hmeshEq
      have hcellMem : cell ∈ J := (Finset.mem_filter.mp hcell).1
      have hcell'Mem : cell' ∈ J := (Finset.mem_filter.mp hcell').1
      have hgroupEq : group cell = group cell' :=
        (Finset.mem_filter.mp hcell).2.trans
          (Finset.mem_filter.mp hcell').2.symm
      rcases cell with ⟨⟨eps, ⟨scale, k⟩⟩, off⟩
      rcases cell' with ⟨⟨eps', ⟨scale', k'⟩⟩, off'⟩
      simp only [group, mesh, Prod.mk.injEq] at hgroupEq hmeshEq ⊢
      have hscaleEq : scale = scale' :=
        (hscale _ hcellMem).trans (hscale _ hcell'Mem).symm
      exact ⟨⟨hgroupEq.1, hscaleEq, hmeshEq⟩, hgroupEq.2⟩
    have hcardEq : fiber.card = K.card := by
      exact (Finset.card_image_of_injOn hmeshInj).symm
    have hK : K ⊆ Finset.range (2 * M) := by
      intro k hk
      obtain ⟨cell, hcell, rfl⟩ := Finset.mem_image.mp hk
      have hcellMem : cell ∈ J := (Finset.mem_filter.mp hcell).1
      exact Finset.mem_range.mpr
        (mem_annularMultiplicativeCellIndices.mp
          (Finset.mem_product.mp (hJ hcellMem)).1).2.2
    have hnearK : ∀ k ∈ K,
        |(1 + (g.2 : ℝ) / (M : ℝ)) *
            (localRatioMeshStep M ^ k * A) -
          B / localRatioMeshStep M ^ k| ≤ H / (M : ℝ) := by
      intro k hk
      obtain ⟨cell, hcell, hmesh⟩ := Finset.mem_image.mp hk
      have hcellMem : cell ∈ J := (Finset.mem_filter.mp hcell).1
      have hcellGroup : group cell = g :=
        (Finset.mem_filter.mp hcell).2
      have hn := hnear cell hcellMem
      have hoff : (cell.2 : ℝ) = (g.2 : ℝ) := by
        exact_mod_cast congrArg Prod.snd hcellGroup
      simpa only [mesh] using hmesh ▸ hoff ▸ hn
    have hbound :=
      card_realMultiplicativeMeshIndices_of_fixedVector_le
        hMpos hH htauLower htauUpper hr K hK hnearK
    change (fiber.card : ℝ) ≤ 1 + 9000 * H / max |A| |B|
    rw [hcardEq]
    exact hbound
  have hdecomposition : (J.card : ℝ) =
      ∑ g ∈ J.image group,
        (((J.filter fun cell ↦ group cell = g).card : ℕ) : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_image group J
  rw [hdecomposition]
  calc
    (∑ g ∈ J.image group,
        (((J.filter fun cell ↦ group cell = g).card : ℕ) : ℝ)) ≤
        ∑ _g ∈ J.image group,
          (1 + 9000 * H / max |A| |B|) :=
      Finset.sum_le_sum hfiber
    _ = ((J.image group).card : ℝ) *
          (1 + 9000 * H / max |A| |B|) := by
      simp
      ring
    _ ≤ 18 * (1 + 9000 * H / max |A| |B|) :=
      mul_le_mul_of_nonneg_right hgroupCardReal hconstantNonneg
    _ = 18 + 162000 * H / max |A| |B| := by ring

end

end PellPaper
