import Pell.ExceptionalDecomposition
import Pell.FixedHeight
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Pell.SquarefreeGlobalReduction
import Mathlib.Tactic

/-!
# The manuscript's doubled-parameter square-part restoration

The split is at the actual squarefree kernel `w = sqrt X`.  Below it we
count all square multiples; above it the transferred Pell unit has height
`2 * theta`.  Natural dyadic blocks may straddle the split, so the conversion
is made before dropping the lower-bound filter on `w`.
-/

open scoped BigOperators
open MeasureTheory intervalIntegral
namespace PellPaper
noncomputable section

/-- The square multiples of `w` whose positive root lies below the real
cutoff forced by `s²w ≤ X`. -/
def doubledParameterSquareMultiples (X : ℝ) (w : ℕ) : Finset ℕ :=
  (Finset.Icc 1 ⌊Real.sqrt (X / (w : ℝ))⌋₊).image fun s => s ^ 2 * w

/-- A square-part decomposition lies in the exact finite root cover. -/
theorem mem_doubledParameterSquareMultiples {X : ℝ} {m s w : ℕ}
    (hs : 0 < s) (hw : 0 < w) (hm : (m : ℝ) ≤ X)
    (hdecomp : m = s ^ 2 * w) :
    m ∈ doubledParameterSquareMultiples X w := by
  classical
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  have hsR : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have hsq : (s : ℝ) ^ 2 ≤ X / (w : ℝ) := by
    apply (le_div_iff₀ hwR).2
    simpa only [hdecomp, Nat.cast_mul, Nat.cast_pow] using hm
  have hsroot : (s : ℝ) ≤ Real.sqrt (X / (w : ℝ)) :=
    Real.le_sqrt_of_sq_le hsq
  exact Finset.mem_image.mpr ⟨s,
    Finset.mem_Icc.mpr ⟨hs, Nat.le_floor hsroot⟩, hdecomp.symm⟩

/-- The fibre contains at most the expected square-root weight. -/
theorem doubledParameterSquareMultiples_card_le {X : ℝ} (w : ℕ) :
    ((doubledParameterSquareMultiples X w).card : ℝ) ≤
      Real.sqrt (X / (w : ℝ)) := by
  calc
    ((doubledParameterSquareMultiples X w).card : ℝ) ≤
        ((Finset.Icc 1 ⌊Real.sqrt (X / (w : ℝ))⌋₊).card : ℝ) := by
      exact_mod_cast Finset.card_image_le
    _ = (⌊Real.sqrt (X / (w : ℝ))⌋₊ : ℝ) := by simp
    _ ≤ Real.sqrt (X / (w : ℝ)) := Nat.floor_le (Real.sqrt_nonneg _)

/-- Above `sqrt X`, the squarefree kernel has exactly the doubled height
used in the manuscript. -/
theorem smallFundamentalSolution_doubled_of_sqrt_le
    {theta X : ℝ} {m s w : ℕ}
    (htheta : 0 ≤ theta) (hX : 0 ≤ X)
    (hsmall : SmallFundamentalSolution theta m)
    (hs : 0 < s) (hw : 0 < w) (hdecomp : m = s ^ 2 * w)
    (hmX : (m : ℝ) ≤ X) (hwX : Real.sqrt X ≤ (w : ℝ)) :
    SmallFundamentalSolution (2 * theta) w := by
  have hwns := squarefree_part_not_isSquare hdecomp
    (positive_nonsquare_of_smallFundamentalSolution hsmall).2
  obtain ⟨a, ha⟩ := Pell.IsFundamental.exists_of_not_isSquare
    (show (0 : ℤ) < w by exact_mod_cast hw)
    (by simpa only [Int.isSquare_natCast_iff] using hwns)
  obtain ⟨b, hb, he⟩ := hsmall
  refine ⟨a, ha, ?_⟩
  have hwR : (0 : ℝ) ≤ w := Nat.cast_nonneg _
  have hXsq : X ≤ (w : ℝ) ^ 2 := by
    nlinarith [Real.sq_sqrt hX,
      mul_self_le_mul_self (Real.sqrt_nonneg X) hwX]
  calc
    epsilon a ≤ epsilon b := square_part_transfer_of_decomposition hs hdecomp ha hb
    _ ≤ (m : ℝ) ^ theta := he
    _ ≤ X ^ theta := Real.rpow_le_rpow (Nat.cast_nonneg _) hmX htheta
    _ ≤ ((w : ℝ) ^ 2) ^ theta := Real.rpow_le_rpow hX hXsq htheta
    _ = (w : ℝ) ^ (2 * theta) := by simpa using (Real.rpow_natCast_mul hwR 2 theta).symm

/-- The exact low-kernel cover drops the Pell and squarefree restrictions. -/
def doubledParameterLowCover (X : ℝ) : Finset ℕ :=
  (Finset.Icc 1 ⌊Real.sqrt X⌋₊).biUnion (doubledParameterSquareMultiples X)

/-- The integral-test bound used in the low-kernel contribution. Keeping it
local makes the counting argument independent of the class-average proof. -/
private theorem doubledParameter_sum_range_succ_rpow_neg_half_le_two_sqrt (k : ℕ) :
    (∑ j ∈ Finset.range (k + 1),
        (((j + 1 : ℕ) : ℝ) ^ (-1 / 2 : ℝ))) ≤
      2 * Real.sqrt ((k + 1 : ℕ) : ℝ) := by
  let f : ℝ → ℝ := fun x ↦ x ^ (-1 / 2 : ℝ)
  have hanti : AntitoneOn f (Set.Icc 1 (1 + (k : ℝ))) :=
    (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos
      (show (-1 / 2 : ℝ) ≤ 0 by norm_num)).mono (by
        intro x hx
        exact (show (0 : ℝ) < x by linarith [hx.1]))
  have htail := hanti.sum_le_integral
  rw [integral_rpow (a := (1 : ℝ)) (b := 1 + (k : ℝ))
    (Or.inl (show (-1 : ℝ) < -1 / 2 by norm_num))] at htail
  have hrewrite :
      (∑ i ∈ Finset.range k, f (1 + ((i + 1 : ℕ) : ℝ))) =
        ∑ i ∈ Finset.range k,
          (((i + 2 : ℕ) : ℝ) ^ (-1 / 2 : ℝ)) := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [f]
    congr 2
    norm_num
    ring
  rw [hrewrite] at htail
  rw [Finset.sum_range_succ']
  simp only [Nat.zero_add, Nat.cast_one, Real.one_rpow]
  rw [Real.sqrt_eq_rpow]
  have hkcast : (1 : ℝ) + (k : ℝ) = ((k + 1 : ℕ) : ℝ) := by
    norm_num
    ring
  rw [hkcast] at htail
  have hshift :
      (∑ i ∈ Finset.range k,
          (((i + 1 + 1 : ℕ) : ℝ) ^ (-1 / 2 : ℝ))) =
        ∑ i ∈ Finset.range k,
          (((i + 2 : ℕ) : ℝ) ^ (-1 / 2 : ℝ)) := by
    apply Finset.sum_congr rfl
    intro i _
    congr 3
  rw [hshift]
  have htail' :
      (∑ i ∈ Finset.range k,
          (((i + 2 : ℕ) : ℝ) ^ (-1 / 2 : ℝ))) ≤
        2 * (((k + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) - 2 := by
    convert htail using 1
    all_goals norm_num [Nat.cast_add, Nat.cast_one, neg_div]
    all_goals ring
  linarith

/-- The elementary reciprocal-square-root sum, in natural interval form. -/
theorem doubledParameter_sum_rpow_neg_half_le (N : ℕ) :
    (∑ w ∈ Finset.Icc 1 N, (w : ℝ) ^ (-1 / 2 : ℝ)) ≤
      2 * Real.sqrt (N : ℝ) := by
  cases N with
  | zero => simp
  | succ k =>
    have hsum :
        (∑ w ∈ Finset.Icc 1 (k + 1), (w : ℝ) ^ (-1 / 2 : ℝ)) =
          ∑ j ∈ Finset.range (k + 1), ((j + 1 : ℕ) : ℝ) ^ (-1 / 2 : ℝ) := by
      rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel_right, add_comm 1]
    rw [hsum]
    exact doubledParameter_sum_range_succ_rpow_neg_half_le_two_sqrt k

/-- The low squarefree-kernel contribution has the manuscript's `X^(3/4)`
bound, with the explicit constant two. -/
theorem doubledParameterLowCover_card_le {X : ℝ} (hX : 0 ≤ X) :
    ((doubledParameterLowCover X).card : ℝ) ≤ 2 * X ^ (3 / 4 : ℝ) := by
  have hsum :
      ((doubledParameterLowCover X).card : ℝ) ≤
        ∑ w ∈ Finset.Icc 1 ⌊Real.sqrt X⌋₊,
          Real.sqrt (X / (w : ℝ)) := by
    calc
      ((doubledParameterLowCover X).card : ℝ) ≤
          ∑ w ∈ Finset.Icc 1 ⌊Real.sqrt X⌋₊,
            ((doubledParameterSquareMultiples X w).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      _ ≤ _ := Finset.sum_le_sum fun w _ => doubledParameterSquareMultiples_card_le w
  calc
    ((doubledParameterLowCover X).card : ℝ) ≤
        ∑ w ∈ Finset.Icc 1 ⌊Real.sqrt X⌋₊,
          Real.sqrt (X / (w : ℝ)) := hsum
    _ = Real.sqrt X *
        ∑ w ∈ Finset.Icc 1 ⌊Real.sqrt X⌋₊, (w : ℝ) ^ (-1 / 2 : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w hw
      have hwpos : (0 : ℝ) < w := by
        exact_mod_cast (Finset.mem_Icc.mp hw).1
      simp only [Real.sqrt_div hX, Real.sqrt_eq_rpow]
      rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hwpos.le]
      ring
    _ ≤ Real.sqrt X * (2 * Real.sqrt (⌊Real.sqrt X⌋₊ : ℝ)) :=
      mul_le_mul_of_nonneg_left (doubledParameter_sum_rpow_neg_half_le _)
        (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt X * (2 * Real.sqrt (Real.sqrt X)) := by
      gcongr
      exact Nat.floor_le (Real.sqrt_nonneg _)
    _ = 2 * X ^ (3 / 4 : ℝ) := by
      simp only [Real.sqrt_eq_rpow]
      rw [← Real.rpow_mul hX]
      calc
        X ^ (1 / 2 : ℝ) * (2 * X ^ ((1 / 2 : ℝ) * (1 / 2))) =
            2 * (X ^ (1 / 2 : ℝ) * X ^ ((1 / 2 : ℝ) * (1 / 2))) := by ring
        _ = 2 * X ^ (3 / 4 : ℝ) := by
          rw [← Real.rpow_add' hX (by norm_num)]
          norm_num

/-- A high kernel dyadic block, with roots bounded by the actual cutoff. -/
def doubledParameterHighBlock (theta X : ℝ) (Y : ℕ) : Finset ℕ :=
  (squarefreeDyadicExceptionalSet (2 * theta) Y).biUnion
    (doubledParameterSquareMultiples X)

/-- The weighted dyadic count used after the doubled-height transfer. -/
theorem doubledParameterHighBlock_card_le {theta X : ℝ} {Y : ℕ}
    (hX : 0 ≤ X) (hY : 0 < Y) :
    ((doubledParameterHighBlock theta X Y).card : ℝ) ≤
      Real.sqrt (X / (Y : ℝ)) *
        (squarefreeDyadicExceptionalCount (2 * theta) Y : ℝ) := by
  classical
  calc
    ((doubledParameterHighBlock theta X Y).card : ℝ) ≤
        ∑ w ∈ squarefreeDyadicExceptionalSet (2 * theta) Y,
          ((doubledParameterSquareMultiples X w).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ w ∈ squarefreeDyadicExceptionalSet (2 * theta) Y,
        Real.sqrt (X / (Y : ℝ)) := by
      apply Finset.sum_le_sum
      intro w hw
      apply (doubledParameterSquareMultiples_card_le w).trans
      apply Real.sqrt_le_sqrt
      apply div_le_div_of_nonneg_left hX
      · exact_mod_cast hY
      · exact_mod_cast (mem_squarefreeDyadicExceptionalSet.mp hw).1
    _ = _ := by simp [squarefreeDyadicExceptionalCount, mul_comm]

/-- The global exceptional set is covered by the low kernels and high dyadic
blocks. The condition `sqrt X ≤ w` is used before dropping it from the block. -/
theorem exceptionalSet_subset_doubledParameter_cover
    {theta X : ℝ} (htheta : 0 ≤ theta) (hX : 0 ≤ X) :
    exceptionalSet theta ⌊X⌋₊ ⊆ doubledParameterLowCover X ∪
      ((Finset.range (Nat.log 2 ⌊X⌋₊ + 1)).filter
        (fun k => Real.sqrt X / 2 ≤ ((2 ^ k : ℕ) : ℝ))).biUnion
          (fun k => doubledParameterHighBlock theta X (2 ^ k)) := by
  classical
  intro m hm
  obtain ⟨s, w, hs, hw, hdecomp, hsf, _, a, b, ha, hb, hab, he⟩ :=
    exists_square_part_fundamental_data_of_mem_exceptionalSet hm
  have hmX : (m : ℝ) ≤ X :=
    (show (m : ℝ) ≤ ⌊X⌋₊ by exact_mod_cast (mem_exceptionalSet.mp hm).2.1).trans
      (Nat.floor_le hX)
  have hwpos : 0 < w := by omega
  have hmem := mem_doubledParameterSquareMultiples hs hwpos hmX hdecomp
  by_cases hwX : (w : ℝ) < Real.sqrt X
  · apply Finset.mem_union_left
    exact Finset.mem_biUnion.mpr ⟨w,
      Finset.mem_Icc.mpr ⟨by omega, Nat.le_floor hwX.le⟩, hmem⟩
  · have hwX' : Real.sqrt X ≤ (w : ℝ) := le_of_not_gt hwX
    have hsmall := smallFundamentalSolution_doubled_of_sqrt_le
      htheta hX (mem_exceptionalSet.mp hm).2.2 hs hwpos hdecomp hmX hwX'
    let k := Nat.log 2 w
    have hlo : 2 ^ k ≤ w := Nat.pow_log_le_self 2 (by omega)
    have hhi : w < 2 * 2 ^ k := by
      simpa only [k, pow_succ, Nat.mul_comm] using
        Nat.lt_pow_succ_log_self Nat.one_lt_two w
    have hwle : w ≤ ⌊X⌋₊ := by
      calc
        w ≤ s ^ 2 * w := Nat.le_mul_of_pos_left w (by positivity)
        _ = m := hdecomp.symm
        _ ≤ ⌊X⌋₊ := (mem_exceptionalSet.mp hm).2.1
    have hk : k < Nat.log 2 ⌊X⌋₊ + 1 := by
      have : k ≤ Nat.log 2 ⌊X⌋₊ := Nat.log_mono_right hwle
      omega
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, ?_⟩, ?_⟩
    · have hhiR : (w : ℝ) < 2 * ((2 ^ k : ℕ) : ℝ) := by exact_mod_cast hhi
      linarith
    · exact Finset.mem_biUnion.mpr ⟨w,
        mem_squarefreeDyadicExceptionalSet.mpr ⟨hlo, hhi, hsf, hsmall⟩, hmem⟩

end
end PellPaper
