import Pell.ClassAverageLayerCake

/-!
# Finite sums from reciprocal-square tail bounds

For a finite real family, a genuine weak-tail estimate `# {i : T ≤ r_i} ≤ B/T²`
above a positive cutoff `S` implies `sum r_i ≤ #J*S+B/S`.  The proof uses
finite layer cake and the exact inverse-square integral.  No positivity of
the family values, supplied truncation, or summability hypothesis is needed.
-/

namespace PellPaper

open MeasureTheory Set
open scoped BigOperators Interval

noncomputable section

private theorem intervalIntegrable_upper_threshold (S L r : ℝ) :
    IntervalIntegrable (fun T : ℝ => if T ≤ r then (1 : ℝ) else 0) volume S L := by
  have hc : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume S L := intervalIntegrable_const
  exact ⟨hc.1.indicator measurableSet_Iic, hc.2.indicator measurableSet_Iic⟩

private theorem le_cutoff_add_upper_threshold_integral
    (S L r : ℝ) (hSL : S ≤ L) (hrL : r ≤ L) :
    r ≤ S + ∫ T in S..L, if T ≤ r then (1 : ℝ) else 0 := by
  by_cases hSr : S ≤ r
  · have hinter : Iic r ∩ Ioc S L = Ioc S r := by
      ext T
      simp only [mem_inter_iff, mem_Iic, mem_Ioc]
      constructor
      · rintro ⟨hr, hS, _⟩
        exact ⟨hS, hr⟩
      · rintro ⟨hS, hr⟩
        exact ⟨hr, hS, hr.trans hrL⟩
    have heq : (∫ T in S..L, if T ≤ r then (1 : ℝ) else 0) = r - S := by
      calc
        (∫ T in S..L, if T ≤ r then (1 : ℝ) else 0) = ∫ _ in S..r, (1 : ℝ) := by
          change (∫ T in S..L, (Iic r).indicator (fun _ : ℝ => (1 : ℝ)) T) = _
          rw [intervalIntegral.integral_of_le hSL, intervalIntegral.integral_of_le hSr,
            MeasureTheory.integral_indicator measurableSet_Iic,
            Measure.restrict_restrict measurableSet_Iic, hinter]
        _ = r - S := by simp
    rw [heq]
    linarith
  · have heq : (∫ T in S..L, if T ≤ r then (1 : ℝ) else 0) = 0 := by
      calc
        (∫ T in S..L, if T ≤ r then (1 : ℝ) else 0) = ∫ _ in S..L, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro T hT
          rw [uIcc_of_le hSL] at hT
          exact if_neg (not_le_of_gt ((lt_of_not_ge hSr).trans_le hT.1))
        _ = 0 := by simp
    rw [heq, add_zero]
    exact (lt_of_not_ge hSr).le

/-- A finite weak-tail bound with reciprocal-square decay gives the exact
cutoff budget `#J*S+B/S`.  All family values are actual real numbers. -/
theorem sum_le_card_mul_cutoff_add_div_of_weak_tail_bound
    {ι : Type*} (J : Finset ι) (r : ι → ℝ) (S B : ℝ)
    (hS : 0 < S) (hB : 0 ≤ B)
    (htail : ∀ T : ℝ, S ≤ T → ((J.filter fun i => T ≤ r i).card : ℝ) ≤ B / T ^ 2) :
    (∑ i ∈ J, r i) ≤ (J.card : ℝ) * S + B / S := by
  classical
  let L := S + ∑ i ∈ J, |r i|
  have hSL : S ≤ L := le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => abs_nonneg (r i)))
  have hL : 0 < L := hS.trans_le hSL
  have hrL : ∀ i ∈ J, r i ≤ L := by
    intro i hi
    have habs := Finset.single_le_sum (fun j (_ : j ∈ J) => abs_nonneg (r j)) hi
    dsimp [L]
    linarith [le_abs_self (r i)]
  have hcount (T : ℝ) : ((J.filter fun i => T ≤ r i).card : ℝ) =
      ∑ i ∈ J, if T ≤ r i then (1 : ℝ) else 0 := by
    simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> norm_num
  have hcount_int : IntervalIntegrable
      (fun T : ℝ => ((J.filter fun i => T ≤ r i).card : ℝ)) volume S L := by
    simp_rw [hcount]
    convert! IntervalIntegrable.sum J
      (fun i (_ : i ∈ J) => intervalIntegrable_upper_threshold S L (r i)) using 1
    all_goals first | rfl | (funext T; simp only [Finset.sum_apply])
  have hkernel : IntervalIntegrable (fun T : ℝ => B / T ^ 2) volume S L := by
    have h := intervalIntegral.intervalIntegrable_zpow (a := S) (b := L) (n := -2)
      (μ := volume) (Or.inr (notMem_uIcc_of_lt hS hL))
    simpa only [zpow_neg, zpow_ofNat, div_eq_mul_inv] using h.const_mul B
  have hsum : (∑ i ∈ J, r i) ≤ (J.card : ℝ) * S +
      ∫ T in S..L, ((J.filter fun i => T ≤ r i).card : ℝ) := by
    have hsum_int : (∫ T in S..L, ((J.filter fun i => T ≤ r i).card : ℝ)) =
        ∑ i ∈ J, ∫ T in S..L, if T ≤ r i then (1 : ℝ) else 0 := by
      simp_rw [hcount]
      exact intervalIntegral.integral_finsetSum
        (fun i (_ : i ∈ J) => intervalIntegrable_upper_threshold S L (r i))
    rw [hsum_int]
    calc
      (∑ i ∈ J, r i) ≤ ∑ i ∈ J,
          (S + ∫ T in S..L, if T ≤ r i then (1 : ℝ) else 0) :=
        Finset.sum_le_sum (fun i hi => le_cutoff_add_upper_threshold_integral S L (r i) hSL (hrL i hi))
      _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  have hint : (∫ T in S..L, ((J.filter fun i => T ≤ r i).card : ℝ)) ≤ B / S := by
    calc
      (∫ T in S..L, ((J.filter fun i => T ≤ r i).card : ℝ)) ≤
          ∫ T in S..L, B / T ^ 2 :=
        intervalIntegral.integral_mono_on hSL hcount_int hkernel (fun T hT => htail T hT.1)
      _ = B * (1 / S - 1 / L) := by
        have hfun : (fun T : ℝ => B / T ^ 2) = (fun T : ℝ => B * (1 / T ^ 2)) := by
          funext T
          ring
        rw [hfun, intervalIntegral.integral_const_mul, inverse_square_interval_integral hS hL]
      _ ≤ B / S := by
        have hnonneg : 0 ≤ B / L := div_nonneg hB hL.le
        calc
          B * (1 / S - 1 / L) = B / S - B / L := by ring
          _ ≤ B / S := sub_le_self _ hnonneg
  exact hsum.trans (add_le_add le_rfl hint)

end

end PellPaper
