import Pell.FiniteReciprocalSquareTailSummation

/-!
# Finite sums from mixed reciprocal-linear and reciprocal-square tails

For a finite real family bounded above by `L`, a weak-tail estimate of the
form `A / T + B / T^2` above a positive cutoff `S` gives the exact finite
layer-cake budget

`#J * S + A * log (L / S) + B / S`.

This is the summation shape needed by the intrinsic-completion argument.  It
contains no lattice, successive-minimum, or character-sum input.
-/

namespace PellPaper

open MeasureTheory Set
open scoped BigOperators Interval

noncomputable section

private theorem intervalIntegrable_upper_threshold_linear_square
    (S L r : ℝ) :
    IntervalIntegrable (fun T : ℝ => if T ≤ r then (1 : ℝ) else 0)
      volume S L := by
  have hc : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume S L :=
    intervalIntegrable_const
  exact ⟨hc.1.indicator measurableSet_Iic, hc.2.indicator measurableSet_Iic⟩

private theorem le_cutoff_add_upper_threshold_integral_linear_square
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
        (∫ T in S..L, if T ≤ r then (1 : ℝ) else 0) =
            ∫ _ in S..r, (1 : ℝ) := by
          change (∫ T in S..L, (Iic r).indicator (fun _ : ℝ => (1 : ℝ)) T) = _
          rw [intervalIntegral.integral_of_le hSL,
            intervalIntegral.integral_of_le hSr,
            MeasureTheory.integral_indicator measurableSet_Iic,
            Measure.restrict_restrict measurableSet_Iic, hinter]
        _ = r - S := by simp
    rw [heq]
    linarith
  · have heq : (∫ T in S..L, if T ≤ r then (1 : ℝ) else 0) = 0 := by
      calc
        (∫ T in S..L, if T ≤ r then (1 : ℝ) else 0) =
            ∫ _ in S..L, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro T hT
          rw [uIcc_of_le hSL] at hT
          exact if_neg (not_le_of_gt ((lt_of_not_ge hSr).trans_le hT.1))
        _ = 0 := by simp
    rw [heq, add_zero]
    exact (lt_of_not_ge hSr).le

/-- A finite weak tail with a reciprocal-linear part and a reciprocal-square
part gives the exact cutoff budget
`#J * S + A * log (L / S) + B / S`.

The explicit upper bound `r i ≤ L` is essential for the logarithmic term.
No positivity assumption on the family values is needed. -/
theorem sum_le_card_mul_cutoff_add_log_add_div_of_weak_linear_square_tail_bound
    {ι : Type*} (J : Finset ι) (r : ι → ℝ) (S L A B : ℝ)
    (hS : 0 < S) (hSL : S ≤ L) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hrL : ∀ i ∈ J, r i ≤ L)
    (htail : ∀ T : ℝ, S ≤ T →
      ((J.filter fun i => T ≤ r i).card : ℝ) ≤ A / T + B / T ^ 2) :
    (∑ i ∈ J, r i) ≤
      (J.card : ℝ) * S + A * Real.log (L / S) + B / S := by
  classical
  by_cases hSL' : S = L
  · subst L
    have hsum : (∑ i ∈ J, r i) ≤ ∑ _i ∈ J, S := by
      exact Finset.sum_le_sum fun i hi => hrL i hi
    calc
      (∑ i ∈ J, r i) ≤ ∑ _i ∈ J, S := hsum
      _ = (J.card : ℝ) * S := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (J.card : ℝ) * S + A * Real.log (S / S) + B / S := by
        have hlog : 0 ≤ Real.log (S / S) := by
          rw [div_self hS.ne', Real.log_one]
        have hlinearNonneg : 0 ≤ A * Real.log (S / S) :=
          mul_nonneg hA hlog
        have hsquareNonneg : 0 ≤ B / S := div_nonneg hB hS.le
        linarith
  · have hSLlt : S < L := lt_of_le_of_ne hSL hSL'
    have hL : 0 < L := hS.trans hSLlt
    have hcount (T : ℝ) :
        ((J.filter fun i => T ≤ r i).card : ℝ) =
          ∑ i ∈ J, if T ≤ r i then (1 : ℝ) else 0 := by
      simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> norm_num
    have hcount_int : IntervalIntegrable
        (fun T : ℝ => ((J.filter fun i => T ≤ r i).card : ℝ))
        volume S L := by
      simp_rw [hcount]
      convert! IntervalIntegrable.sum J
        (fun i (_ : i ∈ J) =>
          intervalIntegrable_upper_threshold_linear_square S L (r i)) using 1
      all_goals first | rfl | (funext T; simp only [Finset.sum_apply])
    have hlinear : IntervalIntegrable (fun T : ℝ => A / T) volume S L := by
      have h := intervalIntegral.intervalIntegrable_zpow
        (a := S) (b := L) (n := -1) (μ := volume)
        (Or.inr (notMem_uIcc_of_lt hS hL))
      simpa only [zpow_neg, zpow_one, div_eq_mul_inv] using h.const_mul A
    have hsquare : IntervalIntegrable (fun T : ℝ => B / T ^ 2) volume S L := by
      have h := intervalIntegral.intervalIntegrable_zpow
        (a := S) (b := L) (n := -2) (μ := volume)
        (Or.inr (notMem_uIcc_of_lt hS hL))
      simpa only [zpow_neg, zpow_ofNat, div_eq_mul_inv] using h.const_mul B
    have hkernel : IntervalIntegrable
        (fun T : ℝ => A / T + B / T ^ 2) volume S L :=
      hlinear.add hsquare
    have hlinearIntegral :
        (∫ T in S..L, A / T) = A * Real.log (L / S) := by
      calc
        (∫ T in S..L, A / T) = A * ∫ T in S..L, 1 / T := by
          simp only [div_eq_mul_inv, one_mul]
          rw [intervalIntegral.integral_const_mul]
        _ = A * Real.log (L / S) := by
          rw [integral_one_div_of_pos hS hL]
    have hsquareIntegral :
        (∫ T in S..L, B / T ^ 2) = B * (1 / S - 1 / L) := by
      calc
        (∫ T in S..L, B / T ^ 2) =
            B * ∫ T in S..L, 1 / T ^ 2 := by
          simp only [div_eq_mul_inv, one_mul]
          rw [intervalIntegral.integral_const_mul]
        _ = B * (1 / S - 1 / L) := by
          rw [inverse_square_interval_integral hS hL]
    have hsum : (∑ i ∈ J, r i) ≤ (J.card : ℝ) * S +
        ∫ T in S..L, ((J.filter fun i => T ≤ r i).card : ℝ) := by
      have hsum_int :
          (∫ T in S..L, ((J.filter fun i => T ≤ r i).card : ℝ)) =
            ∑ i ∈ J, ∫ T in S..L, if T ≤ r i then (1 : ℝ) else 0 := by
        simp_rw [hcount]
        exact intervalIntegral.integral_finsetSum
          (fun i (_ : i ∈ J) =>
            intervalIntegrable_upper_threshold_linear_square S L (r i))
      rw [hsum_int]
      calc
        (∑ i ∈ J, r i) ≤ ∑ i ∈ J,
            (S + ∫ T in S..L, if T ≤ r i then (1 : ℝ) else 0) :=
          Finset.sum_le_sum fun i hi =>
            le_cutoff_add_upper_threshold_integral_linear_square
              S L (r i) hSL (hrL i hi)
        _ = _ := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    have hint :
        (∫ T in S..L, ((J.filter fun i => T ≤ r i).card : ℝ)) ≤
          A * Real.log (L / S) + B / S := by
      calc
        (∫ T in S..L, ((J.filter fun i => T ≤ r i).card : ℝ)) ≤
            ∫ T in S..L, (A / T + B / T ^ 2) :=
          intervalIntegral.integral_mono_on hSL hcount_int hkernel
            (fun T hT => htail T hT.1)
        _ = A * Real.log (L / S) + B * (1 / S - 1 / L) := by
          rw [intervalIntegral.integral_add hlinear hsquare,
            hlinearIntegral, hsquareIntegral]
        _ ≤ A * Real.log (L / S) + B / S := by
          have hnonneg : 0 ≤ B / L := div_nonneg hB hL.le
          calc
            A * Real.log (L / S) + B * (1 / S - 1 / L) =
                A * Real.log (L / S) + B / S - B / L := by ring
            _ ≤ A * Real.log (L / S) + B / S :=
              sub_le_self _ hnonneg
    calc
      (∑ i ∈ J, r i) ≤ (J.card : ℝ) * S +
          ∫ T in S..L, ((J.filter fun i => T ≤ r i).card : ℝ) := hsum
      _ ≤ (J.card : ℝ) * S +
          (A * Real.log (L / S) + B / S) := add_le_add_right hint _
      _ = (J.card : ℝ) * S + A * Real.log (L / S) + B / S := by ring

/-- If every family value is at least the cutoff, the tail estimate at the
cutoff itself absorbs the cardinal term.  This is the form used after the
nonempty-cell lower reciprocal-minimum bound. -/
theorem sum_le_linear_square_tail_completion
    {ι : Type*} (J : Finset ι) (r : ι → ℝ) (S L A B : ℝ)
    (hS : 0 < S) (hSL : S ≤ L) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hSr : ∀ i ∈ J, S ≤ r i)
    (hrL : ∀ i ∈ J, r i ≤ L)
    (htail : ∀ T : ℝ, S ≤ T →
      ((J.filter fun i => T ≤ r i).card : ℝ) ≤ A / T + B / T ^ 2) :
    (∑ i ∈ J, r i) ≤
      A * (1 + Real.log (L / S)) + 2 * B / S := by
  classical
  have hsum :=
    sum_le_card_mul_cutoff_add_log_add_div_of_weak_linear_square_tail_bound
      J r S L A B hS hSL hA hB hrL htail
  have hfilter : J.filter (fun i => S ≤ r i) = J := by
    apply Finset.filter_eq_self.mpr
    intro i hi
    exact hSr i hi
  have hcard : (J.card : ℝ) ≤ A / S + B / S ^ 2 := by
    have htailS := htail S le_rfl
    rw [hfilter] at htailS
    exact htailS
  have hcardTerm : (J.card : ℝ) * S ≤ A + B / S := by
    calc
      (J.card : ℝ) * S ≤ (A / S + B / S ^ 2) * S :=
        mul_le_mul_of_nonneg_right hcard hS.le
      _ = A + B / S := by field_simp [hS.ne']
  calc
    (∑ i ∈ J, r i) ≤
        (J.card : ℝ) * S + A * Real.log (L / S) + B / S := hsum
    _ ≤ (A + B / S) + A * Real.log (L / S) + B / S := by
      gcongr
    _ = A * (1 + Real.log (L / S)) + 2 * B / S := by ring

end

end PellPaper
