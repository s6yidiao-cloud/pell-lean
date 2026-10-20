import Pell.FactorRangeSplit
import Pell.MinimalityShiftExclusion

/-!
# Admissible shifted-square image of the unbalanced Pell range

The broad tuple set in `DyadicCountingReduction` deliberately forgets the
parity branch and the original fundamental Pell solution.  Those data are
needed in the unbalanced range: parity makes the shift squarefree in the
difference-two branch, and fundamental minimality excludes the shift `-1` in
the difference-one branch.

This candidate retains the original solution until those two assertions have
been proved.  It then filters only the unbalanced half of the broad tuple set
and gives a finite cardinality reduction to the balanced set plus this
admissible unbalanced set.  No analytic estimate is asserted here.
-/

namespace PellPaper

noncomputable section

/-- The arithmetic conditions on a shifted-square parameter required by the
uniform unbalanced estimate. -/
def ShiftAdmissible (h : ℤ) (v : ℕ) : Prop :=
  Squarefree (shiftedSquareA h v) ∧ shiftedSquareA h v ≠ -1

/-- A factor tuple has an admissible shift when its literal signed difference
produces a squarefree shifted-square parameter different from `-1`. -/
def DyadicShiftAdmissible (d e u v : ℕ) : Prop :=
  ∃ h : ℤ, IsSignedDyadicDifference h ∧
    (e : ℤ) ^ 2 * v - (d : ℤ) ^ 2 * u = h ∧ ShiftAdmissible h v

/-- The unbalanced part of the broad dyadic tuple set on which the
shifted-square parameter has the two required arithmetic properties. -/
noncomputable def admissibleUnbalancedDyadicFactorTuples
    (θ : ℝ) (Y R : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) := by
  classical
  exact (unbalancedDyadicFactorTuples θ Y R).filter fun p =>
    DyadicShiftAdmissible p.1 p.2.1 p.2.2.1 p.2.2.2

@[simp] theorem mem_admissibleUnbalancedDyadicFactorTuples
    {θ : ℝ} {Y R d e u v : ℕ} :
    (d, e, u, v) ∈ admissibleUnbalancedDyadicFactorTuples θ Y R ↔
      DyadicFactorCondition θ Y d e u v ∧ v < R ∧
        DyadicShiftAdmissible d e u v := by
  classical
  simp [admissibleUnbalancedDyadicFactorTuples, and_assoc]

private theorem squarefree_neg_natCast {v : ℕ} (hv : Squarefree v) :
    Squarefree (-(v : ℤ)) := by
  have hvz : Squarefree (v : ℤ) := Int.squarefree_natCast.mpr hv
  exact ((Associated.refl (v : ℤ)).neg_left.squarefree_iff).mpr hvz

private theorem squarefree_two_mul_natCast {v : ℕ}
    (hv : Squarefree v) (hodd : Odd v) :
    Squarefree ((2 * v : ℕ) : ℤ) := by
  have htwo : Squarefree (2 * v) :=
    (Nat.squarefree_mul hodd.coprime_two_left).mpr
      ⟨Nat.squarefree_two, hv⟩
  exact Int.squarefree_natCast.mpr htwo

private theorem squarefree_neg_two_mul_natCast {v : ℕ}
    (hv : Squarefree v) (hodd : Odd v) :
    Squarefree (-((2 * v : ℕ) : ℤ)) := by
  have hvz := squarefree_two_mul_natCast hv hodd
  exact ((Associated.refl ((2 * v : ℕ) : ℤ)).neg_left.squarefree_iff).mpr hvz

private theorem shiftAdmissible_one {v : ℕ} (hv : Squarefree v)
    (hne : shiftedSquareA 1 v ≠ -1) : ShiftAdmissible 1 v := by
  refine ⟨?_, hne⟩
  simpa [shiftedSquareA] using squarefree_neg_natCast hv

private theorem shiftAdmissible_neg_one {v : ℕ}
    (hvpos : 0 < v) (hv : Squarefree v) : ShiftAdmissible (-1) v := by
  refine ⟨?_, ?_⟩
  · simpa [shiftedSquareA] using (Int.squarefree_natCast.mpr hv)
  · have hvz : (0 : ℤ) < v := by exact_mod_cast hvpos
    simp only [shiftedSquareA]
    norm_num
    linarith

private theorem shiftAdmissible_two {v : ℕ}
    (hvpos : 0 < v) (hv : Squarefree v) (hodd : Odd v) :
    ShiftAdmissible 2 v := by
  refine ⟨?_, ?_⟩
  · simpa [shiftedSquareA] using squarefree_neg_two_mul_natCast hv hodd
  · have hvz : (0 : ℤ) < v := by exact_mod_cast hvpos
    simp only [shiftedSquareA]
    norm_num
    intro h
    nlinarith

private theorem shiftAdmissible_neg_two {v : ℕ}
    (hvpos : 0 < v) (hv : Squarefree v) (hodd : Odd v) :
    ShiftAdmissible (-2) v := by
  refine ⟨?_, ?_⟩
  · simpa [shiftedSquareA] using squarefree_two_mul_natCast hv hodd
  · have hvz : (0 : ℤ) < v := by exact_mod_cast hvpos
    simp only [shiftedSquareA]
    norm_num
    linarith

private theorem odd_right_factor_of_even_x_add_one
    {x : ℤ} {e v : ℕ} (hx : Even x)
    (hplus : x + 1 = (e : ℤ) ^ 2 * v) : Odd v := by
  have hoddProduct : Odd ((e : ℤ) ^ 2 * v) := by
    rw [← hplus]
    exact hx.add_odd (by norm_num)
  have hoddCast : Odd (v : ℤ) := Int.Odd.of_mul_right hoddProduct
  exact_mod_cast hoddCast

private theorem odd_right_factor_of_even_x_sub_one
    {x : ℤ} {d u : ℕ} (hx : Even x)
    (hminus : x - 1 = (d : ℤ) ^ 2 * u) : Odd u := by
  have hoddProduct : Odd ((d : ℤ) ^ 2 * u) := by
    rw [← hminus]
    have hnegOne : Odd (-1 : ℤ) := by norm_num
    simpa only [sub_eq_add_neg] using hx.add_odd hnegOne
  have hoddCast : Odd (u : ℤ) := Int.Odd.of_mul_right hoddProduct
  exact_mod_cast hoddCast

/-- Oriented factor separation with the shift certificate retained.  Unlike
`pell_factor_separation_oriented`, the fundamental-solution hypothesis is kept
long enough to exclude `h=1, v=1`, and the exact parity branch is kept long
enough to prove squarefreeness when `|h|=2`. -/
theorem pell_factor_separation_oriented_shiftAdmissible
    {m : ℕ} (a : Pell.Solution₁ (m : ℤ))
    (hm : 0 < m) (hsm : Squarefree m) (ha : Pell.IsFundamental a) :
    ∃ (d e u v : ℕ) (h : ℤ),
      0 < d ∧ 0 < e ∧ 0 < u ∧ 0 < v ∧
      Squarefree u ∧ Squarefree v ∧ u.Coprime v ∧ u * v = m ∧ v ≤ u ∧
      IsSignedDyadicDifference h ∧
      (e : ℤ) ^ 2 * v - (d : ℤ) ^ 2 * u = h ∧
      (a.y = (d : ℤ) * e ∨ a.y = 2 * (d : ℤ) * e) ∧
      ShiftAdmissible h v := by
  rcases Int.even_or_odd a.x with heven | hodd
  · obtain ⟨d, e, u, v, hd, he, hu, hv, hminus, hplus,
        hsu, hsv, huv, hmuv, hdiff, hy⟩ :=
      pell_factor_separation_of_even a hm hsm ha.1 ha.2.1 heven
    have huOdd : Odd u :=
      odd_right_factor_of_even_x_sub_one heven hminus
    have hvOdd : Odd v :=
      odd_right_factor_of_even_x_add_one heven hplus
    rcases le_total v u with hvu | huv'
    · exact ⟨d, e, u, v, 2, hd, he, hu, hv, hsu, hsv, huv, hmuv, hvu,
        Or.inr (Or.inr (Or.inl rfl)), hdiff, Or.inl hy,
        shiftAdmissible_two hv hsv hvOdd⟩
    · refine ⟨e, d, v, u, -2, he, hd, hv, hu, hsv, hsu, huv.symm,
        ?_, huv', Or.inr (Or.inr (Or.inr rfl)), ?_, ?_,
        shiftAdmissible_neg_two hu hsu huOdd⟩
      · simpa only [mul_comm] using hmuv
      · linarith [hdiff]
      · exact Or.inl (by simpa only [mul_comm (d : ℤ) (e : ℤ)] using hy)
  · obtain ⟨d, e, u, v, hd, he, hu, hv, hminus, hplus,
        hsu, hsv, huv, hmuv, hdiff, hy⟩ :=
      pell_factor_separation_of_odd a hm hsm ha.1 ha.2.1 hodd
    rcases le_total v u with hvu | huv'
    · have hne : shiftedSquareA 1 v ≠ -1 :=
        odd_factor_data_shiftedSquareA_ne_neg_one_of_isFundamental
          a ha hodd hd he hu hminus hplus hy hmuv
      exact ⟨d, e, u, v, 1, hd, he, hu, hv, hsu, hsv, huv, hmuv, hvu,
        Or.inl rfl, hdiff, Or.inr hy, shiftAdmissible_one hsv hne⟩
    · refine ⟨e, d, v, u, -1, he, hd, hv, hu, hsv, hsu, huv.symm,
        ?_, huv', Or.inr (Or.inl rfl), ?_, ?_,
        shiftAdmissible_neg_one hu hsu⟩
      · simpa only [mul_comm] using hmuv
      · linarith [hdiff]
      · exact Or.inr (by
          simpa only [mul_comm (d : ℤ) (e : ℤ), mul_assoc,
            mul_left_comm (d : ℤ)] using hy)

/-- Every dyadic squarefree exception has bounded oriented factor data whose
shift is squarefree and different from `-1`.  The original fundamental
solution and its `y`-coordinate relation remain in the conclusion. -/
theorem dyadic_exception_has_admissible_bounded_factors
    {θ : ℝ} {Y m : ℕ} (hθ : 0 ≤ θ)
    (hm : m ∈ squarefreeDyadicExceptionalSet θ Y) :
    ∃ (a : Pell.Solution₁ (m : ℤ)) (d e u v : ℕ) (h : ℤ),
      Pell.IsFundamental a ∧ epsilon a ≤ (m : ℝ) ^ θ ∧
      DyadicFactorCondition θ Y d e u v ∧ u * v = m ∧
      IsSignedDyadicDifference h ∧
      (e : ℤ) ^ 2 * v - (d : ℤ) ^ 2 * u = h ∧
      ShiftAdmissible h v ∧
      (a.y = (d : ℤ) * e ∨ a.y = 2 * (d : ℤ) * e) := by
  obtain ⟨hmlo, hmhi, hsm, a, ha, hsmall⟩ :=
    mem_squarefreeDyadicExceptionalSet.mp hm
  have hmpos : 0 < m := by exact_mod_cast ha.d_pos
  obtain ⟨d, e, u, v, h, hd, he, hu, hv, hsu, hsv, hcop, huv,
      hvu, hh, hdiff, hy, hshift⟩ :=
    pell_factor_separation_oriented_shiftAdmissible a hmpos hsm ha
  have hyR : 0 ≤ (a.y : ℝ) := by exact_mod_cast ha.2.1.le
  have hroot : 1 ≤ Real.sqrt (m : ℝ) :=
    Real.one_le_sqrt.mpr (by exact_mod_cast hmpos)
  have hysqrt : (a.y : ℝ) * Real.sqrt (m : ℝ) ≤ epsilon a := by
    simp only [epsilon, Int.cast_natCast]
    have hxR : 0 ≤ (a.x : ℝ) := by exact_mod_cast ha.x_pos.le
    linarith
  have hyunit : (a.y : ℝ) ≤ epsilon a :=
    (le_mul_of_one_le_right hyR hroot).trans hysqrt
  have hheight : epsilon a ≤ ((2 * Y : ℕ) : ℝ) ^ θ :=
    hsmall.trans (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hmhi.le) hθ)
  have hde : (d : ℤ) * e ≤ a.y := by
    rcases hy with hy | hy
    · exact hy.ge
    · rw [hy]
      have hnonneg : (0 : ℤ) ≤ (d : ℤ) * e := by positivity
      nlinarith
  have hdeR : ((d * e : ℕ) : ℝ) ≤ (a.y : ℝ) := by exact_mod_cast hde
  have hdde : d ≤ d * e := Nat.le_mul_of_pos_right d he
  have hede : e ≤ d * e := Nat.le_mul_of_pos_left e hd
  have hdeheight : ((d * e : ℕ) : ℝ) ≤ (dyadicFactorHeight θ Y : ℝ) :=
    hdeR.trans (hyunit.trans (hheight.trans (Nat.le_ceil _)))
  have hdheight : d ≤ dyadicFactorHeight θ Y := by
    exact_mod_cast (le_trans (by exact_mod_cast hdde : (d : ℝ) ≤ (d * e : ℕ)) hdeheight)
  have heheight : e ≤ dyadicFactorHeight θ Y := by
    exact_mod_cast (le_trans (by exact_mod_cast hede : (e : ℝ) ≤ (d * e : ℕ)) hdeheight)
  have hum : u ≤ m := huv ▸ Nat.le_mul_of_pos_right u hv
  have hvm : v ≤ m := huv ▸ Nat.le_mul_of_pos_left v hu
  have hvsmall : v ^ 2 < 2 * Y := by
    have hsq : v * v ≤ u * v := Nat.mul_le_mul_right v hvu
    rw [huv] at hsq
    nlinarith
  have hprodheight :
      ((d * e : ℕ) : ℝ) * Real.sqrt (Y : ℝ) ≤ ((2 * Y : ℕ) : ℝ) ^ θ := by
    calc
      _ ≤ (a.y : ℝ) * Real.sqrt (Y : ℝ) :=
        mul_le_mul_of_nonneg_right hdeR (Real.sqrt_nonneg _)
      _ ≤ (a.y : ℝ) * Real.sqrt (m : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by exact_mod_cast hmlo)) hyR
      _ ≤ epsilon a := hysqrt
      _ ≤ ((2 * Y : ℕ) : ℝ) ^ θ := hheight
  have hcondition : DyadicFactorCondition θ Y d e u v := by
    refine ⟨hd, he, hu, hv, hdheight, heheight, hum.trans_lt hmhi,
      hvm.trans_lt hmhi, hsu, hsv, hcop, huv ▸ hmlo, huv ▸ hmhi, hvu,
      hvsmall, ?_, hprodheight⟩
    rcases hh with rfl | rfl | rfl | rfl
    · exact Or.inl hdiff
    · exact Or.inr (Or.inl hdiff)
    · exact Or.inr (Or.inr (Or.inl hdiff))
    · exact Or.inr (Or.inr (Or.inr hdiff))
  exact ⟨a, d, e, u, v, h, ha, hsmall, hcondition, huv, hh,
    hdiff, hshift, hy⟩

/-- Every squarefree dyadic exceptional radicand belongs to the product image
of the balanced tuple set or to the product image of the admissible
unbalanced tuple set. -/
theorem squarefreeDyadicExceptionalSet_subset_balanced_union_admissibleUnbalanced_image
    {θ : ℝ} {Y R : ℕ} (hθ : 0 ≤ θ) :
    squarefreeDyadicExceptionalSet θ Y ⊆
      (balancedDyadicFactorTuples θ Y R).image
          (fun p => p.2.2.1 * p.2.2.2) ∪
        (admissibleUnbalancedDyadicFactorTuples θ Y R).image
          (fun p => p.2.2.1 * p.2.2.2) := by
  classical
  intro m hm
  obtain ⟨a, d, e, u, v, h, _ha, _hsmall, hcond, huv, hh,
      hdiff, hshift, _hy⟩ :=
    dyadic_exception_has_admissible_bounded_factors hθ hm
  by_cases hR : R ≤ v
  · apply Finset.mem_union_left
    exact Finset.mem_image.mpr
      ⟨(d, e, u, v), mem_balancedDyadicFactorTuples.mpr
        ⟨mem_dyadicFactorTuples.mpr hcond, hR⟩, huv⟩
  · have hvR : v < R := Nat.lt_of_not_ge hR
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨(d, e, u, v),
      mem_admissibleUnbalancedDyadicFactorTuples.mpr ?_, huv⟩
    exact ⟨hcond, hvR, h, hh, hdiff, hshift⟩

/-- The finite counting reduction with the analytically valid unbalanced
target.  This is the cardinality interface needed before introducing
shifted-square blocks. -/
theorem squarefreeDyadicExceptionalCount_le_balanced_add_admissibleUnbalanced
    {θ : ℝ} {Y R : ℕ} (hθ : 0 ≤ θ) :
    squarefreeDyadicExceptionalCount θ Y ≤
      (balancedDyadicFactorTuples θ Y R).card +
        (admissibleUnbalancedDyadicFactorTuples θ Y R).card := by
  classical
  let f : ℕ × ℕ × ℕ × ℕ → ℕ := fun p => p.2.2.1 * p.2.2.2
  calc
    squarefreeDyadicExceptionalCount θ Y =
        (squarefreeDyadicExceptionalSet θ Y).card := rfl
    _ ≤ ((balancedDyadicFactorTuples θ Y R).image f ∪
          (admissibleUnbalancedDyadicFactorTuples θ Y R).image f).card :=
      Finset.card_le_card
        (squarefreeDyadicExceptionalSet_subset_balanced_union_admissibleUnbalanced_image hθ)
    _ ≤ ((balancedDyadicFactorTuples θ Y R).image f).card +
          ((admissibleUnbalancedDyadicFactorTuples θ Y R).image f).card :=
      Finset.card_union_le _ _
    _ ≤ (balancedDyadicFactorTuples θ Y R).card +
          (admissibleUnbalancedDyadicFactorTuples θ Y R).card :=
      Nat.add_le_add Finset.card_image_le Finset.card_image_le

end

end PellPaper
