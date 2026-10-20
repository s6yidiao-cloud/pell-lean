import Pell.QuadraticOrderDiscriminants
import Pell.QuadraticFormProperEquivalence

/-!
# Finiteness of proper form classes for positive order discriminants

Every primitive integral form of a positive nonsquare discriminant is properly
equivalent to one whose three coefficients are bounded in absolute value by
the discriminant.  This gives finiteness of the literal proper-equivalence
quotient without using the form--ideal correspondence for nonmaximal orders.
-/

namespace PellPaper

open scoped MatrixGroups

namespace IntegralBinaryQuadraticForm

noncomputable section

/-- The determinant-one shear sending `[a,b,c]` to a form with middle
coefficient `b + 2ak`. -/
private def orderReductionShear (k : ℤ) : SL(2, ℤ) :=
  ⟨!![1, k; 0, 1], by norm_num [Matrix.det_fin_two]⟩

/-- The determinant-one interchange of the two variables. -/
private def orderReductionSwap : SL(2, ℤ) :=
  ⟨!![0, -1; 1, 0], by norm_num [Matrix.det_fin_two]⟩

@[simp]
private theorem properTransform_orderReductionShear_a
    (Q : IntegralBinaryQuadraticForm) (k : ℤ) :
    (Q.properTransform (orderReductionShear k)).a = Q.a := by
  simp [orderReductionShear, properTransform]

@[simp]
private theorem properTransform_orderReductionShear_b
    (Q : IntegralBinaryQuadraticForm) (k : ℤ) :
    (Q.properTransform (orderReductionShear k)).b = Q.b + 2 * Q.a * k := by
  simp [orderReductionShear, properTransform]
  ring

@[simp]
private theorem properTransform_orderReductionSwap_coefficients
    (Q : IntegralBinaryQuadraticForm) :
    (Q.properTransform orderReductionSwap).a = Q.c ∧
      (Q.properTransform orderReductionSwap).b = -Q.b ∧
      (Q.properTransform orderReductionSwap).c = Q.a := by
  norm_num [orderReductionSwap, properTransform]

/-- An integral shear can place the middle coefficient in the symmetric
interval of radius `|a|`. -/
private theorem exists_shear_middle_abs_le (a b : ℤ) (ha : a ≠ 0) :
    ∃ k : ℤ, |b + 2 * a * k| ≤ |a| := by
  let m : ℤ := |a|
  let t : ℤ := 2 * m
  let r : ℤ := b % t
  have hm : 0 < m := abs_pos.mpr ha
  have ht : 0 < t := by dsimp [t]; omega
  have hr0 : 0 ≤ r := Int.emod_nonneg _ ht.ne'
  have hrt : r < t := Int.emod_lt_of_pos _ ht
  by_cases hrm : r ≤ m
  · have hdiv : 2 * a ∣ r - b := by
      have htdiv : 2 * a ∣ t := by
        dsimp [t, m]
        by_cases ha0 : 0 ≤ a
        · rw [abs_of_nonneg ha0]
        · rw [abs_of_neg (lt_of_not_ge ha0)]
          exact ⟨-1, by ring⟩
      have htb : t ∣ r - b := by
        refine ⟨-(b / t), ?_⟩
        have hrem := Int.emod_add_mul_ediv b t
        dsimp [r]
        linarith
      exact dvd_trans htdiv htb
    rcases hdiv with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have heq : b + 2 * a * k = r := by linarith
    rw [heq, abs_of_nonneg hr0]
    exact hrm
  · have hmr : m < r := lt_of_not_ge hrm
    have hdiv : 2 * a ∣ (r - t) - b := by
      have htdiv : 2 * a ∣ t := by
        dsimp [t, m]
        by_cases ha0 : 0 ≤ a
        · rw [abs_of_nonneg ha0]
        · rw [abs_of_neg (lt_of_not_ge ha0)]
          exact ⟨-1, by ring⟩
      have htb : t ∣ r - b := by
        refine ⟨-(b / t), ?_⟩
        have hrem := Int.emod_add_mul_ediv b t
        dsimp [r]
        linarith
      have hdiff : 2 * a ∣ r - b := dvd_trans htdiv htb
      have hsub : 2 * a ∣ (r - b) - t := dvd_sub hdiff htdiv
      convert hsub using 1
      ring
    rcases hdiv with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have heq : b + 2 * a * k = r - t := by linarith
    rw [heq, abs_le]
    constructor <;> dsimp [t] at * <;> omega

/-- Every primitive form of a positive nonsquare order discriminant has a
properly equivalent representative whose three coefficients have absolute
value at most the discriminant. -/
theorem exists_bounded_properEquivalent_of_positiveQuadraticOrderDiscriminant
    {D : ℕ} (hD : PositiveQuadraticOrderDiscriminant D)
    (Q : PrimitiveBinaryQuadraticForms (D : ℤ)) :
    ∃ R : PrimitiveBinaryQuadraticForms (D : ℤ),
      ProperEquivalent Q R ∧
        R.1.a.natAbs ≤ D ∧ R.1.b.natAbs ≤ D ∧ R.1.c.natAbs ≤ D := by
  classical
  let P : ℕ → Prop := fun n ↦
    ∃ R : PrimitiveBinaryQuadraticForms (D : ℤ),
      ProperEquivalent Q R ∧ R.1.a.natAbs = n
  have hP : ∃ n, P n :=
    ⟨Q.1.a.natAbs, Q, properEquivalent_refl Q, rfl⟩
  let m := Nat.find hP
  obtain ⟨R, hQR, hRa⟩ := Nat.find_spec hP
  have hmin (T : PrimitiveBinaryQuadraticForms (D : ℤ))
      (hQT : ProperEquivalent Q T) : R.1.a.natAbs ≤ T.1.a.natAbs := by
    rw [hRa]
    exact Nat.find_min' hP ⟨T, hQT, rfl⟩
  have hRane : R.1.a ≠ 0 := by
    intro ha0
    apply hD.2.1
    refine ⟨R.1.b.natAbs, ?_⟩
    have hdisc : (D : ℤ) = R.1.b ^ 2 := by
      have hdiscR := R.2.2
      simp [discriminant, ha0] at hdiscR
      exact hdiscR.symm
    have hsquareInt : (D : ℤ) = (R.1.b.natAbs : ℤ) ^ 2 := by
      calc
        (D : ℤ) = R.1.b ^ 2 := hdisc
        _ = |R.1.b| ^ 2 := (sq_abs R.1.b).symm
        _ = (R.1.b.natAbs : ℤ) ^ 2 := by rw [Int.natCast_natAbs]
    have hsquareNat : D = R.1.b.natAbs ^ 2 := by exact_mod_cast hsquareInt
    simpa [pow_two] using hsquareNat
  obtain ⟨k, hk⟩ := exists_shear_middle_abs_le R.1.a R.1.b hRane
  let S : PrimitiveBinaryQuadraticForms (D : ℤ) :=
    properTransformAt R (orderReductionShear k)
  have hRS : ProperEquivalent R S := ⟨orderReductionShear k, rfl⟩
  have hQS : ProperEquivalent Q S := properEquivalent_trans hQR hRS
  have hSa : S.1.a = R.1.a := by
    simp [S, properTransformAt]
  have hSb : S.1.b = R.1.b + 2 * R.1.a * k := by
    simp [S, properTransformAt]
  have hba : |S.1.b| ≤ |S.1.a| := by simpa [hSa, hSb] using hk
  let T : PrimitiveBinaryQuadraticForms (D : ℤ) :=
    properTransformAt S orderReductionSwap
  have hST : ProperEquivalent S T := ⟨orderReductionSwap, rfl⟩
  have hQT : ProperEquivalent Q T := properEquivalent_trans hQS hST
  have hTac : T.1.a = S.1.c := by
    simp [T, properTransformAt]
  have hacNat : S.1.a.natAbs ≤ S.1.c.natAbs := by
    rw [hSa, ← hTac]
    exact hmin T hQT
  have hac : |S.1.a| ≤ |S.1.c| := by
    rw [← Int.natCast_natAbs, ← Int.natCast_natAbs]
    exact_mod_cast hacNat
  have hSane : S.1.a ≠ 0 := hSa.trans_ne hRane
  have hScne : S.1.c ≠ 0 := by
    intro hc0
    have ha0 : S.1.a = 0 := by
      have h := hacNat
      simpa [hc0] using h
    exact hSane ha0
  have hacneg : S.1.a * S.1.c < 0 := by
    by_contra hn
    have hac0 : 0 ≤ S.1.a * S.1.c := le_of_not_gt hn
    have hb_sq : S.1.b ^ 2 ≤ S.1.a ^ 2 := sq_le_sq.mpr hba
    have hac_sq : S.1.a ^ 2 ≤ S.1.a * S.1.c := by
      rcases lt_or_gt_of_ne hSane with ha | ha
      · have hc : S.1.c < 0 := by
          have hc0 : S.1.c ≤ 0 := by
            by_contra hn0
            have hcpos : 0 < S.1.c := lt_of_not_ge hn0
            exact (not_lt_of_ge hac0) (mul_neg_of_neg_of_pos ha hcpos)
          exact lt_of_le_of_ne hc0 hScne
        rw [abs_of_neg ha, abs_of_neg hc] at hac
        nlinarith
      · have hc : 0 < S.1.c := by
          have hc0 : 0 ≤ S.1.c := by
            by_contra hn0
            have hcneg : S.1.c < 0 := lt_of_not_ge hn0
            exact (not_lt_of_ge hac0) (mul_neg_of_pos_of_neg ha hcneg)
          exact lt_of_le_of_ne hc0 (Ne.symm hScne)
        rw [abs_of_pos ha, abs_of_pos hc] at hac
        nlinarith
    have hDpos : 0 < (D : ℤ) := by exact_mod_cast hD.1
    have hdisc := S.2.2
    simp only [discriminant] at hdisc
    nlinarith [sq_pos_of_ne_zero hSane]
  have hdiscAbs :
      (D : ℤ) = S.1.b ^ 2 + 4 * |S.1.a| * |S.1.c| := by
    have hdisc := S.2.2
    simp only [discriminant] at hdisc
    have habs : |S.1.a| * |S.1.c| = -(S.1.a * S.1.c) := by
      rw [← abs_mul, abs_of_neg hacneg]
    nlinarith [hdisc, habs]
  have ha1 : 1 ≤ |S.1.a| := (Int.add_one_le_iff).mpr (abs_pos.mpr hSane)
  have hc1 : 1 ≤ |S.1.c| := (Int.add_one_le_iff).mpr (abs_pos.mpr hScne)
  have hDa : |S.1.a| ≤ (D : ℤ) := by
    nlinarith [sq_nonneg S.1.b, mul_nonneg (abs_nonneg S.1.a) (abs_nonneg S.1.c)]
  have hDb : |S.1.b| ≤ (D : ℤ) := hba.trans hDa
  have hDc : |S.1.c| ≤ (D : ℤ) := by
    nlinarith [sq_nonneg S.1.b, mul_nonneg (abs_nonneg S.1.a) (abs_nonneg S.1.c)]
  refine ⟨S, hQS, ?_, ?_, ?_⟩
  · have : (S.1.a.natAbs : ℤ) ≤ (D : ℤ) := by
      simpa only [Int.natCast_natAbs] using hDa
    exact_mod_cast this
  · have : (S.1.b.natAbs : ℤ) ≤ (D : ℤ) := by
      simpa only [Int.natCast_natAbs] using hDb
    exact_mod_cast this
  · have : (S.1.c.natAbs : ℤ) ≤ (D : ℤ) := by
      simpa only [Int.natCast_natAbs] using hDc
    exact_mod_cast this

/-- Proper-equivalence classes of primitive forms of every positive nonsquare
order discriminant are finite. -/
theorem finite_properFormClass_of_positiveQuadraticOrderDiscriminant
    {D : ℕ} (hD : PositiveQuadraticOrderDiscriminant D) :
    Finite (ProperFormClass (D : ℤ)) := by
  classical
  let ZD : Set ℤ := {z | z.natAbs ≤ D}
  have hZD : ZD.Finite :=
    (Set.finite_Icc (-(D : ℤ)) (D : ℤ)).subset (by
      intro z hz
      change z.natAbs ≤ D at hz
      have hz' : |z| ≤ (D : ℤ) := by
        rw [← Int.natCast_natAbs]
        exact_mod_cast hz
      exact abs_le.mp hz')
  let _ : Finite ZD := hZD.to_subtype
  let B := {Q : PrimitiveBinaryQuadraticForms (D : ℤ) //
    Q.1.a.natAbs ≤ D ∧ Q.1.b.natAbs ≤ D ∧ Q.1.c.natAbs ≤ D}
  let e : B → ZD × ZD × ZD := fun Q ↦
    (⟨Q.1.1.a, Q.2.1⟩, ⟨Q.1.1.b, Q.2.2.1⟩, ⟨Q.1.1.c, Q.2.2.2⟩)
  have he : Function.Injective e := by
    intro Q R hQR
    apply Subtype.ext
    apply Subtype.ext
    apply IntegralBinaryQuadraticForm.ext
    · exact congrArg (fun z : ZD × ZD × ZD ↦ (z.1 : ℤ)) hQR
    · exact congrArg (fun z : ZD × ZD × ZD ↦ (z.2.1 : ℤ)) hQR
    · exact congrArg (fun z : ZD × ZD × ZD ↦ (z.2.2 : ℤ)) hQR
  let _ : Finite B := Finite.of_injective e he
  let f : B → ProperFormClass (D : ℤ) := fun Q ↦
    PrimitiveBinaryQuadraticForms.toProperFormClass Q.1
  apply Finite.of_surjective f
  intro C
  obtain ⟨Q, hQC⟩ := Quotient.exists_rep C
  obtain ⟨R, hQR, ha, hb, hc⟩ :=
    exists_bounded_properEquivalent_of_positiveQuadraticOrderDiscriminant hD Q
  refine ⟨⟨R, ha, hb, hc⟩, ?_⟩
  change PrimitiveBinaryQuadraticForms.toProperFormClass R = C
  change PrimitiveBinaryQuadraticForms.toProperFormClass Q = C at hQC
  exact (PrimitiveBinaryQuadraticForms.toProperFormClass_eq_of_properEquivalent hQR).symm.trans
    hQC

end
end IntegralBinaryQuadraticForm
end PellPaper
