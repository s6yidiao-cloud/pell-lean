import Pell.ShearedCenterExponentFormula

/-!
# Local denominator and centre cost for the sheared determinant

The determinant endpoint needs a bound for the row-denominator product after
the centre `s₀` has been extracted.  In the dyadic factor coordinates of
`L:sheared`, the scale relation `(D / E)^2 = V / U` rewrites that product in
terms of the symmetric products `D * E` and `U * V`.  This module records the
elementary algebra and a finite-product bound separately from the still
source-specific interval estimates.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- The elementary dyadic scale identity behind the centre/denominator cost.
The exponents `a` and `b` are the half-cardinality contributions of the two
bidegrees. -/
theorem dyadic_center_denominator_scale_identity
    (D E U V : ℝ) (a b : ℕ)
    (hscale : (D / E) ^ 2 = V / U) :
    (E ^ (2 * a) * U ^ (2 * b)) * (D / E) ^ (a + 2 * b) =
      (D * E) ^ a * (U * V) ^ b := by
  have hsource : E ^ (2 * a) * (D / E) ^ a = (D * E) ^ a := by
    rw [show 2 * a = a + a by omega, pow_add, div_pow]
    field_simp
    ring
  have htarget : U ^ (2 * b) * (V / U) ^ b = (U * V) ^ b := by
    rw [show 2 * b = b + b by omega, pow_add, div_pow]
    field_simp
    ring
  calc
    (E ^ (2 * a) * U ^ (2 * b)) * (D / E) ^ (a + 2 * b) =
        (E ^ (2 * a) * (D / E) ^ a) *
          (U ^ (2 * b) * ((D / E) ^ 2) ^ b) := by
            rw [pow_add, pow_mul]
            ring
    _ = (E ^ (2 * a) * (D / E) ^ a) *
          (U ^ (2 * b) * (V / U) ^ b) := by rw [hscale]
    _ = (D * E) ^ a * (U * V) ^ b := by rw [hsource, htarget]

/-- The source-degree contribution has an integral half-cardinality. -/
theorem two_mul_sourceDegree_card_half (A B : ℕ) :
    2 * (A * ((A + 1) * (B + 1)) / 2) =
      A * ((A + 1) * (B + 1)) := by
  apply Nat.two_mul_div_two_of_even
  have hAA : Even (A * (A + 1)) := Nat.even_mul_succ_self A
  rw [show A * ((A + 1) * (B + 1)) = (A * (A + 1)) * (B + 1) by ring]
  exact even_iff_two_dvd.mpr (dvd_mul_of_dvd_left hAA.two_dvd (B + 1))

/-- The target-degree contribution has an integral half-cardinality. -/
theorem two_mul_targetDegree_card_half (A B : ℕ) :
    2 * (B * ((A + 1) * (B + 1)) / 2) =
      B * ((A + 1) * (B + 1)) := by
  apply Nat.two_mul_div_two_of_even
  have hBB : Even (B * (B + 1)) := Nat.even_mul_succ_self B
  rw [show B * ((A + 1) * (B + 1)) = (B * (B + 1)) * (A + 1) by ring]
  exact even_iff_two_dvd.mpr (dvd_mul_of_dvd_left hBB.two_dvd (A + 1))

/-- The full sheared centre exponent splits into the source half-cardinality
and twice the target half-cardinality. -/
theorem shearedCenterExponent_closedForm_split (A B : ℕ) :
    ((A + 1) * (B + 1) * (A + 2 * B)) / 2 =
      A * ((A + 1) * (B + 1)) / 2 +
        2 * (B * ((A + 1) * (B + 1)) / 2) := by
  have hA := two_mul_sourceDegree_card_half A B
  have hB := two_mul_targetDegree_card_half A B
  have htwice :
      2 * (A * ((A + 1) * (B + 1)) / 2 +
        2 * (B * ((A + 1) * (B + 1)) / 2)) =
        (A + 1) * (B + 1) * (A + 2 * B) := by
    calc
      2 * (A * ((A + 1) * (B + 1)) / 2 +
        2 * (B * ((A + 1) * (B + 1)) / 2)) =
          2 * (A * ((A + 1) * (B + 1)) / 2) +
            2 * (B * ((A + 1) * (B + 1)) / 2) * 2 := by ring
      _ = A * ((A + 1) * (B + 1)) +
            B * ((A + 1) * (B + 1)) * 2 := by rw [hA, hB]
      _ = (A + 1) * (B + 1) * (A + 2 * B) := by ring
  have hdiv : 2 ∣ (A + 1) * (B + 1) * (A + 2 * B) :=
    ⟨A * ((A + 1) * (B + 1)) / 2 +
      2 * (B * ((A + 1) * (B + 1)) / 2), htwice.symm⟩
  exact (Nat.div_eq_iff_eq_mul_right (by norm_num) hdiv).mpr htwice.symm

/-- With `H = (A+1)(B+1)`, the dyadic scale identity gives exactly the
centre and denominator cost displayed in `L:sheared`. -/
theorem sheared_dyadic_center_denominator_scale_identity
    (A B : ℕ) (D E U V : ℝ)
    (hscale : (D / E) ^ 2 = V / U) :
    (E ^ A * U ^ B) ^ ((A + 1) * (B + 1)) *
        (D / E) ^ (((A + 1) * (B + 1) * (A + 2 * B)) / 2) =
      (D * E) ^ (A * ((A + 1) * (B + 1)) / 2) *
        (U * V) ^ (B * ((A + 1) * (B + 1)) / 2) := by
  have hA := two_mul_sourceDegree_card_half A B
  have hB := two_mul_targetDegree_card_half A B
  have hcentre := shearedCenterExponent_closedForm_split A B
  have hEpow : E ^ (A * ((A + 1) * (B + 1))) =
      E ^ (2 * (A * ((A + 1) * (B + 1)) / 2)) := by
    congr 1
    exact hA.symm
  have hUpow : U ^ (B * ((A + 1) * (B + 1))) =
      U ^ (2 * (B * ((A + 1) * (B + 1)) / 2)) := by
    congr 1
    exact hB.symm
  have hcentrePow : (D / E) ^ (((A + 1) * (B + 1) * (A + 2 * B)) / 2) =
      (D / E) ^ (A * ((A + 1) * (B + 1)) / 2 +
        2 * (B * ((A + 1) * (B + 1)) / 2)) :=
    congrArg (fun n : ℕ => (D / E) ^ n) hcentre
  calc
    (E ^ A * U ^ B) ^ ((A + 1) * (B + 1)) *
        (D / E) ^ (((A + 1) * (B + 1) * (A + 2 * B)) / 2) =
        (E ^ (A * ((A + 1) * (B + 1))) *
          U ^ (B * ((A + 1) * (B + 1)))) *
          (D / E) ^ (((A + 1) * (B + 1) * (A + 2 * B)) / 2) := by
            rw [mul_pow, ← pow_mul, ← pow_mul]
    _ = (E ^ (2 * (A * ((A + 1) * (B + 1)) / 2)) *
          U ^ (2 * (B * ((A + 1) * (B + 1)) / 2))) *
          (D / E) ^ (A * ((A + 1) * (B + 1)) / 2 +
            2 * (B * ((A + 1) * (B + 1)) / 2)) := by
              rw [hEpow, hUpow, hcentrePow]
    _ = (D * E) ^ (A * ((A + 1) * (B + 1)) / 2) *
          (U * V) ^ (B * ((A + 1) * (B + 1)) / 2) :=
      dyadic_center_denominator_scale_identity D E U V
        (A * ((A + 1) * (B + 1)) / 2)
        (B * ((A + 1) * (B + 1)) / 2) hscale

/-- Rowwise bounds on the two denominators and the local centre give an
explicit bound for the cleared determinant multiplier. -/
theorem abs_rowDenominator_center_le_of_abs_le
    {ι : Type*} [Fintype ι]
    (A B K : ℕ) (e u : ι → ℝ) (s E U S : ℝ)
    (hE : 0 ≤ E) (hU : 0 ≤ U)
    (he : ∀ i, |e i| ≤ E) (hu : ∀ i, |u i| ≤ U)
    (hs : |s| ≤ S) :
    |(∏ i, e i ^ A * u i ^ B) * s ^ K| ≤
      (E ^ A * U ^ B) ^ Fintype.card ι * S ^ K := by
  have hrow_nonneg : ∀ i : ι, 0 ≤ |e i| ^ A * |u i| ^ B := by
    intro i
    positivity
  have hrow_le : ∀ i : ι, |e i| ^ A * |u i| ^ B ≤ E ^ A * U ^ B := by
    intro i
    exact mul_le_mul
      (pow_le_pow_left₀ (abs_nonneg (e i)) (he i) A)
      (pow_le_pow_left₀ (abs_nonneg (u i)) (hu i) B)
      (pow_nonneg (abs_nonneg (u i)) _) (pow_nonneg hE _)
  have hprod : (∏ i, |e i| ^ A * |u i| ^ B) ≤
      ∏ _i : ι, E ^ A * U ^ B := by
    apply Finset.prod_le_prod
    · intro i _
      exact hrow_nonneg i
    · intro i _
      exact hrow_le i
  calc
    |(∏ i, e i ^ A * u i ^ B) * s ^ K| =
        (∏ i, |e i| ^ A * |u i| ^ B) * |s| ^ K := by
          rw [abs_mul, abs_pow, Finset.abs_prod]
          simp_rw [abs_mul, abs_pow]
    _ ≤ (∏ _i : ι, E ^ A * U ^ B) * S ^ K := by
      exact mul_le_mul hprod (pow_le_pow_left₀ (abs_nonneg s) hs K)
        (pow_nonneg (abs_nonneg s) _) (by positivity)
    _ = (E ^ A * U ^ B) ^ Fintype.card ι * S ^ K := by
      rw [Finset.prod_const]
      simp

/-- The rowwise local bounds specialize to the symmetric dyadic cost of
`L:sheared`.  The cardinality hypothesis is deliberately explicit, so this
lemma can be used for any selected full minor, not only the canonical grid. -/
theorem abs_rowDenominator_center_le_shearedDyadicCost
    {ι : Type*} [Fintype ι]
    (A B : ℕ) (e u : ι → ℝ) (s D E U V : ℝ)
    (hcard : Fintype.card ι = (A + 1) * (B + 1))
    (hE : 0 ≤ E) (hU : 0 ≤ U)
    (he : ∀ i, |e i| ≤ E) (hu : ∀ i, |u i| ≤ U)
    (hs : |s| ≤ D / E)
    (hscale : (D / E) ^ 2 = V / U) :
    |(∏ i, e i ^ A * u i ^ B) *
        s ^ (((A + 1) * (B + 1) * (A + 2 * B)) / 2)| ≤
      (D * E) ^ (A * ((A + 1) * (B + 1)) / 2) *
        (U * V) ^ (B * ((A + 1) * (B + 1)) / 2) := by
  calc
    |(∏ i, e i ^ A * u i ^ B) *
        s ^ (((A + 1) * (B + 1) * (A + 2 * B)) / 2)| ≤
        (E ^ A * U ^ B) ^ Fintype.card ι *
          (D / E) ^ (((A + 1) * (B + 1) * (A + 2 * B)) / 2) :=
      abs_rowDenominator_center_le_of_abs_le A B
        (((A + 1) * (B + 1) * (A + 2 * B)) / 2)
        e u s E U (D / E) hE hU he hu hs
    _ = (D * E) ^ (A * ((A + 1) * (B + 1)) / 2) *
          (U * V) ^ (B * ((A + 1) * (B + 1)) / 2) := by
      rw [hcard]
      exact sheared_dyadic_center_denominator_scale_identity A B D E U V hscale

/-- A named exponential upper bound for the symmetric dyadic cost discharges
the `hcost` input of the source-normalized strict determinant endpoint. -/
theorem abs_rowDenominator_center_le_expCost_of_shearedDyadicCost
    {ι : Type*} [Fintype ι]
    (A B : ℕ) (e u : ι → ℝ) (s D E U V cost : ℝ)
    (hcard : Fintype.card ι = (A + 1) * (B + 1))
    (hE : 0 ≤ E) (hU : 0 ≤ U)
    (he : ∀ i, |e i| ≤ E) (hu : ∀ i, |u i| ≤ U)
    (hs : |s| ≤ D / E)
    (hscale : (D / E) ^ 2 = V / U)
    (hcost : (D * E) ^ (A * ((A + 1) * (B + 1)) / 2) *
        (U * V) ^ (B * ((A + 1) * (B + 1)) / 2) ≤ Real.exp cost) :
    |(∏ i, e i ^ A * u i ^ B) *
        s ^ (((A + 1) * (B + 1) * (A + 2 * B)) / 2)| ≤ Real.exp cost :=
  (abs_rowDenominator_center_le_shearedDyadicCost A B e u s D E U V
    hcard hE hU he hu hs hscale).trans hcost

/-- Directly in the point notation used by the source-normalized determinant
endpoint, local dyadic denominator and centre bounds supply its exponential
cost hypothesis.  This is only the finite algebraic bookkeeping; obtaining
the rowwise bounds from a particular interval remains a source-side task. -/
theorem sourceOriented_denominatorCenter_hcost_of_localDyadicBounds
    {ι : Type*} [Fintype ι]
    (A B : ℕ) (points : ι → GeneralBidegreeFormPoint)
    (r : generalBidegreeFormIndex A B → ι)
    (s D E U V cost : ℝ)
    (hE : 0 ≤ E) (hU : 0 ≤ U)
    (he : ∀ i, |((points (r i)).1.2 : ℝ)| ≤ E)
    (hu : ∀ i, |((points (r i)).2.2 : ℝ)| ≤ U)
    (hs : |s| ≤ D / E)
    (hscale : (D / E) ^ 2 = V / U)
    (hcost : (D * E) ^ (A * ((A + 1) * (B + 1)) / 2) *
        (U * V) ^ (B * ((A + 1) * (B + 1)) / 2) ≤ Real.exp cost) :
    |(∏ i : generalBidegreeFormIndex A B,
        ((points (r i)).1.2 : ℝ) ^ A * ((points (r i)).2.2 : ℝ) ^ B) *
        s ^ (((A + 1) * (B + 1) * (A + 2 * B)) / 2)| ≤ Real.exp cost := by
  apply abs_rowDenominator_center_le_expCost_of_shearedDyadicCost
    A B
    (fun i => ((points (r i)).1.2 : ℝ))
    (fun i => ((points (r i)).2.2 : ℝ))
    s D E U V cost
  · exact card_generalBidegreeFormIndex A B
  · exact hE
  · exact hU
  · exact he
  · exact hu
  · exact hs
  · exact hscale
  · exact hcost

end

end PellPaper
