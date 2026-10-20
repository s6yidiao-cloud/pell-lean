import Pell.ShearedLocalCoordinateCost

/-!
# Comparable local denominator and centre cost for the sheared determinant

The exact dyadic identity in `ShearedLocalCoordinateCost` assumes
`(D / E)^2 = V / U`.  A local box can instead supply the one-sided
comparison `(D / E)^2 ≤ k * (V / U)` and a centre bound enlarged by a factor
`c`.  This file records the resulting finite algebraic loss explicitly:
`c` occurs to the centre exponent and `k` to the target half-cardinality.

No source interval estimate, logarithmic bound, or determinant-rate
absorption is asserted here.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- A one-sided replacement for `dyadic_center_denominator_scale_identity`.
The factors `c` and `k` remain visible: respectively they cost the full
centre exponent and the target half-cardinality.  Positivity of `E` and `U`
makes the two dyadic ratios meaningful, while the other sign hypotheses make
the displayed product a genuine nonnegative cost. -/
theorem dyadic_center_denominator_scale_le_of_comparableScale
    (D E U V c k : ℝ) (a b : ℕ)
    (hD : 0 ≤ D) (hE : 0 < E) (hU : 0 < U) (hV : 0 ≤ V)
    (hc : 0 ≤ c) (hk : 0 ≤ k)
    (hscale : (D / E) ^ 2 ≤ k * (V / U)) :
    (E ^ (2 * a) * U ^ (2 * b)) * (c * (D / E)) ^ (a + 2 * b) ≤
      c ^ (a + 2 * b) * k ^ b * (D * E) ^ a * (U * V) ^ b := by
  have hratio : 0 ≤ D / E := div_nonneg hD hE.le
  have hbase : 0 ≤ E ^ (2 * a) * U ^ (2 * b) * (D / E) ^ a := by
    positivity
  have hright : 0 ≤ (k * (V / U)) ^ b := by
    exact pow_nonneg (mul_nonneg hk (div_nonneg hV hU.le)) _
  have hscalePow : (D / E) ^ (2 * b) ≤ (k * (V / U)) ^ b := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (sq_nonneg (D / E)) hscale b
  have hsource : E ^ (2 * a) * (D / E) ^ a = (D * E) ^ a := by
    rw [show 2 * a = a + a by omega, pow_add, div_pow]
    field_simp
    ring
  have htarget : U ^ (2 * b) * (V / U) ^ b = (U * V) ^ b := by
    rw [show 2 * b = b + b by omega, pow_add, div_pow]
    field_simp
    ring
  calc
    (E ^ (2 * a) * U ^ (2 * b)) * (c * (D / E)) ^ (a + 2 * b) =
        c ^ (a + 2 * b) *
          ((D / E) ^ (2 * b) *
            (E ^ (2 * a) * U ^ (2 * b) * (D / E) ^ a)) := by
          rw [mul_pow, pow_add]
          ring
    _ ≤ c ^ (a + 2 * b) *
          ((k * (V / U)) ^ b *
            (E ^ (2 * a) * U ^ (2 * b) * (D / E) ^ a)) := by
          apply mul_le_mul_of_nonneg_left
          · exact mul_le_mul hscalePow le_rfl hbase hright
          · exact pow_nonneg hc _
    _ = c ^ (a + 2 * b) * k ^ b * (D * E) ^ a * (U * V) ^ b := by
          rw [mul_pow]
          calc
            c ^ (a + 2 * b) *
                (k ^ b * (V / U) ^ b *
                  (E ^ (2 * a) * U ^ (2 * b) * (D / E) ^ a)) =
                c ^ (a + 2 * b) * k ^ b *
                  (E ^ (2 * a) * (D / E) ^ a) *
                  (U ^ (2 * b) * (V / U) ^ b) := by ring
            _ = c ^ (a + 2 * b) * k ^ b * (D * E) ^ a * (U * V) ^ b := by
              rw [hsource, htarget]

/-- The preceding one-sided dyadic comparison at the bidegrees used by the
sheared determinant.  With `H = (A + 1) * (B + 1)`, the losses are exactly
`c^(H*(A+2B)/2)` and `k^(B*H/2)`. -/
theorem sheared_dyadic_center_denominator_scale_le_of_comparableScale
    (A B : ℕ) (D E U V c k : ℝ)
    (hD : 0 ≤ D) (hE : 0 < E) (hU : 0 < U) (hV : 0 ≤ V)
    (hc : 0 ≤ c) (hk : 0 ≤ k)
    (hscale : (D / E) ^ 2 ≤ k * (V / U)) :
    (E ^ A * U ^ B) ^ ((A + 1) * (B + 1)) *
        (c * (D / E)) ^ (((A + 1) * (B + 1) * (A + 2 * B)) / 2) ≤
      c ^ (((A + 1) * (B + 1) * (A + 2 * B)) / 2) *
        k ^ (B * ((A + 1) * (B + 1)) / 2) *
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
  have hcentrePow :
      (c * (D / E)) ^ (((A + 1) * (B + 1) * (A + 2 * B)) / 2) =
        (c * (D / E)) ^ (A * ((A + 1) * (B + 1)) / 2 +
          2 * (B * ((A + 1) * (B + 1)) / 2)) :=
    congrArg (fun n : ℕ => (c * (D / E)) ^ n) hcentre
  calc
    (E ^ A * U ^ B) ^ ((A + 1) * (B + 1)) *
        (c * (D / E)) ^ (((A + 1) * (B + 1) * (A + 2 * B)) / 2) =
        (E ^ (A * ((A + 1) * (B + 1))) *
          U ^ (B * ((A + 1) * (B + 1)))) *
          (c * (D / E)) ^ (((A + 1) * (B + 1) * (A + 2 * B)) / 2) := by
            rw [mul_pow, ← pow_mul, ← pow_mul]
    _ = (E ^ (2 * (A * ((A + 1) * (B + 1)) / 2)) *
          U ^ (2 * (B * ((A + 1) * (B + 1)) / 2))) *
          (c * (D / E)) ^ (A * ((A + 1) * (B + 1)) / 2 +
            2 * (B * ((A + 1) * (B + 1)) / 2)) := by
              rw [hEpow, hUpow, hcentrePow]
    _ ≤ c ^ (((A + 1) * (B + 1) * (A + 2 * B)) / 2) *
          k ^ (B * ((A + 1) * (B + 1)) / 2) *
            (D * E) ^ (A * ((A + 1) * (B + 1)) / 2) *
            (U * V) ^ (B * ((A + 1) * (B + 1)) / 2) := by
      rw [hcentre]
      exact dyadic_center_denominator_scale_le_of_comparableScale D E U V c k
        (A * ((A + 1) * (B + 1)) / 2)
        (B * ((A + 1) * (B + 1)) / 2)
        hD hE hU hV hc hk hscale

/-- Rowwise denominator bounds, a centre bound with factor `c`, and a
one-sided dyadic scale comparison give the symmetric sheared cost with the
explicit `c`- and `k`-losses. -/
theorem abs_rowDenominator_center_le_shearedDyadicCost_of_comparableScale
    {ι : Type*} [Fintype ι]
    (A B : ℕ) (e u : ι → ℝ) (s D E U V c k : ℝ)
    (hcard : Fintype.card ι = (A + 1) * (B + 1))
    (hD : 0 ≤ D) (hE : 0 < E) (hU : 0 < U) (hV : 0 ≤ V)
    (hc : 0 ≤ c) (hk : 0 ≤ k)
    (he : ∀ i, |e i| ≤ E) (hu : ∀ i, |u i| ≤ U)
    (hs : |s| ≤ c * (D / E))
    (hscale : (D / E) ^ 2 ≤ k * (V / U)) :
    |(∏ i, e i ^ A * u i ^ B) *
        s ^ (((A + 1) * (B + 1) * (A + 2 * B)) / 2)| ≤
      c ^ (((A + 1) * (B + 1) * (A + 2 * B)) / 2) *
        k ^ (B * ((A + 1) * (B + 1)) / 2) *
          (D * E) ^ (A * ((A + 1) * (B + 1)) / 2) *
          (U * V) ^ (B * ((A + 1) * (B + 1)) / 2) := by
  calc
    |(∏ i, e i ^ A * u i ^ B) *
        s ^ (((A + 1) * (B + 1) * (A + 2 * B)) / 2)| ≤
        (E ^ A * U ^ B) ^ Fintype.card ι *
          (c * (D / E)) ^ (((A + 1) * (B + 1) * (A + 2 * B)) / 2) :=
      abs_rowDenominator_center_le_of_abs_le A B
        (((A + 1) * (B + 1) * (A + 2 * B)) / 2)
        e u s E U (c * (D / E)) hE.le hU.le he hu hs
    _ = (E ^ A * U ^ B) ^ ((A + 1) * (B + 1)) *
          (c * (D / E)) ^ (((A + 1) * (B + 1) * (A + 2 * B)) / 2) := by
            rw [hcard]
    _ ≤ c ^ (((A + 1) * (B + 1) * (A + 2 * B)) / 2) *
          k ^ (B * ((A + 1) * (B + 1)) / 2) *
            (D * E) ^ (A * ((A + 1) * (B + 1)) / 2) *
            (U * V) ^ (B * ((A + 1) * (B + 1)) / 2) :=
      sheared_dyadic_center_denominator_scale_le_of_comparableScale
        A B D E U V c k hD hE hU hV hc hk hscale

/-- An explicit exponential majorant for the comparable symmetric cost
supplies the cleared-determinant cost hypothesis.  The finite powers of `c`
and `k` are intentionally not hidden in `cost`. -/
theorem abs_rowDenominator_center_le_expCost_of_comparableScale
    {ι : Type*} [Fintype ι]
    (A B : ℕ) (e u : ι → ℝ) (s D E U V c k cost : ℝ)
    (hcard : Fintype.card ι = (A + 1) * (B + 1))
    (hD : 0 ≤ D) (hE : 0 < E) (hU : 0 < U) (hV : 0 ≤ V)
    (hc : 0 ≤ c) (hk : 0 ≤ k)
    (he : ∀ i, |e i| ≤ E) (hu : ∀ i, |u i| ≤ U)
    (hs : |s| ≤ c * (D / E))
    (hscale : (D / E) ^ 2 ≤ k * (V / U))
    (hcost : c ^ (((A + 1) * (B + 1) * (A + 2 * B)) / 2) *
        k ^ (B * ((A + 1) * (B + 1)) / 2) *
          (D * E) ^ (A * ((A + 1) * (B + 1)) / 2) *
          (U * V) ^ (B * ((A + 1) * (B + 1)) / 2) ≤ Real.exp cost) :
    |(∏ i, e i ^ A * u i ^ B) *
        s ^ (((A + 1) * (B + 1) * (A + 2 * B)) / 2)| ≤ Real.exp cost :=
  (abs_rowDenominator_center_le_shearedDyadicCost_of_comparableScale
    A B e u s D E U V c k hcard hD hE hU hV hc hk he hu hs hscale).trans hcost

/-- Point-notation form of the comparable local cost bridge for the
source-normalized determinant endpoint.  It supplies only its finite cost
hypothesis; deriving the displayed local inequalities remains source-side. -/
theorem sourceOriented_denominatorCenter_hcost_of_localDyadicComparableBounds
    {ι : Type*} [Fintype ι]
    (A B : ℕ) (points : ι → GeneralBidegreeFormPoint)
    (r : generalBidegreeFormIndex A B → ι)
    (s D E U V c k cost : ℝ)
    (hD : 0 ≤ D) (hE : 0 < E) (hU : 0 < U) (hV : 0 ≤ V)
    (hc : 0 ≤ c) (hk : 0 ≤ k)
    (he : ∀ i, |((points (r i)).1.2 : ℝ)| ≤ E)
    (hu : ∀ i, |((points (r i)).2.2 : ℝ)| ≤ U)
    (hs : |s| ≤ c * (D / E))
    (hscale : (D / E) ^ 2 ≤ k * (V / U))
    (hcost : c ^ (((A + 1) * (B + 1) * (A + 2 * B)) / 2) *
        k ^ (B * ((A + 1) * (B + 1)) / 2) *
          (D * E) ^ (A * ((A + 1) * (B + 1)) / 2) *
          (U * V) ^ (B * ((A + 1) * (B + 1)) / 2) ≤ Real.exp cost) :
    |(∏ i : generalBidegreeFormIndex A B,
        ((points (r i)).1.2 : ℝ) ^ A * ((points (r i)).2.2 : ℝ) ^ B) *
        s ^ (((A + 1) * (B + 1) * (A + 2 * B)) / 2)| ≤ Real.exp cost := by
  apply abs_rowDenominator_center_le_expCost_of_comparableScale
    A B
    (fun i => ((points (r i)).1.2 : ℝ))
    (fun i => ((points (r i)).2.2 : ℝ))
    s D E U V c k cost
  · exact card_generalBidegreeFormIndex A B
  · exact hD
  · exact hE
  · exact hU
  · exact hV
  · exact hc
  · exact hk
  · exact he
  · exact hu
  · exact hs
  · exact hscale
  · exact hcost

end

end PellPaper
