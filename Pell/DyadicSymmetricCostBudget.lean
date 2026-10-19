import Pell.DyadicComparableCostAdapter
import Pell.SourceNormalizedLeadingCostRate

/-!
# Logarithmic budget for the symmetric dyadic clearing cost

The comparable-cost determinant endpoint leaves a symmetric product of the
doubled dyadic endpoints as an exponential-cost premise.  This file turns
separate logarithmic endpoint bounds into that premise, keeping the fixed
factor caused by doubling as the literal `log 4` correction.  It does not
derive the source dyadic exponent ranges or their eventual residual budget.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- The logarithmic clearing-cost budget associated to two symmetric endpoint
products.  The coefficients are the exact half-cardinality contributions of
the source and target bidegrees. -/
def dyadicSymmetricBaseLogCost (A B : ℕ) (ellDE ellUV : ℝ) : ℝ :=
  (A * ((A + 1) * (B + 1)) / 2 : ℕ) * ellDE +
    (B * ((A + 1) * (B + 1)) / 2 : ℕ) * ellUV

/-- The literal finite-degree correction between the exact symmetric
clearing-cost coefficients and the cubic source-normalized leading cost. -/
def dyadicSymmetricFiniteDegreeCorrection
    (A B : ℕ) (alphaDE alphaUV L : ℝ) : ℝ :=
  (alphaDE * ((A : ℝ) ^ 2 + (A : ℝ) * (B : ℝ) + (A : ℝ)) +
      alphaUV * ((A : ℝ) * (B : ℝ) + (B : ℝ) ^ 2 + (B : ℝ))) / 2 * L

/-- The fixed logarithmic contribution of doubling each of the two dyadic
endpoint products. -/
def dyadicEndpointDoublingLogCost (A B : ℕ) : ℝ :=
  (A * ((A + 1) * (B + 1)) / 2 : ℕ) * Real.log 4 +
    (B * ((A + 1) * (B + 1)) / 2 : ℕ) * Real.log 4

/-- At the unperturbed source exponents, the exact finite bidegree clearing
cost is the cubic leading cost from `L:sheared` plus a displayed finite-degree
correction.  This is an identity, not an estimate that the correction is
small enough for the determinant budget. -/
theorem dyadicSymmetricBaseLogCost_eq_sourceLeadingCost_add_correction
    (A B : ℕ) (alphaDE alphaUV L : ℝ) (hB : 0 < B) :
    dyadicSymmetricBaseLogCost A B (alphaDE * L) (alphaUV * L) =
      sourceNormalizedLeadingCost B ((A : ℝ) / (B : ℝ)) alphaDE alphaUV L +
        dyadicSymmetricFiniteDegreeCorrection A B alphaDE alphaUV L := by
  have hsourceNat := two_mul_sourceDegree_card_half A B
  have htargetNat := two_mul_targetDegree_card_half A B
  have hsourceReal :
      (2 : ℝ) * (A * ((A + 1) * (B + 1)) / 2 : ℕ) =
        (A : ℝ) * (((A + 1) * (B + 1) : ℕ) : ℝ) := by
    exact_mod_cast hsourceNat
  have htargetReal :
      (2 : ℝ) * (B * ((A + 1) * (B + 1)) / 2 : ℕ) =
        (B : ℝ) * (((A + 1) * (B + 1) : ℕ) : ℝ) := by
    exact_mod_cast htargetNat
  have hBreal : (B : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hB
  have hweighted :
      2 * (L * ((A * ((A + 1) * (B + 1)) / 2 : ℕ) * alphaDE +
        (B * ((A + 1) * (B + 1)) / 2 : ℕ) * alphaUV)) =
        L * (alphaDE * (A : ℝ) + alphaUV * (B : ℝ)) *
          ((A : ℝ) + 1) * ((B : ℝ) + 1) := by
    calc
      2 * (L * ((A * ((A + 1) * (B + 1)) / 2 : ℕ) * alphaDE +
          (B * ((A + 1) * (B + 1)) / 2 : ℕ) * alphaUV)) =
        L * ((2 * (A * ((A + 1) * (B + 1)) / 2 : ℕ)) * alphaDE +
          (2 * (B * ((A + 1) * (B + 1)) / 2 : ℕ)) * alphaUV) := by
            ring
      _ = L * ((A : ℝ) * ((A : ℝ) + 1) * ((B : ℝ) + 1) * alphaDE +
          (B : ℝ) * ((A : ℝ) + 1) * ((B : ℝ) + 1) * alphaUV) := by
            rw [hsourceReal, htargetReal]
            push_cast
            ring
      _ = L * (alphaDE * (A : ℝ) + alphaUV * (B : ℝ)) *
          ((A : ℝ) + 1) * ((B : ℝ) + 1) := by ring
  unfold dyadicSymmetricBaseLogCost dyadicSymmetricFiniteDegreeCorrection
    sourceNormalizedLeadingCost
  push_cast at hsourceReal htargetReal
  field_simp [hBreal]
  convert hweighted using 1 <;> ring

/-- Adding the two literal `log 4` endpoint-doubling losses to the
unperturbed source exponents adds precisely the named fixed cost, while the
remaining main term has the exact leading-cost/correction split above. -/
theorem dyadicSymmetricBaseLogCost_doubled_eq_sourceLeadingCost_add_correction
    (A B : ℕ) (alphaDE alphaUV L : ℝ) (hB : 0 < B) :
    dyadicSymmetricBaseLogCost A B
        (alphaDE * L + Real.log 4) (alphaUV * L + Real.log 4) =
      sourceNormalizedLeadingCost B ((A : ℝ) / (B : ℝ)) alphaDE alphaUV L +
        dyadicSymmetricFiniteDegreeCorrection A B alphaDE alphaUV L +
          dyadicEndpointDoublingLogCost A B := by
  rw [show dyadicSymmetricBaseLogCost A B
      (alphaDE * L + Real.log 4) (alphaUV * L + Real.log 4) =
      dyadicSymmetricBaseLogCost A B (alphaDE * L) (alphaUV * L) +
        dyadicEndpointDoublingLogCost A B by
      unfold dyadicSymmetricBaseLogCost dyadicEndpointDoublingLogCost
      ring]
  rw [dyadicSymmetricBaseLogCost_eq_sourceLeadingCost_add_correction
    A B alphaDE alphaUV L hB]

/-- Two nonnegative endpoint-product bounds imply the corresponding
exponential bound after taking the exact bidegree powers. -/
theorem symmetricProductPowers_le_exp_of_logBounds
    (A B : ℕ) (DE UV ellDE ellUV : ℝ)
    (hDE0 : 0 ≤ DE) (hUV0 : 0 ≤ UV)
    (hDE : DE ≤ Real.exp ellDE) (hUV : UV ≤ Real.exp ellUV) :
    DE ^ (A * ((A + 1) * (B + 1)) / 2) *
        UV ^ (B * ((A + 1) * (B + 1)) / 2) ≤
      Real.exp (dyadicSymmetricBaseLogCost A B ellDE ellUV) := by
  have hDEpow : DE ^ (A * ((A + 1) * (B + 1)) / 2) ≤
      (Real.exp ellDE) ^ (A * ((A + 1) * (B + 1)) / 2) :=
    pow_le_pow_left₀ hDE0 hDE _
  have hUVpow : UV ^ (B * ((A + 1) * (B + 1)) / 2) ≤
      (Real.exp ellUV) ^ (B * ((A + 1) * (B + 1)) / 2) :=
    pow_le_pow_left₀ hUV0 hUV _
  calc
    DE ^ (A * ((A + 1) * (B + 1)) / 2) *
        UV ^ (B * ((A + 1) * (B + 1)) / 2) ≤
      (Real.exp ellDE) ^ (A * ((A + 1) * (B + 1)) / 2) *
        (Real.exp ellUV) ^ (B * ((A + 1) * (B + 1)) / 2) :=
      mul_le_mul hDEpow hUVpow (pow_nonneg hUV0 _)
        (pow_nonneg (Real.exp_pos _).le _)
    _ = Real.exp (dyadicSymmetricBaseLogCost A B ellDE ellUV) := by
      unfold dyadicSymmetricBaseLogCost
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]

/-- Passing from an undoubled positive endpoint product to doubled endpoints
costs exactly `log 4` in its exponential logarithmic budget. -/
theorem doubledEndpointProduct_le_exp_add_log_four
    (D E ell : ℝ) (hDE : D * E ≤ Real.exp ell) :
    (2 * D) * (2 * E) ≤ Real.exp (ell + Real.log 4) := by
  calc
    (2 * D) * (2 * E) = 4 * (D * E) := by ring
    _ ≤ 4 * Real.exp ell :=
      mul_le_mul_of_nonneg_left hDE (by norm_num)
    _ = Real.exp (ell + Real.log 4) := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
      ring

/-- A source-style real-power endpoint bound has the equivalent exponential
logarithmic form needed by the clearing-cost ledger. -/
theorem endpointProduct_le_exp_of_le_rpow
    (Y product exponent : ℝ) (hY : 0 < Y)
    (hproduct : product ≤ Y ^ exponent) :
    product ≤ Real.exp (exponent * Real.log Y) := by
  calc
    product ≤ Y ^ exponent := hproduct
    _ = Real.exp (Real.log Y * exponent) :=
      Real.rpow_def_of_pos hY exponent
    _ = Real.exp (exponent * Real.log Y) := by ring_nf

/-- **Dyadic symmetric clearing-cost bridge.** Separate upper bounds for the
undoubled source and target dyadic products produce the exact `hbaseCost`
shape used by the uniform comparable-cost determinant endpoint.  The two
fixed endpoint doublings appear explicitly as `log 4`; no source exponent
range or leading-cost comparison is inferred. -/
theorem doubledDyadicSymmetricCost_le_exp_of_endpointLogBounds
    (A B : ℕ) (i : ℕ × ℕ × ℕ × ℕ) (ellDE ellUV : ℝ)
    (hDE :
      ((2 ^ i.1 : ℕ) : ℝ) * ((2 ^ i.2.1 : ℕ) : ℝ) ≤ Real.exp ellDE)
    (hUV :
      ((2 ^ i.2.2.1 : ℕ) : ℝ) * ((2 ^ i.2.2.2 : ℕ) : ℝ) ≤ Real.exp ellUV) :
    ((2 * ((2 ^ i.1 : ℕ) : ℝ)) *
        (2 * ((2 ^ i.2.1 : ℕ) : ℝ))) ^
          (A * ((A + 1) * (B + 1)) / 2) *
      ((2 * ((2 ^ i.2.2.1 : ℕ) : ℝ)) *
        (2 * ((2 ^ i.2.2.2 : ℕ) : ℝ))) ^
          (B * ((A + 1) * (B + 1)) / 2) ≤
      Real.exp (dyadicSymmetricBaseLogCost A B
        (ellDE + Real.log 4) (ellUV + Real.log 4)) := by
  apply symmetricProductPowers_le_exp_of_logBounds
    A B
    ((2 * ((2 ^ i.1 : ℕ) : ℝ)) * (2 * ((2 ^ i.2.1 : ℕ) : ℝ)))
    ((2 * ((2 ^ i.2.2.1 : ℕ) : ℝ)) * (2 * ((2 ^ i.2.2.2 : ℕ) : ℝ)))
  · positivity
  · positivity
  · exact doubledEndpointProduct_le_exp_add_log_four
      (((2 ^ i.1 : ℕ) : ℝ)) (((2 ^ i.2.1 : ℕ) : ℝ)) ellDE hDE
  · exact doubledEndpointProduct_le_exp_add_log_four
      (((2 ^ i.2.2.1 : ℕ) : ℝ)) (((2 ^ i.2.2.2 : ℕ) : ℝ)) ellUV hUV

/-- The source-style `Y`-power bounds for the two undoubled dyadic products
give the clearing-cost premise with all endpoint-doubling terms visible.
For the manuscript's perturbed exponent ranges, callers may instantiate
`alphaDE` and `alphaUV` with the corresponding perturbed values. -/
theorem doubledDyadicSymmetricCost_le_exp_of_endpointRpowBounds
    (A B : ℕ) (i : ℕ × ℕ × ℕ × ℕ) (Y alphaDE alphaUV : ℝ)
    (hY : 0 < Y)
    (hDE :
      ((2 ^ i.1 : ℕ) : ℝ) * ((2 ^ i.2.1 : ℕ) : ℝ) ≤ Y ^ alphaDE)
    (hUV :
      ((2 ^ i.2.2.1 : ℕ) : ℝ) * ((2 ^ i.2.2.2 : ℕ) : ℝ) ≤ Y ^ alphaUV) :
    ((2 * ((2 ^ i.1 : ℕ) : ℝ)) *
        (2 * ((2 ^ i.2.1 : ℕ) : ℝ))) ^
          (A * ((A + 1) * (B + 1)) / 2) *
      ((2 * ((2 ^ i.2.2.1 : ℕ) : ℝ)) *
        (2 * ((2 ^ i.2.2.2 : ℕ) : ℝ))) ^
          (B * ((A + 1) * (B + 1)) / 2) ≤
      Real.exp (dyadicSymmetricBaseLogCost A B
        (alphaDE * Real.log Y + Real.log 4)
        (alphaUV * Real.log Y + Real.log 4)) := by
  apply doubledDyadicSymmetricCost_le_exp_of_endpointLogBounds
  · exact endpointProduct_le_exp_of_le_rpow Y
      (((2 ^ i.1 : ℕ) : ℝ) * ((2 ^ i.2.1 : ℕ) : ℝ)) alphaDE hY hDE
  · exact endpointProduct_le_exp_of_le_rpow Y
      (((2 ^ i.2.2.1 : ℕ) : ℝ) * ((2 ^ i.2.2.2 : ℕ) : ℝ)) alphaUV hY hUV

end

end PellPaper
