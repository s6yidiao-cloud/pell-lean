import Pell.SourceNormalizedLeadingCostRate
import Pell.ShearedSurplusStability

/-!
# The finite source mesh correction to the sheared cubic surplus

The rounded source-normalized determinant gain is the continuous sheared
cubic gain minus three completely explicit losses: the third mesh-cell loss
and the low- and high-branch boundary-error sums.  This file records that
identity in the same leading-cost/surplus language as `L:sheared`.

It does not bound the displayed correction, choose the bidegree parameters,
or prove a determinant rate.  Those are the genuinely remaining finite-mesh
and source-parameter tasks.
-/

namespace PellPaper

open scoped BigOperators

noncomputable section

/-- The literal loss between the continuous source-normalized cubic and the
rounded floor-mesh cubic.  It consists of the third mesh-cell loss and the
two finite boundary-error sums, all after the determinant-side `B * L`
rescaling. -/
def sourceNormalizedFloorMeshCorrection (A B : ℕ) (m x L : ℝ) : ℝ :=
  (B : ℝ) * L *
    ((B : ℝ) ^ 2 *
        (3 * ((A : ℝ) / (B : ℝ)) * (x / (B : ℝ))) +
      sourceNormalizedLowMeshBoundaryErrorSum A B m x +
        sourceNormalizedHighMeshBoundaryErrorSum A B
          (sourceNormalizedHighMeshFloorCount A B m x) m x)

/-- The corresponding correction when the two finite boundary sums are
replaced by their checked polynomial envelope. -/
def sourceNormalizedFloorPolynomialMeshCorrection
    (A B : ℕ) (m x L : ℝ) : ℝ :=
  (B : ℝ) * L *
    ((B : ℝ) ^ 2 *
        (3 * ((A : ℝ) / (B : ℝ)) * (x / (B : ℝ))) +
      (x / (B : ℝ)) *
        ((A : ℝ) * ((A : ℝ) * (x / m + 1) + 1) +
          (sourceNormalizedHighMeshFloorCount A B m x : ℝ) *
            (((A : ℝ) + (sourceNormalizedHighMeshFloorCount A B m x : ℝ)) *
              (3 * x / (2 * m) + 1) + 1)))

/-- With positive bidegree scale, the literal correction separates into the
third mesh-cell loss `3 A B x L` and the two already mesh-scaled finite
boundary sums. -/
theorem sourceNormalizedFloorMeshCorrection_eq_threeMeshCellLoss_add_boundarySums
    (A B : ℕ) (m x L : ℝ) (hB : 0 < B) :
    sourceNormalizedFloorMeshCorrection A B m x L =
      3 * (A : ℝ) * (B : ℝ) * x * L +
        (B : ℝ) * L *
          (sourceNormalizedLowMeshBoundaryErrorSum A B m x +
            sourceNormalizedHighMeshBoundaryErrorSum A B
              (sourceNormalizedHighMeshFloorCount A B m x) m x) := by
  have hBreal : 0 < (B : ℝ) := by exact_mod_cast hB
  have hthird : (B : ℝ) ^ 2 *
      (3 * ((A : ℝ) / (B : ℝ)) * (x / (B : ℝ))) =
        3 * (A : ℝ) * x := by
    field_simp [ne_of_gt hBreal]
  unfold sourceNormalizedFloorMeshCorrection
  rw [hthird]
  ring

/-- The polynomial correction has the same explicit third mesh-cell loss;
only the two finite boundary sums have been replaced by their polynomial
envelope. -/
theorem sourceNormalizedFloorPolynomialMeshCorrection_eq_threeMeshCellLoss_add_boundaryBudget
    (A B : ℕ) (m x L : ℝ) (hB : 0 < B) :
    sourceNormalizedFloorPolynomialMeshCorrection A B m x L =
      3 * (A : ℝ) * (B : ℝ) * x * L +
        (B : ℝ) * L * (x / (B : ℝ)) *
          ((A : ℝ) * ((A : ℝ) * (x / m + 1) + 1) +
            (sourceNormalizedHighMeshFloorCount A B m x : ℝ) *
              (((A : ℝ) + (sourceNormalizedHighMeshFloorCount A B m x : ℝ)) *
                (3 * x / (2 * m) + 1) + 1)) := by
  have hBreal : 0 < (B : ℝ) := by exact_mod_cast hB
  have hthird : (B : ℝ) ^ 2 *
      (3 * ((A : ℝ) / (B : ℝ)) * (x / (B : ℝ))) =
        3 * (A : ℝ) * x := by
    field_simp [ne_of_gt hBreal]
  unfold sourceNormalizedFloorPolynomialMeshCorrection
  rw [hthird]
  ring

/-- The exact floor-mesh cubic is the leading centre/denominator cost plus
the continuous sheared surplus, minus precisely the finite mesh correction.
No positivity or asymptotic hypothesis is used in this algebraic identity. -/
theorem sourceNormalizedFloorCubicGain_eq_sourceLeadingCost_add_shearedSurplus_sub_meshCorrection
    (A B : ℕ) (m x L alphaDE alphaUV : ℝ) :
    sourceNormalizedFloorCubicGain A B m x L =
      sourceNormalizedLeadingCost B ((A : ℝ) / (B : ℝ)) alphaDE alphaUV L +
        (B : ℝ) ^ 3 * L *
          shearedSurplus m x alphaDE alphaUV ((A : ℝ) / (B : ℝ)) -
            sourceNormalizedFloorMeshCorrection A B m x L := by
  unfold sourceNormalizedFloorCubicGain sourceNormalizedLeadingCost
    sourceNormalizedFloorMeshCorrection
    sourceNormalizedLowMeshBoundaryErrorSum
    sourceNormalizedHighMeshBoundaryErrorSum sourceNormalizedHighMeshFloorCount
    shearedSurplus
  ring

/-- The polynomial-error floor mesh has the same leading-cost/surplus
identity, with its explicit polynomial correction shown verbatim. -/
theorem sourceNormalizedFloorPolynomialCubicGain_eq_sourceLeadingCost_add_shearedSurplus_sub_meshCorrection
    (A B : ℕ) (m x L alphaDE alphaUV : ℝ) :
    sourceNormalizedFloorPolynomialCubicGain A B m x L =
      sourceNormalizedLeadingCost B ((A : ℝ) / (B : ℝ)) alphaDE alphaUV L +
        (B : ℝ) ^ 3 * L *
          shearedSurplus m x alphaDE alphaUV ((A : ℝ) / (B : ℝ)) -
            sourceNormalizedFloorPolynomialMeshCorrection A B m x L := by
  unfold sourceNormalizedFloorPolynomialCubicGain sourceNormalizedLeadingCost
    sourceNormalizedFloorPolynomialMeshCorrection shearedSurplus
  ring

/-- An exact reformulation of the finite-mesh condition needed to place a
chosen cubic coefficient below the literal floor-mesh gain.  The right side
exhibits the only scalar obligation left after the continuous surplus is
known: its finite correction must fit inside the surplus gap. -/
theorem sourceNormalizedLeadingCost_add_cubicGain_le_floorCubicGain_iff
    (A B : ℕ) (m x L alphaDE alphaUV gainCoeff : ℝ) :
    sourceNormalizedLeadingCost B ((A : ℝ) / (B : ℝ)) alphaDE alphaUV L +
        gainCoeff * (B : ℝ) ^ 3 * L ≤
      sourceNormalizedFloorCubicGain A B m x L ↔
    gainCoeff * (B : ℝ) ^ 3 * L +
        sourceNormalizedFloorMeshCorrection A B m x L ≤
      (B : ℝ) ^ 3 * L *
        shearedSurplus m x alphaDE alphaUV ((A : ℝ) / (B : ℝ)) := by
  rw [sourceNormalizedFloorCubicGain_eq_sourceLeadingCost_add_shearedSurplus_sub_meshCorrection]
  constructor
  · intro h
    have h' := (le_sub_iff_add_le).mp h
    apply (add_le_add_iff_left
      (sourceNormalizedLeadingCost B ((A : ℝ) / (B : ℝ)) alphaDE alphaUV L)).mp
    convert h' using 1
    ring
  · intro h
    apply (le_sub_iff_add_le).mpr
    calc
      sourceNormalizedLeadingCost B ((A : ℝ) / (B : ℝ)) alphaDE alphaUV L +
          gainCoeff * (B : ℝ) ^ 3 * L +
            sourceNormalizedFloorMeshCorrection A B m x L =
        sourceNormalizedLeadingCost B ((A : ℝ) / (B : ℝ)) alphaDE alphaUV L +
          (gainCoeff * (B : ℝ) ^ 3 * L +
            sourceNormalizedFloorMeshCorrection A B m x L) := by ring
      _ ≤ sourceNormalizedLeadingCost B ((A : ℝ) / (B : ℝ)) alphaDE alphaUV L +
          (B : ℝ) ^ 3 * L *
            shearedSurplus m x alphaDE alphaUV ((A : ℝ) / (B : ℝ)) :=
        (add_le_add_iff_left _).mpr h

/-- A convenient coefficient-level sufficient condition for the exact
finite-mesh lower bound.  The caller supplies a coefficient `meshCoeff`
that dominates the displayed finite correction after scaling; the remaining
continuous surplus must exceed `gainCoeff + meshCoeff`. -/
theorem sourceNormalizedLeadingCost_add_cubicGain_le_floorCubicGain_of_meshCorrection_coeff_bound
    (A B : ℕ) (m x L alphaDE alphaUV gainCoeff meshCoeff : ℝ)
    (hB : 0 < B) (hL : 0 < L)
    (hcorrection : sourceNormalizedFloorMeshCorrection A B m x L ≤
      meshCoeff * (B : ℝ) ^ 3 * L)
    (hsurplus : gainCoeff + meshCoeff ≤
      shearedSurplus m x alphaDE alphaUV ((A : ℝ) / (B : ℝ))) :
    sourceNormalizedLeadingCost B ((A : ℝ) / (B : ℝ)) alphaDE alphaUV L +
        gainCoeff * (B : ℝ) ^ 3 * L ≤
      sourceNormalizedFloorCubicGain A B m x L := by
  apply (sourceNormalizedLeadingCost_add_cubicGain_le_floorCubicGain_iff
    A B m x L alphaDE alphaUV gainCoeff).mpr
  have hBreal : 0 < (B : ℝ) := by exact_mod_cast hB
  have hscale : 0 < (B : ℝ) ^ 3 * L :=
    mul_pos (pow_pos hBreal _) hL
  have hcorrection' : sourceNormalizedFloorMeshCorrection A B m x L ≤
      meshCoeff * ((B : ℝ) ^ 3 * L) := by
    convert hcorrection using 1
    ring
  have hsurplusScaled := mul_le_mul_of_nonneg_left hsurplus hscale.le
  calc
    gainCoeff * (B : ℝ) ^ 3 * L +
        sourceNormalizedFloorMeshCorrection A B m x L =
      gainCoeff * ((B : ℝ) ^ 3 * L) +
        sourceNormalizedFloorMeshCorrection A B m x L := by ring
    _ ≤
      gainCoeff * ((B : ℝ) ^ 3 * L) +
        meshCoeff * ((B : ℝ) ^ 3 * L) := by
          exact add_le_add (le_refl _) hcorrection'
    _ = (gainCoeff + meshCoeff) * ((B : ℝ) ^ 3 * L) := by ring
    _ = ((B : ℝ) ^ 3 * L) * (gainCoeff + meshCoeff) := by ring
    _ ≤ ((B : ℝ) ^ 3 * L) *
        shearedSurplus m x alphaDE alphaUV ((A : ℝ) / (B : ℝ)) :=
      hsurplusScaled
    _ = (B : ℝ) ^ 3 * L *
        shearedSurplus m x alphaDE alphaUV ((A : ℝ) / (B : ℝ)) := by ring

/-- The exact finite boundary correction is at most its checked polynomial
envelope.  The third mesh-cell loss is common to both sides; this theorem
only replaces the two explicitly named finite sums. -/
theorem sourceNormalizedFloorMeshCorrection_le_polynomialMeshCorrection
    (A B : ℕ) (m x L : ℝ)
    (hB : 0 < B) (hm : 0 < m) (hmx : m ≤ x) (hL : 0 < L) :
    sourceNormalizedFloorMeshCorrection A B m x L ≤
      sourceNormalizedFloorPolynomialMeshCorrection A B m x L := by
  have hBreal : 0 < (B : ℝ) := by exact_mod_cast hB
  have hx : 0 < x := hm.trans_le hmx
  have hboundary := sourceNormalizedMeshBoundaryErrorSums_le_polynomial
    A B (sourceNormalizedHighMeshFloorCount A B m x) m x hB hm hx
  unfold sourceNormalizedFloorMeshCorrection
    sourceNormalizedFloorPolynomialMeshCorrection
  apply mul_le_mul_of_nonneg_left _ (mul_pos hBreal hL).le
  calc
    (B : ℝ) ^ 2 * (3 * ((A : ℝ) / (B : ℝ)) * (x / (B : ℝ))) +
        sourceNormalizedLowMeshBoundaryErrorSum A B m x +
          sourceNormalizedHighMeshBoundaryErrorSum A B
            (sourceNormalizedHighMeshFloorCount A B m x) m x =
      (B : ℝ) ^ 2 * (3 * ((A : ℝ) / (B : ℝ)) * (x / (B : ℝ))) +
        (sourceNormalizedLowMeshBoundaryErrorSum A B m x +
          sourceNormalizedHighMeshBoundaryErrorSum A B
            (sourceNormalizedHighMeshFloorCount A B m x) m x) := by ring
    _ ≤ (B : ℝ) ^ 2 * (3 * ((A : ℝ) / (B : ℝ)) * (x / (B : ℝ))) +
        (x / (B : ℝ)) *
          ((A : ℝ) * ((A : ℝ) * (x / m + 1) + 1) +
            (sourceNormalizedHighMeshFloorCount A B m x : ℝ) *
              (((A : ℝ) + (sourceNormalizedHighMeshFloorCount A B m x : ℝ)) *
                (3 * x / (2 * m) + 1) + 1)) :=
      add_le_add_right hboundary _

/-- A polynomial-envelope version of the finite-mesh lower bound.  It is
enough to dominate the displayed polynomial correction; the previous theorem
then transfers that bound to the literal floor-mesh gain. -/
theorem sourceNormalizedLeadingCost_add_cubicGain_le_floorCubicGain_of_polynomialMeshCorrection_coeff_bound
    (A B : ℕ) (m x L alphaDE alphaUV gainCoeff meshCoeff : ℝ)
    (hB : 0 < B) (hm : 0 < m) (hmx : m ≤ x) (hL : 0 < L)
    (hcorrection : sourceNormalizedFloorPolynomialMeshCorrection A B m x L ≤
      meshCoeff * (B : ℝ) ^ 3 * L)
    (hsurplus : gainCoeff + meshCoeff ≤
      shearedSurplus m x alphaDE alphaUV ((A : ℝ) / (B : ℝ))) :
    sourceNormalizedLeadingCost B ((A : ℝ) / (B : ℝ)) alphaDE alphaUV L +
        gainCoeff * (B : ℝ) ^ 3 * L ≤
      sourceNormalizedFloorCubicGain A B m x L := by
  apply sourceNormalizedLeadingCost_add_cubicGain_le_floorCubicGain_of_meshCorrection_coeff_bound
    A B m x L alphaDE alphaUV gainCoeff meshCoeff hB hL
  · exact (sourceNormalizedFloorMeshCorrection_le_polynomialMeshCorrection
      A B m x L hB hm hmx hL).trans hcorrection
  · exact hsurplus

/-- The analogous exact condition for the polynomial finite-error endpoint. -/
theorem sourceNormalizedLeadingCost_add_cubicGain_le_floorPolynomialCubicGain_iff
    (A B : ℕ) (m x L alphaDE alphaUV gainCoeff : ℝ) :
    sourceNormalizedLeadingCost B ((A : ℝ) / (B : ℝ)) alphaDE alphaUV L +
        gainCoeff * (B : ℝ) ^ 3 * L ≤
      sourceNormalizedFloorPolynomialCubicGain A B m x L ↔
    gainCoeff * (B : ℝ) ^ 3 * L +
        sourceNormalizedFloorPolynomialMeshCorrection A B m x L ≤
      (B : ℝ) ^ 3 * L *
        shearedSurplus m x alphaDE alphaUV ((A : ℝ) / (B : ℝ)) := by
  rw [sourceNormalizedFloorPolynomialCubicGain_eq_sourceLeadingCost_add_shearedSurplus_sub_meshCorrection]
  constructor
  · intro h
    have h' := (le_sub_iff_add_le).mp h
    apply (add_le_add_iff_left
      (sourceNormalizedLeadingCost B ((A : ℝ) / (B : ℝ)) alphaDE alphaUV L)).mp
    convert h' using 1
    ring
  · intro h
    apply (le_sub_iff_add_le).mpr
    calc
      sourceNormalizedLeadingCost B ((A : ℝ) / (B : ℝ)) alphaDE alphaUV L +
          gainCoeff * (B : ℝ) ^ 3 * L +
            sourceNormalizedFloorPolynomialMeshCorrection A B m x L =
        sourceNormalizedLeadingCost B ((A : ℝ) / (B : ℝ)) alphaDE alphaUV L +
          (gainCoeff * (B : ℝ) ^ 3 * L +
            sourceNormalizedFloorPolynomialMeshCorrection A B m x L) := by ring
      _ ≤ sourceNormalizedLeadingCost B ((A : ℝ) / (B : ℝ)) alphaDE alphaUV L +
          (B : ℝ) ^ 3 * L *
            shearedSurplus m x alphaDE alphaUV ((A : ℝ) / (B : ℝ)) :=
        (add_le_add_iff_left _).mpr h

end

end PellPaper
